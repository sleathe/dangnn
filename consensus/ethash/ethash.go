// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

// Package ethash implements the ethash proof-of-work consensus engine.
package ethash

import (
	"errors"
	"fmt"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/ethdb"
	"math"
	"math/big"
	"math/rand"
	"os"
	"path/filepath"
	"reflect"
	"runtime"
	"sort"
	"strconv"
	"sync"
	"sync/atomic"
	"time"
	"unsafe"

	mmap "github.com/edsrzf/mmap-go"
	"github.com/ethereum/go-ethereum/accounts"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/metrics"
	"github.com/ethereum/go-ethereum/rpc"
	"github.com/hashicorp/golang-lru/simplelru"
)

var ErrInvalidDumpMagic = errors.New("invalid dump magic")

var (
	// two256 is a big integer representing 2^256
	two256 = new(big.Int).Exp(big.NewInt(2), big.NewInt(256), big.NewInt(0))

	// sharedEthash is a full instance that can be shared between multiple users.
	sharedEthash = New(Config{"", 3, 0, "", 1, 0, ModeNormal, nil, 30000}, nil, false, nil)

	// algorithmRevision is the data structure version used for file naming.
	algorithmRevision = 23

	// dumpMagic is a dataset dump header to sanity check a data dump.
	dumpMagic = []uint32{0xbaddcafe, 0xfee1dead}

	EthashEpoch = uint64(votesEpochLength)
)

// isLittleEndian returns whether the local system is running in little or big
// endian byte order.
func isLittleEndian() bool {
	n := uint32(0x01020304)
	return *(*byte)(unsafe.Pointer(&n)) == 0x04
}

// memoryMap tries to memory map a file of uint32s for read only access.
func memoryMap(path string) (*os.File, mmap.MMap, []uint32, error) {
	file, err := os.OpenFile(path, os.O_RDONLY, 0644)
	if err != nil {
		return nil, nil, nil, err
	}
	mem, buffer, err := memoryMapFile(file, false)
	if err != nil {
		file.Close()
		return nil, nil, nil, err
	}
	for i, magic := range dumpMagic {
		if buffer[i] != magic {
			mem.Unmap()
			file.Close()
			return nil, nil, nil, ErrInvalidDumpMagic
		}
	}
	return file, mem, buffer[len(dumpMagic):], err
}

// memoryMapFile tries to memory map an already opened file descriptor.
func memoryMapFile(file *os.File, write bool) (mmap.MMap, []uint32, error) {
	// Try to memory map the file
	flag := mmap.RDONLY
	if write {
		flag = mmap.RDWR
	}
	mem, err := mmap.Map(file, flag, 0)
	if err != nil {
		return nil, nil, err
	}
	// Yay, we managed to memory map the file, here be dragons
	header := *(*reflect.SliceHeader)(unsafe.Pointer(&mem))
	header.Len /= 4
	header.Cap /= 4

	return mem, *(*[]uint32)(unsafe.Pointer(&header)), nil
}

// memoryMapAndGenerate tries to memory map a temporary file of uint32s for write
// access, fill it with the data from a generator and then move it into the final
// path requested.
func memoryMapAndGenerate(path string, size uint64, generator func(buffer []uint32)) (*os.File, mmap.MMap, []uint32, error) {
	// Ensure the data folder exists
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return nil, nil, nil, err
	}
	// Create a huge temporary empty file to fill with data
	temp := path + "." + strconv.Itoa(rand.Int())

	dump, err := os.Create(temp)
	if err != nil {
		return nil, nil, nil, err
	}
	if err = dump.Truncate(int64(len(dumpMagic))*4 + int64(size)); err != nil {
		return nil, nil, nil, err
	}
	// Memory map the file for writing and fill it with the generator
	mem, buffer, err := memoryMapFile(dump, true)
	if err != nil {
		dump.Close()
		return nil, nil, nil, err
	}
	copy(buffer, dumpMagic)

	data := buffer[len(dumpMagic):]
	generator(data)

	if err := mem.Unmap(); err != nil {
		return nil, nil, nil, err
	}
	if err := dump.Close(); err != nil {
		return nil, nil, nil, err
	}
	if err := os.Rename(temp, path); err != nil {
		return nil, nil, nil, err
	}
	return memoryMap(path)
}

// lru tracks caches or datasets by their last use time, keeping at most N of them.
type lru struct {
	what string
	new  func(epoch uint64) interface{}
	mu   sync.Mutex
	// Items are kept in a LRU cache, but there is a special case:
	// We always keep an item for (highest seen epoch) + 1 as the 'future item'.
	cache      *simplelru.LRU
	future     uint64
	futureItem interface{}
}

// newlru create a new least-recently-used cache for either the verification caches
// or the mining datasets.
func newlru(what string, maxItems int, new func(epoch uint64) interface{}) *lru {
	if maxItems <= 0 {
		maxItems = 1
	}
	cache, _ := simplelru.NewLRU(maxItems, func(key, value interface{}) {
		log.Trace("Evicted ethash "+what, "epoch", key)
	})
	return &lru{what: what, new: new, cache: cache}
}

// get retrieves or creates an item for the given epoch. The first return value is always
// non-nil. The second return value is non-nil if lru thinks that an item will be useful in
// the near future.
func (lru *lru) get(epoch uint64) (item, future interface{}) {
	lru.mu.Lock()
	defer lru.mu.Unlock()

	// Get or create the item for the requested epoch.
	item, ok := lru.cache.Get(epoch)
	if !ok {
		if lru.future > 0 && lru.future == epoch {
			item = lru.futureItem
		} else {
			log.Trace("Requiring new ethash "+lru.what, "epoch", epoch)
			item = lru.new(epoch)
		}
		lru.cache.Add(epoch, item)
	}
	// Update the 'future item' if epoch is larger than previously seen.
	if epoch < maxEpoch-1 && lru.future < epoch+1 {
		log.Trace("Requiring new future ethash "+lru.what, "epoch", epoch+1)
		future = lru.new(epoch + 1)
		lru.future = epoch + 1
		lru.futureItem = future
	}
	return item, future
}

// cache wraps an ethash cache with some metadata to allow easier concurrent use.
type cache struct {
	epoch uint64    // Epoch for which this cache is relevant
	dump  *os.File  // File descriptor of the memory mapped cache
	mmap  mmap.MMap // Memory map itself to unmap before releasing
	cache []uint32  // The actual cache data content (may be memory mapped)
	once  sync.Once // Ensures the cache is generated only once
}

// newCache creates a new ethash verification cache and returns it as a plain Go
// interface to be usable in an LRU cache.
func newCache(epoch uint64) interface{} {
	return &cache{epoch: epoch}
}

// generate ensures that the cache content is generated before use.
func (c *cache) generate(dir string, limit int, test bool) {
	c.once.Do(func() {
		size := cacheSize(c.epoch*epochLength + 1)
		seed := seedHash(c.epoch*epochLength + 1)
		if test {
			size = 1024
		}
		// If we don't store anything on disk, generate and return.
		if dir == "" {
			c.cache = make([]uint32, size/4)
			generateCache(c.cache, c.epoch, seed)
			return
		}
		// Disk storage is needed, this will get fancy
		var endian string
		if !isLittleEndian() {
			endian = ".be"
		}
		path := filepath.Join(dir, fmt.Sprintf("cache-R%d-%x%s", algorithmRevision, seed[:8], endian))
		logger := log.New("epoch", c.epoch)

		// We're about to mmap the file, ensure that the mapping is cleaned up when the
		// cache becomes unused.
		runtime.SetFinalizer(c, (*cache).finalizer)

		// Try to load the file from disk and memory map it
		var err error
		c.dump, c.mmap, c.cache, err = memoryMap(path)
		if err == nil {
			logger.Debug("Loaded old ethash cache from disk")
			return
		}
		logger.Debug("Failed to load old ethash cache", "err", err)

		// No previous cache available, create a new cache file to fill
		c.dump, c.mmap, c.cache, err = memoryMapAndGenerate(path, size, func(buffer []uint32) { generateCache(buffer, c.epoch, seed) })
		if err != nil {
			logger.Error("Failed to generate mapped ethash cache", "err", err)

			c.cache = make([]uint32, size/4)
			generateCache(c.cache, c.epoch, seed)
		}
		// Iterate over all previous instances and delete old ones
		for ep := int(c.epoch) - limit; ep >= 0; ep-- {
			seed := seedHash(uint64(ep)*epochLength + 1)
			path := filepath.Join(dir, fmt.Sprintf("cache-R%d-%x%s", algorithmRevision, seed[:8], endian))
			os.Remove(path)
		}
	})
}

// finalizer unmaps the memory and closes the file.
func (c *cache) finalizer() {
	if c.mmap != nil {
		c.mmap.Unmap()
		c.dump.Close()
		c.mmap, c.dump = nil, nil
	}
}

// dataset wraps an ethash dataset with some metadata to allow easier concurrent use.
type dataset struct {
	epoch   uint64    // Epoch for which this cache is relevant
	dump    *os.File  // File descriptor of the memory mapped cache
	mmap    mmap.MMap // Memory map itself to unmap before releasing
	dataset []uint32  // The actual cache data content
	once    sync.Once // Ensures the cache is generated only once
	done    uint32    // Atomic flag to determine generation status
}

// newDataset creates a new ethash mining dataset and returns it as a plain Go
// interface to be usable in an LRU cache.
func newDataset(epoch uint64) interface{} {
	return &dataset{epoch: epoch}
}

// generate ensures that the dataset content is generated before use.
func (d *dataset) generate(dir string, limit int, test bool) {
	d.once.Do(func() {
		// Mark the dataset generated after we're done. This is needed for remote
		defer atomic.StoreUint32(&d.done, 1)

		csize := cacheSize(d.epoch*epochLength + 1)
		dsize := datasetSize(d.epoch*epochLength + 1)
		seed := seedHash(d.epoch*epochLength + 1)
		if test {
			csize = 1024
			dsize = 32 * 1024
		}
		// If we don't store anything on disk, generate and return
		if dir == "" {
			cache := make([]uint32, csize/4)
			generateCache(cache, d.epoch, seed)

			d.dataset = make([]uint32, dsize/4)
			generateDataset(d.dataset, d.epoch, cache)

			return
		}
		// Disk storage is needed, this will get fancy
		var endian string
		if !isLittleEndian() {
			endian = ".be"
		}
		path := filepath.Join(dir, fmt.Sprintf("full-R%d-%x%s", algorithmRevision, seed[:8], endian))
		logger := log.New("epoch", d.epoch)

		// We're about to mmap the file, ensure that the mapping is cleaned up when the
		// cache becomes unused.
		runtime.SetFinalizer(d, (*dataset).finalizer)

		// Try to load the file from disk and memory map it
		var err error
		d.dump, d.mmap, d.dataset, err = memoryMap(path)
		if err == nil {
			logger.Debug("Loaded old ethash dataset from disk")
			return
		}
		logger.Debug("Failed to load old ethash dataset", "err", err)

		// No previous dataset available, create a new dataset file to fill
		cache := make([]uint32, csize/4)
		generateCache(cache, d.epoch, seed)

		d.dump, d.mmap, d.dataset, err = memoryMapAndGenerate(path, dsize, func(buffer []uint32) { generateDataset(buffer, d.epoch, cache) })
		if err != nil {
			logger.Error("Failed to generate mapped ethash dataset", "err", err)

			d.dataset = make([]uint32, dsize/2)
			generateDataset(d.dataset, d.epoch, cache)
		}
		// Iterate over all previous instances and delete old ones
		for ep := int(d.epoch) - limit; ep >= 0; ep-- {
			seed := seedHash(uint64(ep)*epochLength + 1)
			path := filepath.Join(dir, fmt.Sprintf("full-R%d-%x%s", algorithmRevision, seed[:8], endian))
			os.Remove(path)
		}
	})
}

// generated returns whether this particular dataset finished generating already
// or not (it may not have been started at all). This is useful for remote miners
// to default to verification caches instead of blocking on DAG generations.
func (d *dataset) generated() bool {
	return atomic.LoadUint32(&d.done) == 1
}

// finalizer closes any file handlers and memory maps open.
func (d *dataset) finalizer() {
	if d.mmap != nil {
		d.mmap.Unmap()
		d.dump.Close()
		d.mmap, d.dump = nil, nil
	}
}

// MakeCache generates a new ethash cache and optionally stores it to disk.
func MakeCache(block uint64, dir string) {
	c := cache{epoch: block / epochLength}
	c.generate(dir, math.MaxInt32, false)
}

// MakeDataset generates a new ethash dataset and optionally stores it to disk.
func MakeDataset(block uint64, dir string) {
	d := dataset{epoch: block / epochLength}
	d.generate(dir, math.MaxInt32, false)
}

// Mode defines the type and amount of PoW verification an ethash engine makes.
type Mode uint

const (
	ModeNormal Mode = iota
	ModeShared
	ModeTest
	ModeFake
	ModeFullFake
)

// SignerFn is a signer callback function to request a header to be signed by a
// backing account.
type SignerBlockFn func(account accounts.Account, block *types.Block, chainID *big.Int) (*types.Block, error)

// Config are the configuration parameters of the ethash.
type Config struct {
	CacheDir       string
	CachesInMem    int
	CachesOnDisk   int
	DatasetDir     string
	DatasetsInMem  int
	DatasetsOnDisk int
	PowMode        Mode

	Log log.Logger `toml:"-"`
	Epoch  		   uint64   // Epoch length to reset votes and checkpoint
}

// Ethash is a consensus engine based on proof-of-work implementing the ethash
// algorithm.
type Ethash struct {
	config Config

	caches   *lru // In memory caches to avoid regenerating too often
	datasets *lru // In memory datasets to avoid regenerating too often

	// Mining related fields
	rand     *rand.Rand    // Properly seeded random source for nonces
	threads  int           // Number of threads to mine on if mining
	update   chan struct{} // Notification channel to update mining parameters
	hashrate metrics.Meter // Meter tracking the average hashrate
	remote   *remoteSealer

	// The fields below are hooks for testing
	shared    *Ethash       // Shared PoW verifier to avoid cache regeneration
	fakeFail  uint64        // Block number which fails PoW check even in fake mode
	fakeDelay time.Duration // Time delay to sleep for before returning from verify

	db     ethdb.Database       // Database to store and retrieve snapshot checkpoints

	recents    		*simplelru.LRU // Snapshots for recent block to speed up reorgs
	proposals 		[]*Vote // Current list of proposals we are pushing

	signer common.Address 		// Ethereum address of the signing key
	signFn SignerBlockFn  		// Signer function to authorize hashes with
	lockSigner   sync.RWMutex   // Protects the signer fields

	lock      sync.Mutex // Ensures thread safety for the in-memory caches and mining fields
	closeOnce sync.Once  // Ensures exit channel will not be closed twice.
}

// New creates a full sized ethash PoW scheme and starts a background thread for
// remote mining, also optionally notifying a batch of remote services of new work
// packages.
func New(config Config, notify []string, noverify bool, db ethdb.Database) *Ethash {
	if config.Log == nil {
		config.Log = log.Root()
	}
	if config.CachesInMem <= 0 {
		config.Log.Warn("One ethash cache must always be in memory", "requested", config.CachesInMem)
		config.CachesInMem = 1
	}
	if config.CacheDir != "" && config.CachesOnDisk > 0 {
		config.Log.Info("Disk storage enabled for ethash caches", "dir", config.CacheDir, "count", config.CachesOnDisk)
	}
	if config.DatasetDir != "" && config.DatasetsOnDisk > 0 {
		config.Log.Info("Disk storage enabled for ethash DAGs", "dir", config.DatasetDir, "count", config.DatasetsOnDisk)
	}

	cache, _ := simplelru.NewLRU(int(config.Epoch), func(key, value interface{}) {
		log.Trace("Evicted ethash recents election key:",key)
	})

	ethash := &Ethash{
		config:   config,
		caches:   newlru("cache", config.CachesInMem, newCache),
		datasets: newlru("dataset", config.DatasetsInMem, newDataset),
		update:   make(chan struct{}),
		hashrate: metrics.NewMeterForced(),
		db:		db,
		recents: cache,
		//recents: newlru("elect",int(config.Epoch), newElectionSet),
		proposals:  make([]*Vote, 0, 3),
	}
	ethash.remote = startRemoteSealer(ethash, notify, noverify)
	return ethash
}

// NewTester creates a small sized ethash PoW scheme useful only for testing
// purposes.
func NewTester(notify []string, noverify bool) *Ethash {
	ethash := &Ethash{
		config:   Config{PowMode: ModeTest, Log: log.Root()},
		caches:   newlru("cache", 1, newCache),
		datasets: newlru("dataset", 1, newDataset),
		update:   make(chan struct{}),
		hashrate: metrics.NewMeterForced(),
		db:		rawdb.NewMemoryDatabase(),
		proposals:  make([]*Vote, 0, 3),
	}
	ethash.remote = startRemoteSealer(ethash, notify, noverify)
	return ethash
}

// NewFaker creates a ethash consensus engine with a fake PoW scheme that accepts
// all blocks' seal as valid, though they still have to conform to the Ethereum
// consensus rules.
func NewFaker() *Ethash {
	return &Ethash{
		config: Config{
			PowMode: ModeFake,
			Log:     log.Root(),
		},
	}
}

// NewFakeFailer creates a ethash consensus engine with a fake PoW scheme that
// accepts all blocks as valid apart from the single one specified, though they
// still have to conform to the Ethereum consensus rules.
func NewFakeFailer(fail uint64) *Ethash {
	return &Ethash{
		config: Config{
			PowMode: ModeFake,
			Log:     log.Root(),
		},
		fakeFail: fail,
	}
}

// NewFakeDelayer creates a ethash consensus engine with a fake PoW scheme that
// accepts all blocks as valid, but delays verifications by some time, though
// they still have to conform to the Ethereum consensus rules.
func NewFakeDelayer(delay time.Duration) *Ethash {
	return &Ethash{
		config: Config{
			PowMode: ModeFake,
			Log:     log.Root(),
		},
		fakeDelay: delay,
	}
}

// NewFullFaker creates an ethash consensus engine with a full fake scheme that
// accepts all blocks as valid, without checking any consensus rules whatsoever.
func NewFullFaker() *Ethash {
	return &Ethash{
		config: Config{
			PowMode: ModeFullFake,
			Log:     log.Root(),
		},
	}
}

// NewShared creates a full sized ethash PoW shared between all requesters running
// in the same process.
func NewShared() *Ethash {
	return &Ethash{shared: sharedEthash}
}

// Close closes the exit channel to notify all backend threads exiting.
func (ethash *Ethash) Close() error {
	var err error
	ethash.closeOnce.Do(func() {
		// Short circuit if the exit channel is not allocated.
		if ethash.remote == nil {
			return
		}
		close(ethash.remote.requestExit)
		<-ethash.remote.exitCh
	})
	return err
}

// cache tries to retrieve a verification cache for the specified block number
// by first checking against a list of in-memory caches, then against caches
// stored on disk, and finally generating one if none can be found.
func (ethash *Ethash) cache(block uint64) *cache {
	epoch := block / epochLength
	currentI, futureI := ethash.caches.get(epoch)
	current := currentI.(*cache)

	// Wait for generation finish.
	current.generate(ethash.config.CacheDir, ethash.config.CachesOnDisk, ethash.config.PowMode == ModeTest)

	// If we need a new future cache, now's a good time to regenerate it.
	if futureI != nil {
		future := futureI.(*cache)
		go future.generate(ethash.config.CacheDir, ethash.config.CachesOnDisk, ethash.config.PowMode == ModeTest)
	}
	return current
}

// dataset tries to retrieve a mining dataset for the specified block number
// by first checking against a list of in-memory datasets, then against DAGs
// stored on disk, and finally generating one if none can be found.
//
// If async is specified, not only the future but the current DAG is also
// generates on a background thread.
func (ethash *Ethash) dataset(block uint64, async bool) *dataset {
	// Retrieve the requested ethash dataset
	epoch := block / epochLength
	currentI, futureI := ethash.datasets.get(epoch)
	current := currentI.(*dataset)

	// If async is specified, generate everything in a background thread
	if async && !current.generated() {
		go func() {
			current.generate(ethash.config.DatasetDir, ethash.config.DatasetsOnDisk, ethash.config.PowMode == ModeTest)

			if futureI != nil {
				future := futureI.(*dataset)
				future.generate(ethash.config.DatasetDir, ethash.config.DatasetsOnDisk, ethash.config.PowMode == ModeTest)
			}
		}()
	} else {
		// Either blocking generation was requested, or already done
		current.generate(ethash.config.DatasetDir, ethash.config.DatasetsOnDisk, ethash.config.PowMode == ModeTest)

		if futureI != nil {
			future := futureI.(*dataset)
			go future.generate(ethash.config.DatasetDir, ethash.config.DatasetsOnDisk, ethash.config.PowMode == ModeTest)
		}
	}
	return current
}

// Threads returns the number of mining threads currently enabled. This doesn't
// necessarily mean that mining is running!
func (ethash *Ethash) Threads() int {
	ethash.lock.Lock()
	defer ethash.lock.Unlock()

	return ethash.threads
}

// SetThreads updates the number of mining threads currently enabled. Calling
// this method does not start mining, only sets the thread count. If zero is
// specified, the miner will use all cores of the machine. Setting a thread
// count below zero is allowed and will cause the miner to idle, without any
// work being done.
func (ethash *Ethash) SetThreads(threads int) {
	ethash.lock.Lock()
	defer ethash.lock.Unlock()

	// If we're running a shared PoW, set the thread count on that instead
	if ethash.shared != nil {
		ethash.shared.SetThreads(threads)
		return
	}
	// Update the threads and ping any running seal to pull in any changes
	ethash.threads = threads
	select {
	case ethash.update <- struct{}{}:
	default:
	}
}

// Hashrate implements PoW, returning the measured rate of the search invocations
// per second over the last minute.
// Note the returned hashrate includes local hashrate, but also includes the total
// hashrate of all remote miner.
func (ethash *Ethash) Hashrate() float64 {
	// Short circuit if we are run the ethash in normal/test mode.
	if ethash.config.PowMode != ModeNormal && ethash.config.PowMode != ModeTest {
		return ethash.hashrate.Rate1()
	}
	var res = make(chan uint64, 1)

	select {
	case ethash.remote.fetchRateCh <- res:
	case <-ethash.remote.exitCh:
		// Return local hashrate only if ethash is stopped.
		return ethash.hashrate.Rate1()
	}

	// Gather total submitted hash rate of remote sealers.
	return ethash.hashrate.Rate1() + float64(<-res)
}

// APIs implements consensus.Engine, returning the user facing RPC APIs.
func (ethash *Ethash) APIs(chain consensus.ChainReader) []rpc.API {
	// In order to ensure backward compatibility, we exposes ethash RPC APIs
	// to both eth and ethash namespaces.
	return []rpc.API{
		{
			Namespace: "eth",
			Version:   "1.0",
			Service:   &API{ ethash, chain},
			Public:    true,
		},
		{
			Namespace: "ethash",
			Version:   "1.0",
			Service:   &API{ethash, chain},
			Public:    true,
		},
	}
}

// SeedHash is the seed to use for generating a verification cache and the mining
// dataset.
func SeedHash(block uint64) []byte {
	return seedHash(block)
}

func (ethash *Ethash) getSnapshot(checkNumber uint64) (*Election) {
	ethash.lockSigner.Lock()
	defer ethash.lockSigner.Unlock()
	if s, ok := ethash.recents.Get(checkNumber); ok {
		snap := s.(*Election)
		// If you have a recently created snapshot, load it and start
		return snap
	}
	return nil
}

// GetSnapshot shows a cache of election-related information.
func (ethash *Ethash) GetSnapshot(chain consensus.ChainReader, header *types.Header) *Election{
	checkNumber := header.Number.Uint64()/ethash.config.Epoch + 1
	var snap *Election

	snap = ethash.getSnapshot(checkNumber)
	if snap != nil {
		return snap
	}

	// If it is not in the cache, a new snapshot is created.
	snap = newElection(checkNumber, nil, ethash.config.Epoch)
	// If a snapshot is newly created, it must be read in its entirety.
	// It is not stored in the cache list.
	err := snap.CheckFullBlock(chain)
	if err != nil {
		return nil
	}
	return snap
}

// GetSnapshots shows the list in the cache
func (ethash *Ethash) GetSnapshots() []Election{
	snapList := make([]Election,0)
	for _, k := range ethash.recents.Keys(){
		if s, ok := ethash.recents.Get(k); ok {
			snap := s.(*Election)
			if snap.Total != 99 {
				snapList = append(snapList,*snap)
			}
		}
	}
	return snapList
}

// Proposals shows a list of proposers.
func (ethash *Ethash) Proposals() []*Vote {
	ethash.lockSigner.RLock()
	defer ethash.lockSigner.RUnlock()

	proposals := make([]*Vote,len(ethash.proposals))
	copy(proposals, ethash.proposals)
	return proposals
}

// AddPropose injects a new authorization proposal that the signer will attempt to
// push through.
func (ethash *Ethash) AddPropose(chain consensus.ChainReader, address common.Address, keepalive uint64, priority int) (*Vote, error) {
	// Does the address already have mining rights?
	isMine := chain.IsMiner(chain.CurrentHeader().Root,address,chain.CurrentHeader().Number.Uint64())
	if isMine > 0 {
		return nil, errors.New("miner who already has authority")
	}

	ethash.lockSigner.Lock()
	defer ethash.lockSigner.Unlock()

	// Already on the offer list?
	apply := false
	dept := uint64(0)
	for  idx, propose := range ethash.proposals {
		if propose.Addr == address {
			if propose.Apply == true && propose.ApplyDept > chain.CurrentHeader().Number.Uint64() {
				return propose, errors.New("already registered on the propose list")
			}

			// Default applied value
			apply = propose.Apply
			dept = propose.ApplyDept
			// Delete from the existing list
			ethash.proposals = append(ethash.proposals[:idx],ethash.proposals[idx+1:]...)
			break
		}
	}
	vote := &Vote{
		Addr:      address,
		Auth:      false,
		Keepalive: keepalive,
		Priority:  priority,
		Apply:     apply,
		ApplyDept: dept,
	}
	ethash.proposals = append(ethash.proposals, vote)
	// Let's sort by priority.
	sort.Sort(VoteByPriority(ethash.proposals))

	return vote, nil
}

// DeletePropose drops a currently running proposal, stopping the signer from casting
// further votes (either for or against).
func (ethash *Ethash) DeletePropose(address common.Address) error {
	// Has it already been applied?
	ethash.lockSigner.Lock()
	defer ethash.lockSigner.Unlock()

	for index, value := range ethash.proposals {
		if value.Addr == address {
			ethash.proposals = append(ethash.proposals[:index], ethash.proposals[index+1:]...)
			return  nil
		}
	}

	return nil
}


// SearchPropose finds data to be registered in the candidate list.
func (ethash *Ethash) SearchPropose(chain consensus.ChainReader, header *types.Header) {
	if len(ethash.proposals) == 0 {
		return
	}

	ethash.lockSigner.RLock()
	defer ethash.lockSigner.RUnlock()
	// Let's pick out those who already have authority from the suggested list.
	for _, propose := range ethash.proposals {
		if propose.Auth == false && propose.ApplyDept <= header.Number.Uint64() {
			parent := chain.GetBlock(header.ParentHash, header.Number.Uint64()-1)
			if parent == nil {
				continue
			}
			authMiner := chain.IsMiner(parent.Root(),propose.Addr,header.Number.Uint64())
			if authMiner > 0 {
				propose.Auth = true
			}
		}
	}
	index := 0
	// Let's select from the proposed candidates and add x names to the block header.
	for _, propose := range ethash.proposals {
		if propose.Auth == false {
			if (propose.Apply != true || propose.ApplyDept <= header.Number.Uint64()) && propose.Keepalive > header.Number.Uint64() {
				header.Election = append(header.Election, propose.Addr[:]...)
				index++
				if index >= candidatePerBlock {
					break
				}
			}
		}
	}
}

// ApplyPropose is actually applied to the proposer.
func (ethash *Ethash) ApplyPropose(header *types.Header, apply bool) error {
	// Has it already been applied?
	if len(header.Election) == 0 {
		return nil
	}
	number := header.Number.Uint64()
	dept := uint64((number/ethash.config.Epoch + 1) * ethash.config.Epoch)

	ethash.lockSigner.Lock()
	defer ethash.lockSigner.Unlock()

	for i := 0; i < len(header.Election)/common.AddressLength ; i++ {
		addr := common.BytesToAddress(header.Election[i*common.AddressLength: (i+1)*common.AddressLength])
		for i := 0; i < len(ethash.proposals); i++ {
			if ethash.proposals[i].Addr == addr{
				ethash.proposals[i].Apply = apply
				ethash.proposals[i].ApplyDept = dept
				break
			}
		}
	}
	return nil
}

// makeSliceUnique delete duplicate data.
func makeSliceUnique(s []common.Address) []common.Address {
	keys := make(map[common.Address]struct{})
	res := make([]common.Address, 0)
	for _, val := range s {
		if _, ok := keys[val]; ok {
			continue
		} else {
			keys[val] = struct{}{}
			res = append(res, val)
		}
	}
	return res
}

// SearchFullBlock reads data directly from the blockchain and checks the election data.
func (ethash *Ethash) SearchFullBlock(chain consensus.ChainReader, head *types.Header) ([]byte, error) {
	number := head.Number.Uint64()
	if number%ethash.config.Epoch != 0 || number == 0 {
		return nil, nil
	}

	lastNumber := head.Number.Uint64() - ethash.config.Epoch + 1

	var (
		header *types.Header
	)

	header = head

	minerVotes := make(map[common.Address]uint64)
	tmp := make(map[common.Address][]common.Address)

	for {
		if lastNumber >= number {
			break
		}

		header = chain.GetHeader(header.ParentHash, number-1)
		if header == nil {
			log.Crit("It is an unknown block. block: ",header.ParentHash, number-1)
			return nil, consensus.ErrUnknownAncestor
		}
		minerVotes[header.Coinbase] += 1
		if len(header.Election) > 0 {
			for i := 0; i < len(header.Election)/common.AddressLength ; i++ {
				tmp[common.BytesToAddress(header.Election[i*common.AddressLength: (i+1)*common.AddressLength])] = append(tmp[common.BytesToAddress(header.Election[i*common.AddressLength: (i+1)*common.AddressLength])],header.Coinbase)
			}
		}
		number = number - 1
	}

	if len(tmp) <= 0 {
		return nil, nil
	}

	var (
		sum uint64
	)
	addrList := make(signersAscending,0,len(tmp))
	for prop, coinbase := range tmp {
		sum = 0
		coinbase = makeSliceUnique(coinbase) // Deduplication
		for _, addrMiner := range coinbase {
			sum += minerVotes[addrMiner]
		}
		if sum > ethash.config.Epoch/votesPerRate {
			addrList = append(addrList, prop)
		}
	}
	if len(addrList) <= 0 {
		return nil, nil
	}
	sort.Sort(addrList)
	_, byteHash := Decode(addrList)
	return byteHash, nil
}

// GetElectionData enters the mining rights in the state db.
func (ethash *Ethash) GetElectionData(chain consensus.ChainReader, number uint64) (signersAscending,error) {
	checkNumber := number/ethash.config.Epoch
	var snap *Election

	ethash.lockSigner.Lock()
	if s, ok := ethash.recents.Get(checkNumber); ok {
		snap = s.(*Election)
		// If you have a recently created snapshot, load it and start
	} else {
		//If not, create a new snapshot.
		snap = newElection(checkNumber, nil, ethash.config.Epoch)
		ethash.recents.Add(snap.Key, snap)
	}
	ethash.lockSigner.Unlock()

	// If a snapshot is newly created, it must be read in its entirety.
	err := snap.CheckFullBlock(chain)
	if err != nil {
		return nil, err
	}

	return snap.Selected(), nil
}

func (ethash *Ethash) GetSnapshotHash(chain consensus.ChainReader, number uint64) ([]byte,error) {
	checkNumber := number/ethash.config.Epoch
	var snap *Election

	ethash.lockSigner.Lock()
	if s, ok := ethash.recents.Get(checkNumber); ok {
		snap = s.(*Election)
		// If you have a recently created snapshot, load it and start
	} else {
		// If not, create a new snapshot.
		snap = newElection(checkNumber, nil, ethash.config.Epoch)
		ethash.recents.Add(snap.Key, snap)
	}
	ethash.lockSigner.Unlock()

	addrList := snap.Selected()
	if len(addrList) == 0 {
		return nil, nil
	}

	sort.Sort(addrList)
	_, byteHash := Decode(addrList)

	return byteHash, nil
}


func (ethash *Ethash) ValidSnapShot(chain consensus.ChainReader, number uint64, election []byte) (common.Hash, error) {
	if number%ethash.config.Epoch != 0 {
		return common.Hash{}, nil
	}

	// Reads data with the previous number one block
	checkNumber :=  (number - 1)/ethash.config.Epoch + 1
	var (
		snap *Election
	)

	// Do you have any recent snapshots?
	ethash.lockSigner.Lock()
	if s, ok := ethash.recents.Get(checkNumber); ok {
		snap = s.(*Election)
		// If you have a recently created snapshot, load it and start
	} else {
		// If not, create a new snapshot.
		snap = newElection(checkNumber, nil, ethash.config.Epoch)
		ethash.recents.Add(snap.Key, snap)
	}
	ethash.lockSigner.Unlock()

	// If a snapshot is newly created, it must be read in its entirety.
	err := snap.CheckFullBlock(chain)
	if err != nil {
		return common.Hash{}, err
	}

	return snap.ValidSnapShot(chain, election)
}

// Snapshot retrieves the authorization snapshot at a given point in time.
func (ethash *Ethash) Snapshot(chain consensus.ChainReader, head *types.Header, parents []*types.Header) (*Election, error) {
	// Retrieves the voting snapshot for the header of the block.
	//If it is in the cache, read it from the cache.
	var (
		headers []*types.Header
		snap   	*Election
		checkNumber uint64
		number 		uint64
		hash 		common.Hash
		header *types.Header
	)
	header = head
	number, hash = header.Number.Uint64() , header.Hash()
	checkNumber =  (number-1)/ethash.config.Epoch+1

	ethash.lockSigner.Lock()
	// Do you have any recent snapshots?
	if s, ok := ethash.recents.Get(checkNumber); ok {
		snap = s.(*Election)
		// If you have a recently created snapshot, load it and start
	} else {
		//If not, create a new snapshot.
		snap = newElection(checkNumber, nil, ethash.config.Epoch)
		ethash.recents.Add(snap.Key, snap)
	}
	ethash.lockSigner.Unlock()

	// As it goes through the loop, it creates sub-snapshots. (Let's make it rotate until the epoch is 0)
	for {
		ret := snap.Add(number, hash, header.Coinbase, header.Election)
		if !ret {
			return snap, nil
		}
		if number%ethash.config.Epoch == 0 {
			break
		}
		headers = append(headers, header)

		// Let's go back and get the information in the header.
		if len(parents) > 0 {
			// If we have explicit parents, pick from there (enforced)
			header = parents[len(parents)-1]
			if header.Hash() != hash || header.Number.Uint64() != number {
				return nil, consensus.ErrUnknownAncestor
			}
			parents = parents[:len(parents)-1]
		} else {
			// No explicit parents (or no more left), reach out to the database
			header = chain.GetHeader(header.ParentHash, number-1)
			if header == nil {
				// If you haven't found the next block and haven't entered it yet, you may not be able to find it.
				log.Error("Block data could not be found in the chain. parent:%d number:%d",header.ParentHash, number-1)
				return snap, nil
			}
		}

		number, hash = number-1, header.Hash()
	}

	return snap, nil
}

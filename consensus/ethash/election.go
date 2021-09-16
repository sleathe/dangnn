package ethash

import (
	"bytes"
	"fmt"
	"sort"
	"sync"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/rlp"
	"golang.org/x/crypto/sha3"
)


// Vote represents a single vote that an authorized signer made to modify the
// list of authorizations.
type Vote struct {
	Addr        common.Address  // miner addr
	Auth        bool            // permission or not
	Keepalive   uint64          // alive time number of blocks
	Priority    int             // priority being registered

	//For internal use only.
	Apply       bool            // was it used
	ApplyDept   uint64          // Number of blocks applied when used
}

type VoteByPriority []*Vote

func (c VoteByPriority) Len() int {
	return len(c)
}
func (c VoteByPriority) Less(i, j int) bool {
	return c[i].Priority > c[j].Priority
}
func (c VoteByPriority) Swap(i, j int) {
	c[i], c[j] = c[j], c[i]
}

type AddressList []common.Address

type MinerBlock struct {
	Hash common.Hash		`json:"hash"`
	Miner common.Address	`json:"address"`
}

// Tally has a snapshot of the number of blocks mined for each miner.
type Tally struct {
	Authorize   bool                   `json:"authorize"` // Whether the vote is about authorizing or kicking someone
	Votes       int                    `json:"votes"`     // Number of votes until now wanting to pass the proposal
	Recommender map[uint64]AddressList                    // recommender's addr and recommendation block
}

type Election struct {
	Key			uint64

	Miners 	    map[common.Address]*Tally   `json:"miners"`     // The miners who created the block
	Total       uint64                      `json:"total"`      // Number of completed blocks
	IncomeData 	map[uint64]*MinerBlock      `json:"incomeData"` // Hash of the incoming block
	Income 	    []byte                                          // Counts whether a block has already been entered.

	EpochLength uint64
	lock   sync.RWMutex   // Protects the signer fields
}

type signersAscending []common.Address

func (s signersAscending) Len() int           { return len(s) }
func (s signersAscending) Less(i, j int) bool { return bytes.Compare(s[i][:], s[j][:]) < 0 }
func (s signersAscending) Swap(i, j int)      { s[i], s[j] = s[j], s[i] }

func newElection(index uint64, fixBlock *common.Hash, epochLength uint64) *Election {
	elect := &Election{
		Key:		index,
		Miners:  make(map[common.Address]*Tally),
		Income: make([]byte, epochLength/8+1),
		IncomeData: make(map[uint64]*MinerBlock),
		EpochLength : epochLength,
	}
	return elect
}

// Extract the minor address selected by voting from the snapshot
func (e *Election) calcVotes() signersAscending {
	votesByAddr := make(map[common.Address]uint64, 0)
	// Let's combine the recommenders.
	for _, miner := range e.Miners {
		uniqueAddr := make(map[common.Address]struct{}, 0)
		for _, addrList := range miner.Recommender {
			for _, val := range addrList {
				uniqueAddr[val] = struct{}{}
			}
		}

		for key, _ := range uniqueAddr {
			votesByAddr[key] += uint64(miner.Votes)
		}
	}
	if len(votesByAddr) == 0 {
		return nil
	}
	cpy := make(signersAscending, 0, len(votesByAddr))
	//
	for key, val := range votesByAddr {
		if val > e.EpochLength/votesPerRate {
			cpy = append(cpy, key)
		}
	}
	if len(cpy) == 0 {
		return nil
	}
	return cpy
}

func (e *Election) Selected() signersAscending {
	cpy := e.calcVotes()
	if cpy == nil {
		return nil
	}
	// Let's sort the recommenders. signersAscending.
	sort.Sort(cpy)
	return cpy
}

func (e *Election) ValidSnapShot(chain consensus.ChainReader, election []byte) (common.Hash, error) {
	// If no input has been made to the snapshot during the epoch period,
	// check that it is empty. (Not working)

	// Retrieves the selected recommender from the cache.
	cpy := e.calcVotes()
	if len(cpy) == 0 {
		if len(election) == 0 {
			// If 0 is sent, there is no election result.
			return common.Hash{}, nil
		} else {
			// The value is different from the election snapshot data.
			return common.Hash{}, fmt.Errorf("invalid snapshot (recive hash: %x local: %x size:%d)", election, 0x0, len(cpy))
		}
	}

	// Let's sort the recommenders. signersAscending
	sort.Sort(cpy)

	// Gets the hash value of the recommender.
	sanpHash, _ := Decode(cpy)

	if bytes.Equal(election, sanpHash.Bytes()) {
		//
		return sanpHash, nil
	}

	return common.Hash{}, fmt.Errorf("invalid snapshot (recive hash: %x local: %x size:%d)", election, sanpHash, len(cpy))
}

func Decode(sdata []common.Address) (common.Hash, []byte) {
	var hash common.Hash
	hasher := sha3.NewLegacyKeccak256()

	rlp.Encode(hasher, sdata)
	validHash := hasher.Sum(hash[:0])
	return hash, validHash
}

func (e *Election) CheckFullBlock(chain consensus.ChainReader ) error {
	var (
		bit,check byte
	)
	if e.Total == e.EpochLength - 1 {
		// The whole block already exists.
		return nil
	}

	startBlock, endBlock := e.Key*e.EpochLength - e.EpochLength + 1, e.Key*e.EpochLength
	log.Info("check snap block info start. block : ",startBlock,"endBlock : ", endBlock)

	var parentHeader  *types.Header
	for startBlock != endBlock {
		blockCount := startBlock%e.EpochLength
		bit, check = e.Income[blockCount/8],1 << (blockCount%8)
		if ok := bit & check != check; ok {
			// It is a block to which no data has been entered.
			if parentHeader == nil || parentHeader.Number.Uint64() != startBlock-1 {
				parentHeader = chain.GetHeaderByNumber(startBlock-1)
			}
			header := chain.GetHeaderByNumber(startBlock)
			if header == nil {
				// If you haven't found the next block and haven't entered it yet, you may not be able to find it.
				log.Info("Header not found in chain startBlock: ",startBlock)
				return nil
			}

			if header.ParentHash != parentHeader.Hash() {
				log.Info("It is not connected to the previous block. startBlock: ",startBlock,header.ParentHash.Hex() , parentHeader.Hash().Hex())
				return nil
			}

			e.Add(header.Number.Uint64(), header.Hash(), header.Coinbase, header.Election)
			parentHeader = header
		}

		startBlock++
	}
	return nil
}

// Add inserts a new block into the snapshot.
func (e *Election) Add(number uint64, hash common.Hash, miner common.Address, election []byte) (bool) {
	blockCount := number%e.EpochLength // blockCount 1~ epochLength

	// If blockCount is 0, it is a mining verification header.
	if blockCount == 0 {
		return false
	}

	// Determines whether the received block information is already received information.
	var (
		bit,check byte
		data *Tally
		exist bool
	)
	bit, check = e.Income[blockCount/8],1 << (blockCount%8)

	e.lock.Lock()
	defer e.lock.Unlock()
	if ok := bit & check != check; ok {
		// if there is no block
		if data , exist = e.Miners[miner]; !exist {
			data = &Tally{ Authorize: true, Votes: 1, Recommender: make(map[uint64]AddressList) }
			e.Miners[miner] = data
		} else {
			data.Votes += 1
		}
		e.IncomeData[number] = &MinerBlock{hash, miner}
		if len(election) > 0 {
			for i := 0; i < len(election)/common.AddressLength ; i++ {
				data.Recommender[number] = append(data.Recommender[number],common.BytesToAddress(election[i*common.AddressLength: (i+1)*common.AddressLength]))
			}
		}
		e.Income[blockCount/8] |= 1 << (blockCount%8)
		e.Total++
	} else {
		// if there was a block
		if value, exist := e.IncomeData[number]; exist{
			//  If there is election information, it should be compared if the hashes are the same and updated if they are different.
			if value.Hash == hash {
				return false
			}

			// Delete the previous block data
			if data, exist = e.Miners[value.Miner]; exist {

				delete(data.Recommender, number)
				data.Votes -= 1
			}
			delete(e.IncomeData,number)
			if data , exist = e.Miners[miner]; !exist {
				data = &Tally{ Authorize: true, Votes: 1, Recommender: make(map[uint64]AddressList) }
				e.Miners[miner] = data
			} else {
				data.Votes += 1
			}
			e.IncomeData[number] = &MinerBlock{hash, miner}

			// Update, check if block information is modified by sidechain.
			if len(election) > 0 {
				for i := 0; i < len(election)/common.AddressLength ; i++ {
					data.Recommender[number] = append(data.Recommender[number],common.BytesToAddress(election[i*common.AddressLength: (i+1)*common.AddressLength]))
				}
			}
		} else {
			// there can be no (need to delete)
			log.Error("[test code] there can be no")
		}
	}

	blockCount -= 1
	if blockCount > 0 {
		bit, check = e.Income[blockCount/8],1 << (blockCount%8)
		ret := bit & check != check	// true if there is no next block
		return ret
	}

	return false
}


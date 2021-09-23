// Copyright 2018 The go-ethereum Authors
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

package ethash

import (
	"errors"
	"fmt"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/rpc"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/types"
)

var errEthashStopped = errors.New("ethash stopped")
var errUnknownBlock = errors.New("unKnown Block")

// API exposes ethash related methods for the RPC interface.
type API struct {
	ethash *Ethash
	chain  consensus.ChainReader
}

// GetWork returns a work package for external miner.
//
// The work package consists of 3 strings:
//   result[0] - 32 bytes hex encoded current block header pow-hash
//   result[1] - 32 bytes hex encoded seed hash used for DAG
//   result[2] - 32 bytes hex encoded boundary condition ("target"), 2^256/difficulty
//   result[3] - hex encoded block number
func (api *API) GetWork() ([4]string, error) {
	if api.ethash.remote == nil {
		return [4]string{}, errors.New("not supported")
	}

	var (
		workCh = make(chan [4]string, 1)
		errc   = make(chan error, 1)
	)
	select {
	case api.ethash.remote.fetchWorkCh <- &sealWork{errc: errc, res: workCh}:
	case <-api.ethash.remote.exitCh:
		return [4]string{}, errEthashStopped
	}
	select {
	case work := <-workCh:
		return work, nil
	case err := <-errc:
		return [4]string{}, err
	}
}

// GetElection retrieves the state snapshot at a given block.
func (api *API) GetElection(number *rpc.BlockNumber) (*Election, error) {
	// Retrieve the requested block number (or current if none requested)
	var header *types.Header
	if number == nil || *number == rpc.LatestBlockNumber || *number == 0 {
		header = api.chain.CurrentHeader()
	} else {
		header = api.chain.GetHeaderByNumber(uint64(number.Int64()-1))
	}
	// Ensure we have an actually valid block and return its snapshot
	if header == nil {
		return nil, errUnknownBlock
	}

	return api.ethash.GetSnapshot(api.chain, header), nil
}

// GetElections prints out all snapshots in the cache.
func (api *API) GetElections(number *rpc.BlockNumber) ([]Election, error) {
	return api.ethash.GetSnapshots(), nil
}

// Proposals returns the current proposals the node tries to uphold and vote on.
func (api *API) Proposals() []*Vote {
	return api.ethash.Proposals()
}

// Propose injects a new authorization proposal that the signer will attempt to
// push through.
func (api *API) Propose(address common.Address, aliveTime uint64, priority int) (*Vote, error) {
	number := api.chain.CurrentHeader().Number.Uint64()
	maxAliveTime := uint64((number/votesEpochLength + 2) * votesEpochLength)
	if aliveTime == 0 {
		aliveTime = maxAliveTime
	} else {
		if aliveTime <= number || aliveTime > maxAliveTime {
			return nil, fmt.Errorf("it cannot be smaller than the current block (%d~%d)", number,  maxAliveTime)
		}
	}
	return api.ethash.AddPropose(api.chain, address, aliveTime, priority)
}

// Discard drops a currently running proposal, stopping the signer from casting
// further votes (either for or against).
func (api *API) Discard(address common.Address) error {
	return api.ethash.DeletePropose(address)
}

// SubmitWork can be used by external miner to submit their POW solution.
// It returns an indication if the work was accepted.
// Note either an invalid solution, a stale work a non-existent work will return false.
func (api *API) SubmitWork(nonce types.BlockNonce, hash, digest common.Hash) bool {
	if api.ethash.remote == nil {
		return false
	}

	var errc = make(chan error, 1)
	select {
	case api.ethash.remote.submitWorkCh <- &mineResult{
		nonce:     nonce,
		mixDigest: digest,
		hash:      hash,
		errc:      errc,
	}:
	case <-api.ethash.remote.exitCh:
		return false
	}
	err := <-errc
	return err == nil
}

// SubmitHashrate can be used for remote miners to submit their hash rate.
// This enables the node to report the combined hash rate of all miners
// which submit work through this node.
//
// It accepts the miner hash rate and an identifier which must be unique
// between nodes.
func (api *API) SubmitHashRate(rate hexutil.Uint64, id common.Hash) bool {
	if api.ethash.remote == nil {
		return false
	}

	var done = make(chan struct{}, 1)
	select {
	case api.ethash.remote.submitRateCh <- &hashrate{done: done, rate: uint64(rate), id: id}:
	case <-api.ethash.remote.exitCh:
		return false
	}

	// Block until hash rate submitted successfully.
	<-done
	return true
}

// GetHashrate returns the current hashrate for local CPU miner and remote miner.
func (api *API) GetHashrate() uint64 {
	return uint64(api.ethash.Hashrate())
}

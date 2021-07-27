package types

import (
	"crypto/ecdsa"
	"errors"
	"fmt"
	"github.com/ethereum/go-ethereum/rlp"
	"golang.org/x/crypto/sha3"
	"math/big"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/crypto"
	"github.com/ethereum/go-ethereum/params"
)

var (
	ErrInvalidBlockChainId = errors.New("invalid block chain id for signer")
)

// sigBlockCache is used to cache the derived sender and contains
// the signer used to derive it.
type sigBlockCache struct {
	signer BlockSigner
	from   common.Address
}

// MakeBlockSigner returns a Signer based on the given chain config and block number.
func MakeBlockSigner(config *params.ChainConfig) BlockSigner {
	return NewBlockSigner(config.ChainID)
}

// SignBlock signs the block using the given signer and private key
func SignBlock(block *Block, s BlockSigner, prv *ecdsa.PrivateKey) (*Block, error) {
	h := s.BlockHash(block.header)
	sig, err := crypto.Sign(h[:], prv)
	if err != nil {
		return nil, err
	}
	return block.WithBlockSignature(s, sig)
}

// BlockSender returns the address derived from the signature (V, R, S) using secp256k1
// elliptic curve and an error if it failed deriving or upon an incorrect
// signature.
//
// BlockSender may cache the address, allowing it to be used regardless of
// signing method. The cache is invalidated if the cached signer does
// not match the signer used in the current call.
func BlockSender(signer BlockSigner, header *Header) (common.Address, error) {
	//if sc := block.from.Load(); sc != nil {
	//	sigBlockCache := sc.(sigBlockCache)
	//	// If the signer used to derive from in a previous
	//	// call is not the same as used current, invalidate
	//	// the cache.
	//	if sigBlockCache.signer.BlockEqual(signer) {
	//		return sigBlockCache.from, nil
	//	}
	//}

	addr, err := signer.BlockSender(header)
	if err != nil {
		return common.Address{}, err
	}
	// block.from.Store(sigBlockCache{signer: signer, from: addr})
	return addr, nil
}

// BlockSigner encapsulates transaction signature handling. Note that this interface is not a
// stable API and may change at any time to accommodate new protocol rules.
type BlockSigner interface {
	// BlockSender returns the sender address of the transaction.
	BlockSender(block *Header) (common.Address, error)
	// BlockSignatureValues returns the raw R, S, V values corresponding to the
	// given signature.
	BlockSignatureValues(block *Header, sig []byte) (R, S, V *big.Int, err error)
	// BlockHash returns the hash to be signed.
	BlockHash(block *Header) common.Hash
	// BlockEqual returns true if the given signer is the same as the receiver.
	BlockEqual(BlockSigner) bool
}

type EIP155BlockSigner struct {
	chainId, chainIdMul *big.Int
}

func NewBlockSigner(chainId *big.Int) EIP155BlockSigner {
	if chainId == nil {
		chainId = new(big.Int)
	}
	return EIP155BlockSigner{
		chainId:    chainId,
		chainIdMul: new(big.Int).Mul(chainId, big.NewInt(2)),
	}
}

func (s EIP155BlockSigner) BlockEqual(s2 BlockSigner) bool {
	eip155, ok := s2.(EIP155BlockSigner)
	return ok && eip155.chainId.Cmp(s.chainId) == 0
}

func (s EIP155BlockSigner) BlockSender(header *Header) (common.Address, error) {
	//if !block.Protected() {
	//	return HomesteadSigner{}.Sender(block)
	//}
	if header.ChainId().Cmp(s.chainId) != 0 {
		return common.Address{}, ErrInvalidBlockChainId
	}
	V := new(big.Int).Sub(header.V, s.chainIdMul)
	V.Sub(V, big8)
	return recoverBlockPlain(s.BlockHash(header), header.R, header.S, V, true)
}

// BlockSignatureValues returns signature values. This signature
// needs to be in the [R || S || V] format where V is 0 or 1.
func (s EIP155BlockSigner) BlockSignatureValues(header *Header, sig []byte) (R, S, V *big.Int, err error) {
	if len(sig) != crypto.SignatureLength {
		return nil, nil, nil, fmt.Errorf("wrong size for signature: got %d, want %d", len(sig), crypto.SignatureLength)
	}
	R = new(big.Int).SetBytes(sig[:32])
	S = new(big.Int).SetBytes(sig[32:64])
	V = new(big.Int).SetBytes([]byte{sig[64] + 27})

	if s.chainId.Sign() != 0 {
		V = big.NewInt(int64(sig[64] + 35))
		V.Add(V, s.chainIdMul)
	}
	return R, S, V, nil
}

// BlockHash returns the hash to be signed by the sender.
// It does not uniquely identify the transaction.
func (s EIP155BlockSigner) BlockHash(header *Header) (hash common.Hash) {
	//return rlpHash([]interface{}{
	//	block.header.AccountNonce,
	//	block.header.Price,
	//	block.header.GasLimit,
	//	block.header.Recipient,
	//	block.header.Amount,
	//	block.header.Payload,
	//	s.chainId, uint(0), uint(0),
	//})

	hasher := sha3.NewLegacyKeccak256()

	rlp.Encode(hasher, []interface{}{
		header.ParentHash,
		header.UncleHash,
		header.Coinbase,
		header.Root,
		header.TxHash,
		header.ReceiptHash,
		header.Bloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Extra,
	})


	hasher.Sum(hash[:0])
	return hash
}

func recoverBlockPlain(sighash common.Hash, R, S, Vb *big.Int, homestead bool) (common.Address, error) {
	if Vb.BitLen() > 8 {
		return common.Address{}, ErrInvalidSig
	}
	V := byte(Vb.Uint64() - 27)
	if !crypto.ValidateSignatureValues(V, R, S, homestead) {
		return common.Address{}, ErrInvalidSig
	}
	// encode the signature in uncompressed format
	r, s := R.Bytes(), S.Bytes()
	sig := make([]byte, crypto.SignatureLength)
	copy(sig[32-len(r):32], r)
	copy(sig[64-len(s):64], s)
	sig[64] = V
	// recover the public key from the signature
	pub, err := crypto.Ecrecover(sighash[:], sig)
	if err != nil {
		return common.Address{}, err
	}
	if len(pub) == 0 || pub[0] != 4 {
		return common.Address{}, errors.New("invalid public key")
	}
	var addr common.Address
	copy(addr[:], crypto.Keccak256(pub[1:])[12:])
	return addr, nil
}

// deriveBlockChainId derives the chain id from the given v parameter
func deriveBlockChainId(v *big.Int) *big.Int {
	if v.BitLen() <= 64 {
		v := v.Uint64()
		if v == 27 || v == 28 {
			return new(big.Int)
		}
		return new(big.Int).SetUint64((v - 35) / 2)
	}
	v = new(big.Int).Sub(v, big.NewInt(35))
	return v.Div(v, big.NewInt(2))
}

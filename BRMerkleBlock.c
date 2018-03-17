//
//  BRMerkleBlock.c
//
//  Created by Aaron Voisine on 8/6/15.
//  Copyright (c) 2015 breadwallet LLC
//
//  Permission is hereby granted, free of charge, to any person obtaining a copy
//  of this software and associated documentation files (the "Software"), to deal
//  in the Software without restriction, including without limitation the rights
//  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
//  copies of the Software, and to permit persons to whom the Software is
//  furnished to do so, subject to the following conditions:
//
//  The above copyright notice and this permission notice shall be included in
//  all copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//  THE SOFTWARE.

#include "BRMerkleBlock.h"
#include "BRCrypto.h"
#include "BRAddress.h"
#include "BRInt.h"
#include "BRSet.h"
#include <stdlib.h>
#include <inttypes.h>
#include <limits.h>
#include <string.h>
#include <assert.h>

#define MAX_PROOF_OF_WORK 0x1d00ffff    // highest value for difficulty target (higher values are less difficult)
#define TARGET_SPACING    600           // 10-minutes block interval
#define DAA_HEIGHT        504031        // D601 hard fork height: https://reviews.bitcoinabc.org/D601

inline static int _ceil_log2(int x)
{
    int r = (x & (x - 1)) ? 1 : 0;
    
    while ((x >>= 1) != 0) r++;
    return r;
}

// from https://en.bitcoin.it/wiki/Protocol_specification#Merkle_Trees
// Merkle trees are binary trees of hashes. Merkle trees in bitcoin use a double SHA-256, the SHA-256 hash of the
// SHA-256 hash of something. If, when forming a row in the tree (other than the root of the tree), it would have an odd
// number of elements, the final double-hash is duplicated to ensure that the row has an even number of hashes. First
// form the bottom row of the tree with the ordered double-SHA-256 hashes of the byte streams of the transactions in the
// block. Then the row above it consists of half that number of hashes. Each entry is the double-SHA-256 of the 64-byte
// concatenation of the corresponding two hashes below it in the tree. This procedure repeats recursively until we reach
// a row consisting of just a single double-hash. This is the merkle root of the tree.
//
// from https://github.com/bitcoin/bips/blob/master/bip-0037.mediawiki#Partial_Merkle_branch_format
// The encoding works as follows: we traverse the tree in depth-first order, storing a bit for each traversed node,
// signifying whether the node is the parent of at least one matched leaf txid (or a matched txid itself). In case we
// are at the leaf level, or this bit is 0, its merkle node hash is stored, and its children are not explored further.
// Otherwise, no hash is stored, but we recurse into both (or the only) child branch. During decoding, the same
// depth-first traversal is performed, consuming bits and hashes as they were written during encoding.
//
// example tree with three transactions, where only tx2 is matched by the bloom filter:
//
//     merkleRoot
//      /     \
//    m1       m2
//   /  \     /  \
// tx1  tx2 tx3  tx3
//
// flag bits (little endian): 00001011 [merkleRoot = 1, m1 = 1, tx1 = 0, tx2 = 1, m2 = 0, byte padding = 000]
// hashes: [tx1, tx2, m2]
//
// NOTE: this merkle tree design has a security vulnerability (CVE-2012-2459), which can be defended against by
// considering the merkle root invalid if there are duplicate hashes in any rows with an even number of elements

// returns a newly allocated merkle block struct that must be freed by calling BRMerkleBlockFree()
BRMerkleBlock *BRMerkleBlockNew(void)
{
    BRMerkleBlock *block = calloc(1, sizeof(*block));

    assert(block != NULL);
    
    block->height = BLOCK_UNKNOWN_HEIGHT;
    return block;
}


//Math Functions
#define uint256_supeq(a, b) (a.u64[3] > b.u64[3]) || ((a.u64[3] == b.u64[3]) && ((a.u64[2] > b.u64[2]) || ((a.u64[2] == b.u64[2]) && ((a.u64[1] > b.u64[1]) || ((a.u64[1] == b.u64[1]) && (a.u64[0] >= b.u64[0]))))))
UInt256 shiftLeft(UInt256 a, uint8_t bits) {
    UInt256 r = UINT256_ZERO;
    int k = bits / 64;
    bits = bits % 64;
    for (int i = 0; i < 4; i++) {
        if (i + k + 1 < 4 && bits != 0)
            r.u64[i + k + 1] |= (a.u64[i] >> (64 - bits));
        if (i + k < 4)
            r.u64[i + k] |= (a.u64[i] << bits);
    }
    return r;
}

UInt256 shiftRight(UInt256 a, uint8_t bits) {
    UInt256 r = UINT256_ZERO;
    int k = bits / 64;
    bits = bits % 64;
    for (int i = 0; i < 4; i++) {
        if (i - k - 1 >= 0 && bits != 0)
            r.u64[i - k - 1] |= (a.u64[i] << (64 - bits));
        if (i - k >= 0)
            r.u64[i - k] |= (a.u64[i] >> bits);
    }
    return r;
}



UInt256 expand(int32_t nCompact)
{
    int nSize = nCompact >> 24;
    UInt256 nWord = UINT256_ZERO;
    nWord.u32[0] =  nCompact & (uint32_t)0x007fffff;
    if (nSize <= 3) {
        nWord = shiftRight(nWord,(uint8_t) 8 * (3 - nSize));
    } else {
        nWord = shiftLeft(nWord,(uint8_t)( 8 * (nSize - 3)));
    }
    return nWord;
}

int bits(UInt256 number)
{
    for (int pos = 8 - 1; pos >= 0; pos--) {
        if (number.u32[pos]) {
            for (int bits = 31; bits > 0; bits--) {
                if (number.u32[pos] & 1 << bits)
                    return 32 * pos + bits + 1;
            }
            return 32 * pos + 1;
        }
    }
    return 0;
}

int32_t compact(UInt256 number)
{
    int nSize = (bits(number) + 7) / 8;
    uint32_t nCompact = 0;
    if (nSize <= 3) {
        nCompact = number.u32[0] << 8 * (3 - nSize);
    } else {
        UInt256 bn = shiftRight(number,(uint8_t) (8 * (nSize - 3)));
        nCompact = bn.u32[0];
    }
    // The 0x00800000 bit denotes the sign.
    // Thus, if it is already set, divide the mantissa by 256 and increase the exponent.
    if (nCompact & 0x00800000) {
        nCompact >>= 8;
        nSize++;
    }
//    assert((nCompact & ~0x007fffff) == 0);
    assert(nSize < 256);
    nCompact |= nSize << 24;
    return nCompact;
}

UInt256 add(UInt256 a, UInt256 b) {
    uint64_t carry = 0;
    UInt256 r = UINT256_ZERO;
    for (int i = 0; i < 8; i++) {
        uint64_t sum = (uint64_t)a.u32[i] + (uint64_t)b.u32[i] + carry;
        r.u32[i] = (uint32_t)sum;
        carry = sum >> 32;
    }
    return r;
}

UInt256 addOne(UInt256 a) {
    UInt256 r = ((UInt256) { .u64 = { 1, 0, 0, 0 } });
    return add(a, r);
}

UInt256 neg(UInt256 a) {
    UInt256 r = UINT256_ZERO;
    for (int i = 0; i < 4; i++) {
        r.u64[i] = ~a.u64[i];
    }
    return r;
}

UInt256 subtract(UInt256 a, UInt256 b) {
    return add(a,addOne(neg(b)));
}

UInt256 divide(UInt256 a, UInt256 b)
{
    UInt256 div = b;     // make a copy, so we can shift.
    UInt256 num = a;     // make a copy, so we can subtract.
    UInt256 r = UINT256_ZERO;                  // the quotient.
    int num_bits = bits(num);
    int div_bits = bits(div);
    assert (div_bits != 0);
    if (div_bits > num_bits) return r; // the result is certainly 0.
    int shift = num_bits - div_bits;
    UInt256 temp = shiftLeft(div, shift); // shift so that div and nun align.
    div = temp;
    while (shift >= 0) {
        if (uint256_supeq(num,div)) {
            num = subtract(num,div);
            r.u32[shift / 32] |= (1 << (shift & 31)); // set a bit of the result.
        }
        div = shiftRight(div, 1); // shift back.
        shift--;
    }
    // num now contains the remainder of the division.
    return r;
}

UInt256 multiply(UInt256 a, uint32_t b)
{
    uint64_t carry = 0;
    for (int i = 0; i < 8; i++) {
        uint64_t n = carry + (uint64_t)b * (uint64_t)a.u32[i];
        a.u32[i] = n & 0xffffffff;
        carry = n >> 32;
    }
    return a;
}

// buf must contain either a serialized merkleblock or header
// returns a merkle block struct that must be freed by calling BRMerkleBlockFree()
BRMerkleBlock *BRMerkleBlockParse(const uint8_t *buf, size_t bufLen)
{
    BRMerkleBlock *block = (buf && 80 <= bufLen) ? BRMerkleBlockNew() : NULL;
    size_t off = 0, len = 0;
    
    assert(buf != NULL || bufLen == 0);
    
    if (block) {
        block->version = UInt32GetLE(&buf[off]);
        off += sizeof(uint32_t);
        block->prevBlock = UInt256Get(&buf[off]);
        off += sizeof(UInt256);
        block->merkleRoot = UInt256Get(&buf[off]);
        off += sizeof(UInt256);
        block->timestamp = UInt32GetLE(&buf[off]);
        off += sizeof(uint32_t);
        block->target = UInt32GetLE(&buf[off]);
        off += sizeof(uint32_t);
        block->nonce = UInt32GetLE(&buf[off]);
        off += sizeof(uint32_t);
        
        if (off + sizeof(uint32_t) <= bufLen) {
            block->totalTx = UInt32GetLE(&buf[off]);
            off += sizeof(uint32_t);
            block->hashesCount = (size_t)BRVarInt(&buf[off], (off <= bufLen ? bufLen - off : 0), &len);
            off += len;
            len = block->hashesCount*sizeof(UInt256);
            block->hashes = (off + len <= bufLen) ? malloc(len) : NULL;
            if (block->hashes) memcpy(block->hashes, &buf[off], len);
            off += len;
            block->flagsLen = (size_t)BRVarInt(&buf[off], (off <= bufLen ? bufLen - off : 0), &len);
            off += len;
            len = block->flagsLen;
            block->flags = (off + len <= bufLen) ? malloc(len) : NULL;
            if (block->flags) memcpy(block->flags, &buf[off], len);
        }
        
        BRSHA256_2(&block->blockHash, buf, 80);
    }
    
    return block;
}

// returns number of bytes written to buf, or total bufLen needed if buf is NULL (block->height is not serialized)
size_t BRMerkleBlockSerialize(const BRMerkleBlock *block, uint8_t *buf, size_t bufLen)
{
    size_t off = 0, len = 80;
    
    assert(block != NULL);
    
    if (block->totalTx > 0) {
        len += sizeof(uint32_t) + BRVarIntSize(block->hashesCount) + block->hashesCount*sizeof(UInt256) +
               BRVarIntSize(block->flagsLen) + block->flagsLen;
    }
    
    if (buf && len <= bufLen) {
        UInt32SetLE(&buf[off], block->version);
        off += sizeof(uint32_t);
        UInt256Set(&buf[off], block->prevBlock);
        off += sizeof(UInt256);
        UInt256Set(&buf[off], block->merkleRoot);
        off += sizeof(UInt256);
        UInt32SetLE(&buf[off], block->timestamp);
        off += sizeof(uint32_t);
        UInt32SetLE(&buf[off], block->target);
        off += sizeof(uint32_t);
        UInt32SetLE(&buf[off], block->nonce);
        off += sizeof(uint32_t);
    
        if (block->totalTx > 0) {
            UInt32SetLE(&buf[off], block->totalTx);
            off += sizeof(uint32_t);
            off += BRVarIntSet(&buf[off], (off <= bufLen ? bufLen - off : 0), block->hashesCount);
            if (block->hashes) memcpy(&buf[off], block->hashes, block->hashesCount*sizeof(UInt256));
            off += block->hashesCount*sizeof(UInt256);
            off += BRVarIntSet(&buf[off], (off <= bufLen ? bufLen - off : 0), block->flagsLen);
            if (block->flags) memcpy(&buf[off], block->flags, block->flagsLen);
            off += block->flagsLen;
        }
    }
    
    return (! buf || len <= bufLen) ? len : 0;
}

static size_t _BRMerkleBlockTxHashesR(const BRMerkleBlock *block, UInt256 *txHashes, size_t hashesCount, size_t *idx,
                                      size_t *hashIdx, size_t *flagIdx, int depth)
{
    uint8_t flag;
    
    if (*flagIdx/8 < block->flagsLen && *hashIdx < block->hashesCount) {
        flag = (block->flags[*flagIdx/8] & (1 << (*flagIdx % 8)));
        (*flagIdx)++;
    
        if (! flag || depth == _ceil_log2(block->totalTx)) {
            if (flag && *idx < hashesCount) {
                if (txHashes) txHashes[*idx] = block->hashes[*hashIdx]; // leaf
                (*idx)++;
            }
        
            (*hashIdx)++;
        }
        else {
            _BRMerkleBlockTxHashesR(block, txHashes, hashesCount, idx, hashIdx, flagIdx, depth + 1); // left branch
            _BRMerkleBlockTxHashesR(block, txHashes, hashesCount, idx, hashIdx, flagIdx, depth + 1); // right branch
        }
    }

    return *idx;
}

// populates txHashes with the matched tx hashes in the block
// returns number of hashes written, or the total hashesCount needed if txHashes is NULL
size_t BRMerkleBlockTxHashes(const BRMerkleBlock *block, UInt256 *txHashes, size_t hashesCount)
{
    size_t idx = 0, hashIdx = 0, flagIdx = 0;

    assert(block != NULL);
    
    return _BRMerkleBlockTxHashesR(block, txHashes, (txHashes) ? hashesCount : SIZE_MAX, &idx, &hashIdx, &flagIdx, 0);
}

// sets the hashes and flags fields for a block created with BRMerkleBlockNew()
void BRMerkleBlockSetTxHashes(BRMerkleBlock *block, const UInt256 hashes[], size_t hashesCount,
                              const uint8_t *flags, size_t flagsLen)
{
    assert(block != NULL);
    assert(hashes != NULL || hashesCount == 0);
    assert(flags != NULL || flagsLen == 0);
    
    if (block->hashes) free(block->hashes);
    block->hashes = (hashesCount > 0) ? malloc(hashesCount*sizeof(UInt256)) : NULL;
    if (block->hashes) memcpy(block->hashes, hashes, hashesCount*sizeof(UInt256));
    if (block->flags) free(block->flags);
    block->flags = (flagsLen > 0) ? malloc(flagsLen) : NULL;
    if (block->flags) memcpy(block->flags, flags, flagsLen);
}

// recursively walks the merkle tree to calculate the merkle root
// NOTE: this merkle tree design has a security vulnerability (CVE-2012-2459), which can be defended against by
// considering the merkle root invalid if there are duplicate hashes in any rows with an even number of elements
static UInt256 _BRMerkleBlockRootR(const BRMerkleBlock *block, size_t *hashIdx, size_t *flagIdx, int depth)
{
    uint8_t flag;
    UInt256 hashes[2], md = UINT256_ZERO;

    if (*flagIdx/8 < block->flagsLen && *hashIdx < block->hashesCount) {
        flag = (block->flags[*flagIdx/8] & (1 << (*flagIdx % 8)));
        (*flagIdx)++;

        if (flag && depth != _ceil_log2(block->totalTx)) {
            hashes[0] = _BRMerkleBlockRootR(block, hashIdx, flagIdx, depth + 1); // left branch
            hashes[1] = _BRMerkleBlockRootR(block, hashIdx, flagIdx, depth + 1); // right branch

            if (! UInt256IsZero(hashes[0]) && ! UInt256Eq(hashes[0], hashes[1])) {
                if (UInt256IsZero(hashes[1])) hashes[1] = hashes[0]; // if right branch is missing, dup left branch
                BRSHA256_2(&md, hashes, sizeof(hashes));
            }
            else *hashIdx = SIZE_MAX; // defend against (CVE-2012-2459)
        }
        else md = block->hashes[(*hashIdx)++]; // leaf
    }
    
    return md;
}

// true if merkle tree and timestamp are valid, and proof-of-work matches the stated difficulty target
// NOTE: this only checks if the block difficulty matches the difficulty target in the header, it does not check if the
// target is correct for the block's height in the chain - use BRMerkleBlockVerifyDifficulty() for that
int BRMerkleBlockIsValid(const BRMerkleBlock *block, uint32_t currentTime)
{
    assert(block != NULL);
    
    // target is in "compact" format, where the most significant byte is the size of resulting value in bytes, the next
    // bit is the sign, and the remaining 23bits is the value after having been right shifted by (size - 3)*8 bits
    static const uint32_t maxsize = MAX_PROOF_OF_WORK >> 24, maxtarget = MAX_PROOF_OF_WORK & 0x00ffffff;
    const uint32_t size = block->target >> 24, target = block->target & 0x00ffffff;
    size_t hashIdx = 0, flagIdx = 0;
    UInt256 merkleRoot = _BRMerkleBlockRootR(block, &hashIdx, &flagIdx, 0), t = UINT256_ZERO;
    int r = 1;

    // check if merkle root is correct
    if (block->totalTx > 0 && ! UInt256Eq(merkleRoot, block->merkleRoot)) r = 0;
    
    // check if timestamp is too far in future
    if (block->timestamp > currentTime + BLOCK_MAX_TIME_DRIFT) r = 0;
    
    // check if proof-of-work target is out of range
    if (target == 0 || target & 0x00800000 || size > maxsize || (size == maxsize && target > maxtarget)) r = 0;
    
    if (size > 3) UInt32SetLE(&t.u8[size - 3], target);
    else UInt32SetLE(t.u8, target >> (3 - size)*8);
    
    for (int i = sizeof(t) - 1; r && i >= 0; i--) { // check proof-of-work
        if (block->blockHash.u8[i] < t.u8[i]) break;
        if (block->blockHash.u8[i] > t.u8[i]) r = 0;
    }
    
    return r;
}

// true if the given tx hash is known to be included in the block
int BRMerkleBlockContainsTxHash(const BRMerkleBlock *block, UInt256 txHash)
{
    int r = 0;
    
    assert(block != NULL);
    assert(! UInt256IsZero(txHash));
    
    for (size_t i = 0; ! r && i < block->hashesCount; i++) {
        if (UInt256Eq(block->hashes[i], txHash)) r = 1;
    }
    
    return r;
}

static inline int InvertLowestOne(int n) {
    return n & (n - 1);
}
 int GetSkipHeight(int height) {
    if (height < 2) {
        return 0;
    }

    // Determine which height to jump back to. Any number strictly lower than
    // height is acceptable, but the following expression seems to perform well
    // in simulations (max 110 steps to go back up to 2**18 blocks).
    return (height & 1) ? InvertLowestOne(InvertLowestOne(height - 1)) + 1
                        : InvertLowestOne(height);
}

inline static UInt256 targetToWork(uint32_t target) {
    UInt256 bnTarget = expand(target);
    // We need to compute 2**256 / (bnTarget+1), but we can't represent 2**256
    // as it's too large for a UInt256. However, as 2**256 is at least as
    // large as bnTarget+1, it is equal to ((2**256 - bnTarget - 1) /
    // (bnTarget+1)) + 1, or ~bnTarget / (nTarget+1) + 1.
    return addOne(divide(neg(bnTarget), addOne(bnTarget)));
}

inline static UInt256 workToTarget(UInt256 work)
{
    // We need to compute T = (2^256 / W) - 1 but 2^256 doesn't fit in 256 bits.
    // By expressing 1 as W / W, we get (2^256 - W) / W, and we can compute
    // 2^256 - W as the complement of W.
    return divide(neg(work), work);
}

// To reduce the impact of timestamp manipulation, we select the block we are
// basing our computation on via a median of 3.
// Reference: http://github.com/Bitcoin-ABC/bitcoin-abc/master/src/pow.cpp#L201
inline static const BRMerkleBlock *medianBlock(const BRMerkleBlock *b0, const BRSet *blockSet)
{
    const BRMerkleBlock *tmp, *b1, *b2;

    b1 = (b0) ? BRSetGet(blockSet, &b0->prevBlock) : NULL;
    b2 = (b1) ? BRSetGet(blockSet, &b1->prevBlock) : NULL;

    if (b0 && b2 && b0->timestamp > b2->timestamp) tmp = b0, b0 = b2, b2 = tmp;
    if (b0 && b1 && b0->timestamp > b1->timestamp) tmp = b0, b0 = b1, b1 = tmp;
    if (b1 && b2 && b1->timestamp > b2->timestamp) tmp = b1, b1 = b2, b2 = tmp;

    return (b0 && b1 && b2) ? b1 : NULL;
}

inline static const BRMerkleBlock *ancestor(const BRMerkleBlock *block, int jumps, const BRSet *blockSet)
{
    for (int i = 0; block && i < jumps; i++) block = BRSetGet(blockSet, &block->prevBlock);
    return block;
}

inline static UInt256 averageWork(const BRMerkleBlock *top, const BRMerkleBlock *bottom, const BRSet *blockSet)
{
    uint32_t time = (top && bottom) ? top->timestamp - bottom->timestamp : 0;

    // Sanitize excessive numbers
    if (time > 288*TARGET_SPACING) time = 288*TARGET_SPACING;
    if (time < 72*TARGET_SPACING) time =  72*TARGET_SPACING;

    // Calculate total work since bottom block to top block
    UInt256 work = UINT256_ZERO;
    for (const BRMerkleBlock *b = top; b && b != bottom; b = BRSetGet(blockSet, &b->prevBlock)) {
        work = add(work, targetToWork(b->target));
    }

    UInt256 t = UINT256_ZERO;
    t.u32[0] = time;

    return divide(multiply(work, TARGET_SPACING), t);
}

// verifies the block difficulty target is correct for the block's position in the chain
int BRMerkleBlockVerifyDifficulty(const BRMerkleBlock *block, const BRSet *blockSet)
{
    if (block->height <= DAA_HEIGHT) return 1;

    const BRMerkleBlock *top = medianBlock(ancestor(block, 1, blockSet), blockSet);
    const BRMerkleBlock *bottom = medianBlock(ancestor(block, 145, blockSet), blockSet);

    UInt256 work = averageWork(top, bottom, blockSet);

    int32_t target = compact(workToTarget(work));
    if (target > MAX_PROOF_OF_WORK) target = MAX_PROOF_OF_WORK;

    if (top && bottom && block->target != target) return 0;

    return 1;
}

int BRMerkleBlockVerifyDifficultyTestNet(const BRMerkleBlock *block, const BRSet *blockSet)
{
    return 1;
}

// frees memory allocated by BRMerkleBlockParse
void BRMerkleBlockFree(BRMerkleBlock *block)
{
    assert(block != NULL);
    
    if (block->hashes) free(block->hashes);
    if (block->flags) free(block->flags);
    free(block);
}

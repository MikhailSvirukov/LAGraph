// SPDX-License-Identifier: BSD-2-Clause
// Private Bloom primitives: fixed shape per path query, immutable 64-bit leaves.
#ifndef LG_RPQ_PATH_BLOOM_H
#define LG_RPQ_PATH_BLOOM_H
#include <math.h>
#ifndef LG_RPQ_PATH_BLOOM_FPR
#define LG_RPQ_PATH_BLOOM_FPR 0.00001
#endif
#ifndef LG_RPQ_PATH_BLOOM_MAX_BYTES
#define LG_RPQ_PATH_BLOOM_MAX_BYTES (256 * 1024)
#endif

typedef struct { size_t words, hashes, capacity ; unsigned depth ; } LG_RpqPath_BloomShape ;
static uint64_t LG_RpqPath_Hash (uint64_t x)
{
    x = (x ^ (x >> 30)) * UINT64_C (0xbf58476d1ce4e5b9) ;
    x = (x ^ (x >> 27)) * UINT64_C (0x94d049bb133111eb) ;
    return x ^ (x >> 31) ;
}
static uint64_t LG_RpqPath_BloomKey (uint64_t x, uint64_t y, uint64_t z)
{
    uint64_t h = LG_RpqPath_Hash (x + UINT64_C (0x9e3779b97f4a7c15)) ;
    return LG_RpqPath_Hash (LG_RpqPath_Hash (h ^ y) ^ z) ;
}
static int LG_RpqPath_BloomShapeNew (size_t capacity, size_t max_bytes,
    LG_RpqPath_BloomShape *shape)
{
    double p = LG_RPQ_PATH_BLOOM_FPR ;
    if (!(p > 0 && p < 1) || max_bytes < sizeof (uint64_t)) return GrB_INVALID_VALUE ;
    if (capacity == 0) capacity = 1 ;
    // Reserve representable words first, then clamp before converting double.
    size_t max_words = max_bytes / sizeof (uint64_t) ;
    if (max_words > SIZE_MAX / 64) max_words = SIZE_MAX / 64 ;
    double wanted = ceil (-(double) capacity * log (p) / (log (2.0) * log (2.0)) / 64.0) ;
    size_t words = wanted >= (double) max_words ? max_words : (size_t) wanted ;
    if (words == 0) words = 1 ;
    double k = round ((double) words * 64 / capacity * log (2.0)) ;
    size_t hashes = k < 1 ? 1 : k > 64 ? 64 : (size_t) k ;
    unsigned depth = 0 ;
    for (size_t t = words - 1 ; t != 0 ; t >>= 1) depth++ ;
    *shape = (LG_RpqPath_BloomShape) { words, hashes, capacity, depth } ;
    return GrB_SUCCESS ;
}
static size_t LG_RpqPath_BloomPosition (const LG_RpqPath_BloomShape *shape,
    uint64_t hash, uint64_t stride, size_t i)
{
    return (size_t) ((hash + i * stride) % (shape->words * 64)) ;
}
static uint64_t LG_RpqPath_BloomStride (uint64_t hash)
{
    return LG_RpqPath_Hash (hash ^ UINT64_C (0xd1b54a32d192ed03)) | 1 ;
}

typedef struct LG_RpqPath_BloomNode LG_RpqPath_BloomNode ;
struct LG_RpqPath_BloomNode
{
    union { const LG_RpqPath_BloomNode *child[2] ; uint64_t word ; } data ;
} ;
typedef struct LG_RpqPath_BloomNodes
{
    struct LG_RpqPath_BloomNodes *next ;
    size_t count ;
    LG_RpqPath_BloomNode nodes[64] ;
} LG_RpqPath_BloomNodes ;
typedef struct { size_t word ; uint64_t bits ; } LG_RpqPath_BloomChange ;
static int LG_RpqPath_BloomChangeOrder (const void *a, const void *b)
{
    size_t x = ((const LG_RpqPath_BloomChange *) a)->word ;
    size_t y = ((const LG_RpqPath_BloomChange *) b)->word ;
    return (x > y) - (x < y) ;
}
static int LG_RpqPath_BloomNodeNew (LG_RpqPath_BloomNodes **pool,
    LG_RpqPath_BloomNode **node, char *msg)
{
    if (*pool == NULL || (*pool)->count == 64)
    {
        LG_RpqPath_BloomNodes *block = NULL ;
        int info = LAGraph_Malloc ((void **) &block, 1, sizeof (*block), msg) ;
        if (info != GrB_SUCCESS) return info ;
        block->next = *pool ; block->count = 0 ; *pool = block ;
    }
    *node = &(*pool)->nodes[(*pool)->count++] ;
    return GrB_SUCCESS ;
}
static uint64_t LG_RpqPath_BloomWord (const LG_RpqPath_BloomNode *node,
    unsigned depth, size_t word)
{
    while (node != NULL && depth != 0)
    { depth-- ; node = node->data.child[(word >> depth) & 1] ; }
    return node == NULL ? 0 : node->data.word ;
}
static bool LG_RpqPath_BloomMayContain (const LG_RpqPath_BloomShape *shape,
    const LG_RpqPath_BloomNode *root, uint64_t hash)
{
    uint64_t stride = LG_RpqPath_BloomStride (hash) ;
    for (size_t k = 0 ; k < shape->hashes ; k++)
    {
        size_t bit = LG_RpqPath_BloomPosition (shape, hash, stride, k) ;
        if (!(LG_RpqPath_BloomWord (root, shape->depth, bit / 64) &
              (UINT64_C (1) << (bit % 64)))) return false ;
    }
    return true ;
}
// Batch path-copy: clone only the union of branches leading to changed words.
static int LG_RpqPath_BloomUpdate (LG_RpqPath_BloomNodes **pool,
    const LG_RpqPath_BloomNode *old, unsigned depth,
    const LG_RpqPath_BloomChange *changes, size_t count,
    const LG_RpqPath_BloomNode **result, char *msg)
{
    *result = old ;
    if (count == 0) return GrB_SUCCESS ;
    LG_RpqPath_BloomNode value = { 0 } ;
    if (depth == 0)
    {
        uint64_t before = old == NULL ? 0 : old->data.word ;
        value.data.word = before | changes[0].bits ;
        if (value.data.word == before) return GrB_SUCCESS ;
    }
    else
    {
        size_t split = 0 ;
        while (split < count && ((changes[split].word >> (depth - 1)) & 1) == 0) split++ ;
        const LG_RpqPath_BloomNode *left = old == NULL ? NULL : old->data.child[0] ;
        const LG_RpqPath_BloomNode *right = old == NULL ? NULL : old->data.child[1] ;
        int info = LG_RpqPath_BloomUpdate (pool, left, depth - 1, changes, split,
            &value.data.child[0], msg) ;
        if (info != GrB_SUCCESS) return info ;
        info = LG_RpqPath_BloomUpdate (pool, right, depth - 1, changes + split,
            count - split, &value.data.child[1], msg) ;
        if (info != GrB_SUCCESS) return info ;
        if (value.data.child[0] == left && value.data.child[1] == right) return GrB_SUCCESS ;
    }
    LG_RpqPath_BloomNode *node = NULL ;
    int info = LG_RpqPath_BloomNodeNew (pool, &node, msg) ;
    if (info != GrB_SUCCESS) return info ;
    *node = value ; *result = node ; return GrB_SUCCESS ;
}
static int LG_RpqPath_BloomExtend (const LG_RpqPath_BloomShape *shape,
    LG_RpqPath_BloomNodes **pool, const LG_RpqPath_BloomNode *old,
    uint64_t hash, const LG_RpqPath_BloomNode **result, char *msg)
{
    LG_RpqPath_BloomChange changes[64] ;
    uint64_t stride = LG_RpqPath_BloomStride (hash) ;
    for (size_t k = 0 ; k < shape->hashes ; k++)
    {
        size_t bit = LG_RpqPath_BloomPosition (shape, hash, stride, k) ;
        changes[k] = (LG_RpqPath_BloomChange) { bit / 64, UINT64_C (1) << (bit % 64) } ;
    }
    qsort (changes, shape->hashes, sizeof (*changes), LG_RpqPath_BloomChangeOrder) ;
    size_t count = 0 ;
    for (size_t k = 0 ; k < shape->hashes ; k++)
        if (count != 0 && changes[count-1].word == changes[k].word) changes[count-1].bits |= changes[k].bits ;
        else changes[count++] = changes[k] ;
    return LG_RpqPath_BloomUpdate (pool, old, shape->depth, changes, count, result, msg) ;
}
static void LG_RpqPath_BloomNodesFree (LG_RpqPath_BloomNodes **pool)
{
    while (*pool != NULL)
    {
        LG_RpqPath_BloomNodes *next = (*pool)->next ;
        LAGraph_Free ((void **) pool, NULL) ; *pool = next ;
    }
}
#endif

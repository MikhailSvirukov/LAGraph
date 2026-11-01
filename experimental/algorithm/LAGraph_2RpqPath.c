//------------------------------------------------------------------------------
// LAGraph_2RpqPath.c: regular path enumeration through predecessor matrices
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause
//
// Unlike the path semiring in RPQ_paths_LA, the planned traversal keeps a
// Boolean frontier M.  For each label a it computes
//
//   H[p,j] = { q : N_a[q,p] && M[q,j] },
//   C[p,i] = { (q,j,a) : q belongs to H[p,j] && G_a[j,i] }.
//
// P retains predecessor records, including their labels.  Only cells receiving
// new records (C \ P, evaluated before updating P) enter the next frontier.
// There is no visited mask: alternative predecessors and cycles must survive
// in P.  Path semantics are checked later, during backward reconstruction.
//
// P is shared by all four semantics; restrictions apply during reconstruction.
// All owned matrices are local variables in LG_RpqPath_Traverse.
// Public query wrappers own the internal workspace for one query.
// Optimizations, including minor ones, require the user's prior approval.

// The input helpers own no memory; workspace cleanup is enabled before Init.
#define LG_FREE_WORK ;
#define LG_FREE_ALL LG_FREE_WORK

#include "LG_internal.h"
#include "LAGraphX.h"
#include <stdatomic.h>

// Set to 0 for builds whose callers supply already validated inputs.
// Allocation and GraphBLAS operation errors are still handled in those builds.
#ifndef LG_RPQ_PATH_VALIDATE_INPUT
#define LG_RPQ_PATH_VALIDATE_INPUT 1
#endif

// Maximum reconstructed path length, in edges, including for all-paths queries
// whose result could otherwise be infinite.  This does not limit the matrix
// traversal, which terminates when P stops receiving new predecessor records.
#ifndef LG_RPQ_PATH_MAX_LENGTH
#define LG_RPQ_PATH_MAX_LENGTH 1024
#endif
#if LG_RPQ_PATH_MAX_LENGTH < 0
#error "LG_RPQ_PATH_MAX_LENGTH must be nonnegative"
#endif

// Working reconstruction-buffer capacity, measured in vertex/label integers.
// Grow geometrically when the next predecessor does not fit the current buffer.
#ifndef LG_RPQ_PATH_INITIAL_CAPACITY
#define LG_RPQ_PATH_INITIAL_CAPACITY 2
#endif
#ifndef LG_RPQ_PATH_GROWTH_FACTOR
#define LG_RPQ_PATH_GROWTH_FACTOR 2
#endif
#if LG_RPQ_PATH_INITIAL_CAPACITY < 1
#error "LG_RPQ_PATH_INITIAL_CAPACITY must be positive"
#endif
#if LG_RPQ_PATH_GROWTH_FACTOR < 2
#error "LG_RPQ_PATH_GROWTH_FACTOR must be at least 2"
#endif

// Number of predecessor records in one temporary block.  This is a baseline
// layout constant, not a tuned value; changing it requires user approval.
#ifndef LG_RPQ_PATH_BLOCK_CAPACITY
#define LG_RPQ_PATH_BLOCK_CAPACITY 64
#endif
#if LG_RPQ_PATH_BLOCK_CAPACITY < 1
#error "LG_RPQ_PATH_BLOCK_CAPACITY must be positive"
#endif

// Fixed number of blocks allocated before matrix operations start.  The pool
// never grows inside a callback.  This baseline limit includes intermediate
// values, not just the predecessor sets that survive in the final C matrix.
#ifndef LG_RPQ_PATH_POOL_BLOCKS
#define LG_RPQ_PATH_POOL_BLOCKS 1024
#endif
#if LG_RPQ_PATH_POOL_BLOCKS < 1
#error "LG_RPQ_PATH_POOL_BLOCKS must be positive"
#endif

// One incoming product-graph edge.  Its destination is given by the P/C cell
// indices; these fields identify the predecessor configuration and edge label.
typedef struct
{
    GrB_Index state ;               // predecessor NFA state q
    GrB_Index vertex ;              // predecessor graph vertex j
    size_t label ;                  // traversed label a
}
LG_RpqPath_Predecessor ;

// H values reserve room for all nr state indices.  The GraphBLAS type size is
// fixed for one query: sizeof this header plus nr * sizeof (GrB_Index).
// Only the first count entries belong to the set; count == 0 means empty.
// capacity is nr, carried with every value so the addition callback can write
// the entire fixed-size result without global query state.  State indices are
// stored in ascending order and unused slots are zero, giving union a canonical
// representation independent of GraphBLAS reduction order.
typedef struct
{
    size_t count ;
    size_t capacity ;
    GrB_Index states [] ;
}
LG_RpqPath_StateSet ;

/**
 * @brief Add two H values by taking the union of their state sets.
 *
 * @param[out] z GraphBLAS output buffer for one StateSet value, including its
 *     capacity state slots.  May alias x or y; no output bytes are read before
 *     they have been written or copied from a valid input.
 * @param[in] x First StateSet value with sorted, distinct indices.
 * @param[in] y Second StateSet value with sorted, distinct indices and the
 *     same capacity as x.  Both inputs belong to the same query-specific type.
 *
 * The result contains sorted, distinct indices.  No allocation is performed:
 * all states belong to [0, capacity), so the union fits the reserved slots.
 * Merging and moving the result take O(x->count + y->count); clearing unused
 * slots additionally takes O(capacity - result->count).
 * This callback has the exact signature required by GrB_BinaryOp_new.
 */
static void LG_RpqPath_UnionStates (void *z, const void *x, const void *y)
{
    LG_RpqPath_StateSet *result = z ;
    const LG_RpqPath_StateSet *left = x ;
    const LG_RpqPath_StateSet *right = y ;

    size_t i = left->count ;
    size_t j = right->count ;
    size_t capacity = left->capacity ;
    size_t output = capacity ;

    // Merge the largest remaining indices into the end of the output buffer.
    // Since the union fits capacity slots, each write is past all unread
    // indices in either input, including when result aliases left or right.
    while (i > 0 || j > 0)
    {
        GrB_Index q ;
        if (j == 0 || (i > 0 && left->states[i-1] > right->states[j-1]))
        {
            q = left->states[--i] ;
        }
        else if (i == 0 || right->states[j-1] > left->states[i-1])
        {
            q = right->states[--j] ;
        }
        else
        {
            // Equal indices occur once in the union; consume both inputs.
            q = left->states[--i] ;
            j-- ;
        }
        result->states[--output] = q ;
    }

    // The merged suffix is already ascending.  Move it to the beginning and
    // restore the same canonical representation used by the singleton product.
    size_t count = capacity - output ;
    memmove (result->states, result->states + output,
        count * sizeof (GrB_Index)) ;
    result->count = count ;
    result->capacity = capacity ;
    memset (result->states + result->count, 0,
        (capacity - result->count) * sizeof (GrB_Index)) ;
}

/**
 * @brief Multiply Boolean entries into a singleton predecessor-state set.
 *
 * @param[out] z GraphBLAS buffer for one StateSet value with nr reserved slots.
 * @param[in] x Boolean entry of the NFA matrix in its selected direction.
 * @param[in] ix Row index of x in the multiplication; unused.
 * @param[in] jx Column index of x in the multiplication; unused.
 * @param[in] y Boolean entry of the unchanged frontier.
 * @param[in] iy Row index of y, the predecessor NFA state q to record.
 * @param[in] jy Column index of y, the graph vertex; unused in this product.
 * @param[in] theta Bound GrB_UINT64 scalar containing nr, the set capacity.
 *
 * Returns {iy} when both Boolean entries are true, otherwise the empty set.
 * Using the frontier's row identifies q for either N^T x M or N x M.
 * This callback uses the exact GxB_index_binary_function signature.
 */
static void LG_RpqPath_CollectState
(
    void *z,
    const void *x,
    GrB_Index ix,
    GrB_Index jx,
    const void *y,
    GrB_Index iy,
    GrB_Index jy,
    const void *theta
)
{
    (void) ix ;
    (void) jx ;
    (void) jy ;
    bool active = (*(const bool *) x && *(const bool *) y) ;
    size_t capacity = (size_t) *(const uint64_t *) theta ;
    LG_RpqPath_StateSet *result = z ;
    memset (result, 0,
        sizeof (LG_RpqPath_StateSet) + capacity * sizeof (GrB_Index)) ;
    result->capacity = capacity ;
    if (active)
    {
        result->count = 1 ;
        result->states[0] = iy ;
    }
}

// next links blocks of one value.  Every block is a fixed-size slice of the
// pool's single allocation and remains at the same address until pool teardown.
typedef struct LG_RpqPath_PredecessorBlock
{
    size_t count ;
    LG_RpqPath_Predecessor records [LG_RPQ_PATH_BLOCK_CAPACITY] ;
    struct LG_RpqPath_PredecessorBlock *next ;
}
LG_RpqPath_PredecessorBlock ;

// One contiguous allocation serves the whole traversal.  Each callback reserves
// a distinct index with atomic_fetch_add; blocks never move and the pool never
// grows.  Resetting the index reclaims the whole iteration, including blocks
// whose intermediate UDT handles GraphBLAS has overwritten.  error reports
// exhaustion from callbacks, whose void return type cannot return an error code.
typedef struct
{
    LG_RpqPath_PredecessorBlock *blocks ;
    size_t block_count ;
    atomic_size_t next_block ;
    atomic_int error ;
}
LG_RpqPath_BlockPool ;

// GraphBLAS copies this handle by value, not the blocks it references.  A
// published set must remain immutable: a copied UDT may still share its head.
// Records are distinct and sorted lexicographically by (state, vertex, label)
// across the whole chain, including block boundaries.
typedef struct
{
    LG_RpqPath_BlockPool *pool ;     // borrowed owner; alive for the traversal
    LG_RpqPath_PredecessorBlock *head ;  // NULL denotes an empty temporary set
}
LG_RpqPath_TemporarySet ;

/**
 * @brief Allocate one contiguous array of blocks before matrix operations.
 *
 * @param[in,out] pool Empty pool with initialized next_block and error atomics.
 *     Receives the array pointer and its capacity; no callbacks may run yet.
 * @param[in] block_count Number of blocks to allocate for the whole traversal.
 *     The same array is reused after the index is reset between iterations.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.
 * @return GrB_SUCCESS on success or an allocation error.  The allocation
 *     wrapper checks block_count * sizeof(block) for overflow.  On failure,
 *     the pool remains empty and can be safely destroyed.
 */
static int LG_RpqPath_PoolInit
(
    LG_RpqPath_BlockPool *pool,
    size_t block_count,
    char *msg
)
{
    int info = LAGraph_Malloc ((void **) &pool->blocks, block_count,
        sizeof (LG_RpqPath_PredecessorBlock), msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    pool->block_count = block_count ;
    atomic_store (&pool->next_block, 0) ;
    atomic_store (&pool->error, GrB_SUCCESS) ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Obtain an empty block from the fixed pool without allocating memory.
 *
 * @param[in,out] pool Non-NULL initialized traversal pool.  A unique index is
 *     reserved atomically.  Exhaustion sets error to GrB_OUT_OF_MEMORY;
 *     no malloc/realloc or explicit waiting loop is used.
 * @return A block with count=0 and next=NULL, or NULL on pool exhaustion.
 *     The pool retains ownership of the array containing this block.
 *
 * No individual block is returned while GraphBLAS may retain a copied handle.
 * PoolReset reclaims all slices together after the iteration completes.
 */
static LG_RpqPath_PredecessorBlock *LG_RpqPath_PoolAcquire
(
    LG_RpqPath_BlockPool *pool
)
{
    // Once an allocation failed, stop issuing further tickets.  Already
    // running callbacks still own their distinct reserved slices until reset.
    if (atomic_load (&pool->error) != GrB_SUCCESS) return (NULL) ;
    size_t index = atomic_fetch_add (&pool->next_block, 1) ;
    if (index >= pool->block_count)
    {
        atomic_store (&pool->error, GrB_OUT_OF_MEMORY) ;
        return (NULL) ;
    }
    // &blocks[index] is base + index * sizeof(block), with no new allocation.
    LG_RpqPath_PredecessorBlock *block = &pool->blocks[index] ;
    block->count = 0 ;
    block->next = NULL ;
    return (block) ;
}

/**
 * @brief Append one predecessor while constructing a private temporary value.
 *
 * @param[in,out] set Non-NULL unpublished set with an initialized pool pointer.
 *     head may be NULL.  Its chain must not be shared with other values or
 *     modified by another thread; only block-index reservation is atomic.
 * @param[in,out] tail Address of the construction's local last-block pointer.
 *     Start with NULL for an empty set; preserve it between append calls.
 *     The pointer is updated only when a new block is successfully attached.
 * @param[in] record Non-NULL predecessor record, copied into the last block.
 *     The caller supplies records in strictly increasing lexicographic order.
 * @return true on success; false if no free block remains in the pool.
 *     Previously appended records stay valid on failure, and set->pool->error
 *     contains GrB_OUT_OF_MEMORY for the caller to inspect after GraphBLAS
 *     finishes.  Partial values use slices of the same array and are reclaimed
 *     together with the rest of the iteration.
 */
static bool LG_RpqPath_TemporaryAppend
(
    LG_RpqPath_TemporarySet *set,
    LG_RpqPath_PredecessorBlock **tail,
    const LG_RpqPath_Predecessor *record
)
{
    LG_RpqPath_PredecessorBlock *block = *tail ;
    if (block == NULL || block->count == LG_RPQ_PATH_BLOCK_CAPACITY)
    {
        LG_RpqPath_PredecessorBlock *next =
            LG_RpqPath_PoolAcquire (set->pool) ;
        if (next == NULL) return (false) ;
        if (block == NULL)
        {
            set->head = next ;
        }
        else
        {
            block->next = next ;
        }
        block = next ;
        *tail = block ;
    }
    block->records[block->count] = *record ;
    block->count++ ;
    return (true) ;
}

/**
 * @brief Compare predecessor records in the order used by temporary sets.
 *
 * @param[in] left Non-NULL first record.
 * @param[in] right Non-NULL second record.
 * @return -1, 0 or 1 when left is less than, equal to or greater than right
 *     lexicographically by state, then vertex, then label.
 */
static int LG_RpqPath_ComparePredecessors
(
    const LG_RpqPath_Predecessor *left,
    const LG_RpqPath_Predecessor *right
)
{
    if (left->state < right->state) return (-1) ;
    if (left->state > right->state) return (1) ;
    if (left->vertex < right->vertex) return (-1) ;
    if (left->vertex > right->vertex) return (1) ;
    if (left->label < right->label) return (-1) ;
    if (left->label > right->label) return (1) ;
    return (0) ;
}

/**
 * @brief Advance one input cursor across a temporary set's block chain.
 *
 * @param[in,out] block Address of the current non-NULL immutable block pointer.
 *     Becomes the next block, or NULL at the end of the set, when exhausted.
 * @param[in,out] index Index of a valid current record.  Incremented within
 *     the block and reset to zero when advancing to the next block.
 */
static void LG_RpqPath_TemporaryAdvance
(
    const LG_RpqPath_PredecessorBlock **block,
    size_t *index
)
{
    (*index)++ ;
    if (*index == (*block)->count)
    {
        *block = (*block)->next ;
        *index = 0 ;
    }
}

/**
 * @brief Union two temporary predecessor sets without changing their blocks.
 *
 * @param[out] z GraphBLAS output buffer for TemporarySet.  May alias x or y;
 *     input handles are captured before the result handle is overwritten.
 * @param[in] x Immutable sorted first set, including the empty monoid identity.
 * @param[in] y Immutable sorted second set belonging to the same pool as x.
 *
 * Two cursors merge records in O(|x| + |y|), including traversal across blocks.
 * Equal records are emitted once and advance both cursors.  A local output
 * tail allows appending without rescanning the result chain.
 * Every output record is copied into a new private chain.  Shallow-copied UDT
 * handles therefore never observe mutations of an input chain.  Exhaustion
 * produces an empty handle and sets the pool error; the outer traversal must
 * discard the failed operation's result after waiting for its completion.
 */
static void LG_RpqPath_UnionPredecessors (void *z, const void *x, const void *y)
{
    LG_RpqPath_TemporarySet left = *(const LG_RpqPath_TemporarySet *) x ;
    LG_RpqPath_TemporarySet right = *(const LG_RpqPath_TemporarySet *) y ;
    LG_RpqPath_TemporarySet result = { .pool = left.pool, .head = NULL } ;
    LG_RpqPath_PredecessorBlock *tail = NULL ;
    const LG_RpqPath_PredecessorBlock *left_block = left.head ;
    const LG_RpqPath_PredecessorBlock *right_block = right.head ;
    size_t left_index = 0, right_index = 0 ;

    if (atomic_load (&result.pool->error) == GrB_SUCCESS)
    {
        while (left_block != NULL || right_block != NULL)
        {
            const LG_RpqPath_Predecessor *record ;
            if (left_block == NULL)
            {
                record = &right_block->records[right_index] ;
                LG_RpqPath_TemporaryAdvance (&right_block, &right_index) ;
            }
            else if (right_block == NULL)
            {
                record = &left_block->records[left_index] ;
                LG_RpqPath_TemporaryAdvance (&left_block, &left_index) ;
            }
            else
            {
                const LG_RpqPath_Predecessor *left_record =
                    &left_block->records[left_index] ;
                const LG_RpqPath_Predecessor *right_record =
                    &right_block->records[right_index] ;
                int order = LG_RpqPath_ComparePredecessors (
                    left_record, right_record) ;
                record = (order <= 0) ? left_record : right_record ;
                if (order <= 0)
                {
                    LG_RpqPath_TemporaryAdvance (&left_block, &left_index) ;
                }
                if (order >= 0)
                {
                    LG_RpqPath_TemporaryAdvance (&right_block, &right_index) ;
                }
            }
            if (!LG_RpqPath_TemporaryAppend (&result, &tail, record))
            {
                // Partial output remains in the arena until iteration reset.
                result.head = NULL ;
                break ;
            }
        }
    }
    *(LG_RpqPath_TemporarySet *) z = result ;
}

// The scalar bound to the indexed product carries the current label and a
// borrowed arena pointer.  Binding copies the scalar value, including this
// pointer; the arena remains alive until all operators and matrices are freed.
typedef struct
{
    LG_RpqPath_BlockPool *pool ;
    size_t label ;
}
LG_RpqPath_PredecessorContext ;

/**
 * @brief Extend an H state set into predecessor records for a graph edge.
 *
 * @param[out] z GraphBLAS output buffer for a TemporarySet handle.
 * @param[in] x StateSet value H[p,j], containing distinct predecessor states q.
 * @param[in] ix Row p of H; unused because C's row already records this state.
 * @param[in] jx Column j of H, the predecessor graph vertex to record.
 * @param[in] y Boolean graph adjacency value in the chosen traversal direction.
 * @param[in] iy Row of the graph operand; unused because jx identifies j.
 * @param[in] jy Destination graph vertex; unused because C's column records it.
 * @param[in] theta Bound PredecessorContext containing the pool and label a.
 *
 * Produces {(q,jx,a) | q belongs to x} when y is true; otherwise the empty
 * set.  H already contains increasing q; jx and a are fixed for this call,
 * so the emitted records are sorted without a separate sorting pass.
 * Newly acquired blocks are private until the result handle is written.
 * A failed allocation records GrB_OUT_OF_MEMORY in the pool and returns an
 * empty handle; the caller checks the flag after GrB_Matrix_wait on C.
 */
static void LG_RpqPath_CollectPredecessors
(
    void *z,
    const void *x,
    GrB_Index ix,
    GrB_Index jx,
    const void *y,
    GrB_Index iy,
    GrB_Index jy,
    const void *theta
)
{
    (void) ix ;
    (void) iy ;
    (void) jy ;
    const LG_RpqPath_StateSet *states = x ;
    const LG_RpqPath_PredecessorContext *context = theta ;
    LG_RpqPath_TemporarySet result = { .pool = context->pool, .head = NULL } ;
    LG_RpqPath_PredecessorBlock *tail = NULL ;

    if (*(const bool *) y &&
        atomic_load (&context->pool->error) == GrB_SUCCESS)
    {
        for (size_t k = 0 ; k < states->count ; k++)
        {
            LG_RpqPath_Predecessor record =
            {
                .state = states->states[k],
                .vertex = jx,
                .label = context->label
            } ;
            if (!LG_RpqPath_TemporaryAppend (&result, &tail, &record))
            {
                result.head = NULL ;
                break ;
            }
        }
    }
    *(LG_RpqPath_TemporarySet *) z = result ;
}

/**
 * @brief Reclaim all block slices by resetting the next-allocation index.
 *
 * @param[in,out] pool Non-NULL initialized pool.  next_block becomes zero and
 *     the callback error flag is cleared.  The backing allocation is retained.
 * @pre All operations using these blocks have completed, P has received deep
 *     copies of the needed records, and all temporary handles are discarded.
 *     Read pool->error before calling this function if callbacks were used.
 *
 * No block traversal is needed.  Acquire initializes each block's header when
 * it is issued again; old record bytes are ignored beyond the new count.
 */
static void LG_RpqPath_PoolReset (LG_RpqPath_BlockPool *pool)
{
    atomic_store (&pool->next_block, 0) ;
    atomic_store (&pool->error, GrB_SUCCESS) ;
}

/**
 * @brief Free all memory owned by a traversal's pool.
 *
 * @param[in,out] pool Non-NULL initialized pool.  The backing array is freed,
 *     its pointer and capacity are cleared.  May be called again when empty.
 * @pre No callbacks are active and no surviving value references these blocks.
 *     Safe after failed pool initialization as well as a failed traversal.
 */
static void LG_RpqPath_PoolDestroy (LG_RpqPath_BlockPool *pool)
{
    LAGraph_Free ((void **) &pool->blocks, NULL) ;
    pool->block_count = 0 ;
    LG_RpqPath_PoolReset (pool) ;
}

// Each P buffer is one allocation containing its ownership link and records.
// Old and new P buffers are tracked separately during an in-place eWiseUnion.
// GraphBLAS only copies their handles and does not manage the pointed-to memory.
typedef struct LG_RpqPath_StoredAllocation
{
    struct LG_RpqPath_StoredAllocation *next ;
    LG_RpqPath_Predecessor records [] ;
}
LG_RpqPath_StoredAllocation ;

// P values refer to ordinary heap allocations, never to the temporary arena.
// count records are valid and sorted by (state, vertex, label).
typedef struct
{
    size_t count ;
    LG_RpqPath_StoredAllocation *allocation ; // NULL denotes the empty set
}
LG_RpqPath_StoredSet ;

// Callbacks may allocate concurrently.  They only prepend to this owner list;
// nothing is removed or freed until all callbacks have completed.  This is
// independent of the unchanged fixed-block pool used by temporary C values.
typedef struct
{
    _Atomic (LG_RpqPath_StoredAllocation *) allocations ;
    atomic_int error ;
}
LG_RpqPath_StoredOwner ;

// Bound scalar for P's mixed-type binary operator; indices are not needed.
typedef struct
{
    LG_RpqPath_StoredOwner *owner ;
}
LG_RpqPath_StoredContext ;

/**
 * @brief Determine whether a C value contains a record absent from the old P.
 *
 * @param[out] z Output bool for GxB_eWiseUnion; true iff x adds a predecessor.
 * @param[in] x Sorted TemporarySet from C, or its empty substitute scalar.
 * @param[in] y Sorted StoredSet from P, or its empty substitute scalar.
 *
 * Both operands are read-only.  Missing and explicitly empty cells have the
 * same set semantics.  C-only positions compare against empty P and P-only
 * positions compare against empty C.  No allocation or mutation is performed.
 */
static void LG_RpqPath_HasNewPredecessors (void *z, const void *x, const void *y)
{
    const LG_RpqPath_TemporarySet *temporary = x ;
    const LG_RpqPath_StoredSet *stored = y ;
    const LG_RpqPath_PredecessorBlock *block = temporary->head ;
    size_t temporary_index = 0, stored_index = 0 ;

    while (block != NULL)
    {
        if (stored_index == stored->count)
        {
            *(bool *) z = true ;
            return ;
        }
        int order = LG_RpqPath_ComparePredecessors (
            &block->records[temporary_index],
            &stored->allocation->records[stored_index]) ;
        if (order < 0)
        {
            *(bool *) z = true ;
            return ;
        }
        if (order == 0)
        {
            LG_RpqPath_TemporaryAdvance (&block, &temporary_index) ;
        }
        stored_index++ ;
    }
    *(bool *) z = false ;
}

/**
 * @brief Allocate an independent P record buffer and register its owner.
 *
 * @param[in,out] owner Non-NULL owner of the new P buffers.  Concurrent
 *     registrations are allowed; removal is deferred until callbacks finish.
 * @param[in] capacity Number of record slots to allocate in the new buffer.
 * @param[out] result Non-NULL output initialized to an empty StoredSet.  On
 *     success it references the registered allocation, with count still zero.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or an allocation error.  Registration happens before
 *     the handle can be given to GraphBLAS, so error cleanup never needs to
 *     discover ownership by reading a potentially failed output matrix.
 */
static int LG_RpqPath_StoredAllocate
(
    LG_RpqPath_StoredOwner *owner,
    size_t capacity,
    LG_RpqPath_StoredSet *result,
    char *msg
)
{
    result->count = 0 ;
    result->allocation = NULL ;
    if (capacity > (SIZE_MAX - sizeof (LG_RpqPath_StoredAllocation)) /
        sizeof (LG_RpqPath_Predecessor))
    {
        LG_ERROR_MSG ("stored predecessor set size exceeds addressable memory") ;
        return (GrB_OUT_OF_MEMORY) ;
    }
    size_t bytes = sizeof (LG_RpqPath_StoredAllocation) +
        capacity * sizeof (LG_RpqPath_Predecessor) ;
    LG_RpqPath_StoredAllocation *allocation = NULL ;
    int info = LAGraph_Malloc ((void **) &allocation, 1, bytes, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    // Only the new private node's link changes on a retry.  Existing nodes
    // remain immutable, and none can be freed while registration is active.
    LG_RpqPath_StoredAllocation *head = atomic_load (&owner->allocations) ;
    do
    {
        allocation->next = head ;
    }
    while (!atomic_compare_exchange_weak (&owner->allocations, &head,
        allocation)) ;
    result->allocation = allocation ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Free all P buffers registered with an owner.
 *
 * @param[in,out] owner Non-NULL initialized owner.  Its list is cleared and
 *     error flag reset; calling again on an empty owner is safe.
 * @pre No callback is registering buffers, and no surviving matrix value or
 *     pending operation uses them.  Wait for P before releasing its old owner.
 */
static void LG_RpqPath_StoredRelease (LG_RpqPath_StoredOwner *owner)
{
    LG_RpqPath_StoredAllocation *allocation =
        atomic_exchange (&owner->allocations, NULL) ;
    while (allocation != NULL)
    {
        LG_RpqPath_StoredAllocation *next = allocation->next ;
        LAGraph_Free ((void **) &allocation, NULL) ;
        allocation = next ;
    }
    atomic_store (&owner->error, GrB_SUCCESS) ;
}

/**
 * @brief Deep-copy a stored set and a temporary set into their sorted union.
 *
 * @param[in] stored Immutable old P value; an empty value has count=0.
 * @param[in] temporary Immutable C value, with sorted distinct records.
 * @param[in,out] owner Non-NULL owner registering all new P buffers.
 * @param[out] result Receives a newly allocated union with no arena references
 *     and no shared record storage with stored.  All equal records occur once.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or GrB_OUT_OF_MEMORY.  Inputs remain unchanged on failure.
 *     The result allocation, once created, belongs to owner until freed.
 */
static int LG_RpqPath_MergeStoredSet
(
    const LG_RpqPath_StoredSet *stored,
    const LG_RpqPath_TemporarySet *temporary,
    LG_RpqPath_StoredOwner *owner,
    LG_RpqPath_StoredSet *result,
    char *msg
)
{
    // Determine the allocation bound without relying on a fixed set capacity.
    // Duplicate removal during merging may leave unused slots in this buffer.
    size_t capacity = stored->count ;
    for (const LG_RpqPath_PredecessorBlock *block = temporary->head ;
         block != NULL ; block = block->next)
    {
        if (block->count > SIZE_MAX - capacity)
        {
            LG_ERROR_MSG ("stored predecessor count exceeds addressable memory") ;
            return (GrB_OUT_OF_MEMORY) ;
        }
        capacity += block->count ;
    }
    int info = LG_RpqPath_StoredAllocate (owner, capacity, result, msg) ;
    if (info != GrB_SUCCESS) return (info) ;

    const LG_RpqPath_PredecessorBlock *block = temporary->head ;
    size_t temporary_index = 0, stored_index = 0 ;
    while (block != NULL || stored_index < stored->count)
    {
        const LG_RpqPath_Predecessor *record ;
        if (block == NULL)
        {
            record = &stored->allocation->records[stored_index++] ;
        }
        else if (stored_index == stored->count)
        {
            record = &block->records[temporary_index] ;
            LG_RpqPath_TemporaryAdvance (&block, &temporary_index) ;
        }
        else
        {
            const LG_RpqPath_Predecessor *temporary_record =
                &block->records[temporary_index] ;
            const LG_RpqPath_Predecessor *stored_record =
                &stored->allocation->records[stored_index] ;
            int order = LG_RpqPath_ComparePredecessors (
                temporary_record, stored_record) ;
            record = (order <= 0) ? temporary_record : stored_record ;
            if (order <= 0)
            {
                LG_RpqPath_TemporaryAdvance (&block, &temporary_index) ;
            }
            if (order >= 0) stored_index++ ;
        }
        result->allocation->records[result->count++] = *record ;
    }
    return (GrB_SUCCESS) ;
}

/**
 * @brief Produce a deep-copied P value from a C value and the old P value.
 *
 * @param[out] z StoredSet result, with an independent sorted record buffer.
 * @param[in] x TemporarySet from C, or the empty substitute scalar.
 * @param[in] ix Row of x; unused because records contain all required fields.
 * @param[in] jx Column of x; unused.
 * @param[in] y StoredSet from the old P, or the empty substitute scalar.
 * @param[in] iy Row of y; unused.
 * @param[in] jy Column of y; unused.
 * @param[in] theta Non-NULL bound StoredContext with the new buffers' owner.
 *
 * Used by eWiseUnion at every position of C union P, including P-only cells.
 * All records are copied by value; neither input buffer is modified or freed.
 * Input handles are captured before writing z, which may alias an input.
 * On failure the result is empty and the owner's error flag is set.  After
 * waiting for P, the caller checks that flag before accepting the new P.
 */
static void LG_RpqPath_MergePredecessors
(
    void *z,
    const void *x,
    GrB_Index ix,
    GrB_Index jx,
    const void *y,
    GrB_Index iy,
    GrB_Index jy,
    const void *theta
)
{
    (void) ix ;
    (void) jx ;
    (void) iy ;
    (void) jy ;
    LG_RpqPath_TemporarySet temporary =
        *(const LG_RpqPath_TemporarySet *) x ;
    LG_RpqPath_StoredSet stored = *(const LG_RpqPath_StoredSet *) y ;
    const LG_RpqPath_StoredContext *context = theta ;
    LG_RpqPath_StoredSet result = { .count = 0, .allocation = NULL } ;

    if (atomic_load (&context->owner->error) == GrB_SUCCESS)
    {
        int info = LG_RpqPath_MergeStoredSet (&stored, &temporary,
            context->owner, &result, NULL) ;
        if (info != GrB_SUCCESS)
        {
            int expected = GrB_SUCCESS ;
            atomic_compare_exchange_strong (&context->owner->error,
                &expected, info) ;
            result = (LG_RpqPath_StoredSet) { .count = 0, .allocation = NULL } ;
        }
    }
    *(LG_RpqPath_StoredSet *) z = result ;
}

// One graph path, independent of the accepting run of the NFA.  length counts
// edges; elements owns exactly 2 * length + 1 integers in traversal order:
// vertex, label, vertex, ..., label, vertex.  A zero-edge path owns one vertex.
// The result has no pointers into P, roots, the temporary pool or DFS storage.
typedef LAGraph_RpqPath LG_RpqPath_Path ;

/**
 * @brief Release a returned path array and all its independently owned paths.
 *
 * @param[in,out] paths Address of an owned array of path_count entries.  Each
 *     element buffer and the array itself are freed, and *paths becomes NULL.
 *     A NULL address or an already NULL array is accepted.
 * @param[in] path_count Number of initialized entries in *paths.  Ignored if
 *     paths or *paths is NULL; the caller's count variable is not modified.
 */
static void LG_RpqPath_FreePaths
(
    LG_RpqPath_Path **paths,
    size_t path_count
)
{
    if (paths == NULL || *paths == NULL) return ;
    for (size_t k = 0 ; k < path_count ; k++)
    {
        LAGraph_Free ((void **) &(*paths)[k].elements, NULL) ;
    }
    LAGraph_Free ((void **) paths, NULL) ;
}

// Only reconstruction owns these buffers.  The recursive calls share the
// working prefix, while completed results own separate forward-order copies.
// No matrix handles, cached cells or memoized suffixes are stored here.
typedef struct
{
    LG_RpqPath_Path *paths ;
    size_t count ;
    uint64_t *reverse_path ;         // target, label, predecessor, ..., source
    size_t capacity ;                // allocated integer slots in reverse_path
}
LG_RpqPath_Reconstruction ;

/**
 * @brief Reserve a working prefix for a backward path of the requested length.
 *
 * @param[in,out] reconstruction Non-NULL reconstruction state.  Its working
 *     buffer may move; callers must access it through this state after a call.
 *     Existing prefix elements remain intact.  Results are not modified.
 * @param[in] length Required path length in edges; the endpoint adds one slot.
 *     Storage is reserved for 2 * length + 1 integer slots.  Zero is allowed.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or an allocation error.  The old buffer is retained on
 *     failure.  Capacity starts at LG_RPQ_PATH_INITIAL_CAPACITY integer slots
 *     and grows by LG_RPQ_PATH_GROWTH_FACTOR until the prefix fits.
 */
static int LG_RpqPath_ReservePath
(
    LG_RpqPath_Reconstruction *reconstruction,
    size_t length,
    char *msg
)
{
    if (length > (SIZE_MAX - 1) / 2)
    {
        LG_ERROR_MSG ("reconstructed path length exceeds addressable memory") ;
        return (GrB_OUT_OF_MEMORY) ;
    }
    size_t needed = 2 * length + 1 ;
    if (needed <= reconstruction->capacity) return (GrB_SUCCESS) ;
    size_t capacity = reconstruction->capacity == 0 ?
        LG_RPQ_PATH_INITIAL_CAPACITY : reconstruction->capacity ;
    while (capacity < needed)
    {
        // Near the addressable limit, use the exact request instead of
        // overflowing the geometric capacity or its allocation byte count.
        if (capacity > SIZE_MAX / sizeof (uint64_t) /
            LG_RPQ_PATH_GROWTH_FACTOR)
        {
            capacity = needed ;
            break ;
        }
        capacity *= LG_RPQ_PATH_GROWTH_FACTOR ;
    }
    int info = LAGraph_Realloc ((void **) &reconstruction->reverse_path,
        capacity, reconstruction->capacity, sizeof (uint64_t), msg) ;
    if (info == GrB_SUCCESS) reconstruction->capacity = capacity ;
    return (info) ;
}

/**
 * @brief Save the current backward prefix as a distinct forward graph path.
 *
 * @param[in,out] reconstruction Non-NULL state with a valid reverse_path
 *     prefix of 2 * length + 1 slots.  A new result is appended only if no
 *     existing result has the same vertex/label sequence.  The working prefix
 *     is read-only; each saved result receives its own allocation.
 * @param[in] length Number of edges in the valid working prefix; may be zero.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or an allocation error.  Previously saved paths remain
 *     owned by reconstruction even if allocating the new result fails.
 *
 * Different NFA runs, initial states or accepting states may describe the
 * same graph path.  A direct scan removes these duplicates without a cache or
 * hash table.  Equal endpoints with different labels remain different paths.
 */
static int LG_RpqPath_SavePath
(
    LG_RpqPath_Reconstruction *reconstruction,
    size_t length,
    char *msg
)
{
    size_t slots = 2 * length + 1 ;
    for (size_t k = 0 ; k < reconstruction->count ; k++)
    {
        const LG_RpqPath_Path *path = &reconstruction->paths[k] ;
        if (path->length != length) continue ;
        size_t i = 0 ;
        while (i < slots && path->elements[i] ==
            reconstruction->reverse_path[slots - 1 - i])
        {
            i++ ;
        }
        if (i == slots) return (GrB_SUCCESS) ;
    }

    if (reconstruction->count == SIZE_MAX)
    {
        LG_ERROR_MSG ("reconstructed path count exceeds addressable memory") ;
        return (GrB_OUT_OF_MEMORY) ;
    }
    uint64_t *elements = NULL ;
    int info = LAGraph_Malloc ((void **) &elements, slots,
        sizeof (uint64_t), msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t i = 0 ; i < slots ; i++)
    {
        elements[i] = reconstruction->reverse_path[slots - 1 - i] ;
    }
    info = LAGraph_Realloc ((void **) &reconstruction->paths,
        reconstruction->count + 1, reconstruction->count,
        sizeof (LG_RpqPath_Path), msg) ;
    if (info != GrB_SUCCESS)
    {
        LAGraph_Free ((void **) &elements, NULL) ;
        return (info) ;
    }
    reconstruction->paths[reconstruction->count++] =
        (LG_RpqPath_Path) { .length = length, .elements = elements } ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Follow predecessor records recursively for all paths.
 * @param[in] P Completed immutable predecessor matrix; borrowed.
 * @param[in] roots Immutable Boolean initial-configuration relation; borrowed.
 * @param[in] state Current NFA state, a valid row of P.
 * @param[in] vertex Current graph vertex, a valid column of P.
 * @param[in] length Edge count in the backward prefix; initially zero.
 * @param[in,out] reconstruction Working prefix and owned output paths.  Slots
 *     through 2*length are valid; deeper slots may be overwritten by siblings.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error.  All surviving buffers
 *     remain owned by reconstruction for cleanup, including on failure.
 * @note A root saves a path and permits further descent.  Cycles are bounded
 *     only by LG_RPQ_PATH_MAX_LENGTH; the exact limit is included.
 */
static int LG_RpqPath_ReconstructAllCell
(
    GrB_Matrix P,
    GrB_Matrix roots,
    GrB_Index state,
    GrB_Index vertex,
    size_t length,
    LG_RpqPath_Reconstruction *reconstruction,
    char *msg
)
{
    bool root = false ;
    int info = GrB_Matrix_extractElement_BOOL (&root, roots, state, vertex) ;
    if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
    if (info == GrB_SUCCESS && root)
    {
        info = LG_RpqPath_SavePath (reconstruction, length, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    if (length >= LG_RPQ_PATH_MAX_LENGTH) return (GrB_SUCCESS) ;

    LG_RpqPath_StoredSet predecessors = { .count = 0, .allocation = NULL } ;
    info = GrB_Matrix_extractElement_UDT (&predecessors, P, state, vertex) ;
    if (info == GrB_NO_VALUE) return (GrB_SUCCESS) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < predecessors.count ; k++)
    {
        const LG_RpqPath_Predecessor *predecessor =
            &predecessors.allocation->records[k] ;
        info = LG_RpqPath_ReservePath (reconstruction, length + 1, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        reconstruction->reverse_path[2 * length + 1] = predecessor->label ;
        reconstruction->reverse_path[2 * length + 2] = predecessor->vertex ;
        info = LG_RpqPath_ReconstructAllCell (P, roots,
            predecessor->state, predecessor->vertex, length + 1,
            reconstruction, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    return (GrB_SUCCESS) ;
}

/**
 * @brief Follow predecessor records recursively for simple paths.
 * @param[in] P Completed immutable predecessor matrix; borrowed.
 * @param[in] roots Immutable Boolean initial-configuration relation; borrowed.
 * @param[in] state Current NFA state, a valid row of P.
 * @param[in] vertex Current graph vertex, a valid column of P.
 * @param[in] length Edge count in the backward prefix; initially zero.
 * @param[in,out] reconstruction Working prefix and owned output paths.  Slots
 *     through 2*length are valid; deeper slots may be overwritten by siblings.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error.  All surviving buffers
 *     remain owned by reconstruction for cleanup, including on failure.
 * @note Each candidate vertex is scanned against the existing graph prefix.
 *     This gives O(length^2) repetition checks along a path without a set.
 */
static int LG_RpqPath_ReconstructSimpleCell
(
    GrB_Matrix P,
    GrB_Matrix roots,
    GrB_Index state,
    GrB_Index vertex,
    size_t length,
    LG_RpqPath_Reconstruction *reconstruction,
    char *msg
)
{
    bool root = false ;
    int info = GrB_Matrix_extractElement_BOOL (&root, roots, state, vertex) ;
    if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
    if (info == GrB_SUCCESS && root)
    {
        info = LG_RpqPath_SavePath (reconstruction, length, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    if (length >= LG_RPQ_PATH_MAX_LENGTH) return (GrB_SUCCESS) ;

    LG_RpqPath_StoredSet predecessors = { .count = 0, .allocation = NULL } ;
    info = GrB_Matrix_extractElement_UDT (&predecessors, P, state, vertex) ;
    if (info == GrB_NO_VALUE) return (GrB_SUCCESS) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < predecessors.count ; k++)
    {
        const LG_RpqPath_Predecessor *predecessor =
            &predecessors.allocation->records[k] ;
        bool repeated = false ;
        for (size_t i = 0 ; i <= length ; i++)
        {
            if (reconstruction->reverse_path[2 * i] == predecessor->vertex)
            {
                repeated = true ;
                break ;
            }
        }
        if (repeated) continue ;
        info = LG_RpqPath_ReservePath (reconstruction, length + 1, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        reconstruction->reverse_path[2 * length + 1] = predecessor->label ;
        reconstruction->reverse_path[2 * length + 2] = predecessor->vertex ;
        info = LG_RpqPath_ReconstructSimpleCell (P, roots,
            predecessor->state, predecessor->vertex, length + 1,
            reconstruction, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    return (GrB_SUCCESS) ;
}

/**
 * @brief Follow predecessor records recursively for trails paths.
 * @param[in] P Completed immutable predecessor matrix; borrowed.
 * @param[in] roots Immutable Boolean initial-configuration relation; borrowed.
 * @param[in] state Current NFA state, a valid row of P.
 * @param[in] vertex Current graph vertex, a valid column of P.
 * @param[in] length Edge count in the backward prefix; initially zero.
 * @param[in,out] reconstruction Working prefix and owned output paths.  Slots
 *     through 2*length are valid; deeper slots may be overwritten by siblings.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error.  All surviving buffers
 *     remain owned by reconstruction for cleanup, including on failure.
 * @note Each candidate directed edge (source,label,destination) is scanned
 *     against existing edges.  Vertices may repeat; edge checks along a path
 *     take O(length^2) without a set.
 */
static int LG_RpqPath_ReconstructTrailsCell
(
    GrB_Matrix P,
    GrB_Matrix roots,
    GrB_Index state,
    GrB_Index vertex,
    size_t length,
    LG_RpqPath_Reconstruction *reconstruction,
    char *msg
)
{
    bool root = false ;
    int info = GrB_Matrix_extractElement_BOOL (&root, roots, state, vertex) ;
    if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
    if (info == GrB_SUCCESS && root)
    {
        info = LG_RpqPath_SavePath (reconstruction, length, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    if (length >= LG_RPQ_PATH_MAX_LENGTH) return (GrB_SUCCESS) ;

    LG_RpqPath_StoredSet predecessors = { .count = 0, .allocation = NULL } ;
    info = GrB_Matrix_extractElement_UDT (&predecessors, P, state, vertex) ;
    if (info == GrB_NO_VALUE) return (GrB_SUCCESS) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < predecessors.count ; k++)
    {
        const LG_RpqPath_Predecessor *predecessor =
            &predecessors.allocation->records[k] ;
        bool repeated = false ;
        const uint64_t *path = reconstruction->reverse_path ;
        for (size_t i = 0 ; i < length ; i++)
        {
            // Backward storage: source follows label and destination.
            if (path[2 * i + 2] == predecessor->vertex &&
                path[2 * i + 1] == predecessor->label &&
                path[2 * i] == vertex)
            {
                repeated = true ;
                break ;
            }
        }
        if (repeated) continue ;
        info = LG_RpqPath_ReservePath (reconstruction, length + 1, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        reconstruction->reverse_path[2 * length + 1] = predecessor->label ;
        reconstruction->reverse_path[2 * length + 2] = predecessor->vertex ;
        info = LG_RpqPath_ReconstructTrailsCell (P, roots,
            predecessor->state, predecessor->vertex, length + 1,
            reconstruction, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    return (GrB_SUCCESS) ;
}

/**
 * @brief Follow predecessor records recursively for shortest paths.
 * @param[in] P Completed immutable predecessor matrix; borrowed.
 * @param[in] roots Immutable Boolean initial-configuration relation; borrowed.
 * @param[in] state Current NFA state, a valid row of P.
 * @param[in] vertex Current graph vertex, a valid column of P.
 * @param[in] length Edge count in the backward prefix; initially zero.
 * @param[in,out] reconstruction Working prefix and owned output paths.  Slots
 *     through 2*length are valid; deeper slots may be overwritten by siblings.
 * @param[in] destination_begin First output index for this graph endpoint.
 *     Earlier endpoints' results are preserved when a shorter path is found.
 * @param[in,out] shortest_length Best accepted length for this endpoint across
 *     all roots and accepting states; initially SIZE_MAX.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error.  All surviving buffers
 *     remain owned by reconstruction for cleanup, including on failure.
 * @note Reaching a root updates the endpoint's minimum and retains all ties.
 *     Repeated vertices and edges are allowed when required by the language.
 */
static int LG_RpqPath_ReconstructShortestCell
(
    GrB_Matrix P,
    GrB_Matrix roots,
    GrB_Index state,
    GrB_Index vertex,
    size_t length,
    LG_RpqPath_Reconstruction *reconstruction,
    size_t destination_begin,
    size_t *shortest_length,
    char *msg
)
{
    bool root = false ;
    int info = GrB_Matrix_extractElement_BOOL (&root, roots, state, vertex) ;
    if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
    if (info == GrB_SUCCESS && root)
    {
        if (length < *shortest_length)
        {
            for (size_t k = destination_begin ; k < reconstruction->count ; k++)
            {
                LAGraph_Free ((void **) &reconstruction->paths[k].elements,
                    NULL) ;
            }
            reconstruction->count = destination_begin ;
            *shortest_length = length ;
        }
        if (length == *shortest_length)
        {
            info = LG_RpqPath_SavePath (reconstruction, length, msg) ;
            if (info != GrB_SUCCESS) return (info) ;
        }
    }
    if (length >= LG_RPQ_PATH_MAX_LENGTH) return (GrB_SUCCESS) ;
    if (length >= *shortest_length) return (GrB_SUCCESS) ;

    LG_RpqPath_StoredSet predecessors = { .count = 0, .allocation = NULL } ;
    info = GrB_Matrix_extractElement_UDT (&predecessors, P, state, vertex) ;
    if (info == GrB_NO_VALUE) return (GrB_SUCCESS) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < predecessors.count ; k++)
    {
        const LG_RpqPath_Predecessor *predecessor =
            &predecessors.allocation->records[k] ;
        info = LG_RpqPath_ReservePath (reconstruction, length + 1, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        reconstruction->reverse_path[2 * length + 1] = predecessor->label ;
        reconstruction->reverse_path[2 * length + 2] = predecessor->vertex ;
        info = LG_RpqPath_ReconstructShortestCell (P, roots,
            predecessor->state, predecessor->vertex, length + 1,
            reconstruction, destination_begin, shortest_length, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    return (GrB_SUCCESS) ;
}

// Query selects one complete stage-2 handler.  Each handler below directly
// calls its own recursive function; there is no shared reconstruction driver.
typedef int (*LG_RpqPath_Process)
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    char *msg
) ;

/**
 * @brief Reconstruct all paths from the completed accumulation matrix.
 * @param[out] paths Non-NULL address receiving owned paths, or NULL on error.
 * @param[out] path_count Non-NULL address receiving their count, or zero.
 * @param[in] P Completed predecessor matrix, borrowed and never modified.
 * @param[in] roots Immutable initial-configuration relation, borrowed.
 * @param[in] QF Array of nqf accepting states; NULL allowed when nqf=0.
 * @param[in] nqf Number of accepting states, including duplicates.
 * @param[in] ng Number of graph vertices, equal to ncols(P).
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error, with no partial result.
 */
static int LG_RpqPath_ProcessAll
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { 0 } ;
    int info = GrB_SUCCESS ;
    for (GrB_Index vertex = 0 ; vertex < ng ; vertex++)
    {
        for (size_t k = 0 ; k < nqf ; k++)
        {
            info = LG_RpqPath_ReservePath (&reconstruction, 0, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
            reconstruction.reverse_path[0] = vertex ;
            info = LG_RpqPath_ReconstructAllCell (P, roots,
                QF[k], vertex, 0, &reconstruction, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
        }
    }
    *paths = reconstruction.paths ;
    *path_count = reconstruction.count ;
    reconstruction.paths = NULL ;

reconstruction_cleanup:
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    LAGraph_Free ((void **) &reconstruction.reverse_path, NULL) ;
    return (info) ;
}

/**
 * @brief Reconstruct simple paths from the completed accumulation matrix.
 * @param[out] paths Non-NULL address receiving owned paths, or NULL on error.
 * @param[out] path_count Non-NULL address receiving their count, or zero.
 * @param[in] P Completed predecessor matrix, borrowed and never modified.
 * @param[in] roots Immutable initial-configuration relation, borrowed.
 * @param[in] QF Array of nqf accepting states; NULL allowed when nqf=0.
 * @param[in] nqf Number of accepting states, including duplicates.
 * @param[in] ng Number of graph vertices, equal to ncols(P).
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error, with no partial result.
 */
static int LG_RpqPath_ProcessSimple
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { 0 } ;
    int info = GrB_SUCCESS ;
    for (GrB_Index vertex = 0 ; vertex < ng ; vertex++)
    {
        for (size_t k = 0 ; k < nqf ; k++)
        {
            info = LG_RpqPath_ReservePath (&reconstruction, 0, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
            reconstruction.reverse_path[0] = vertex ;
            info = LG_RpqPath_ReconstructSimpleCell (P, roots,
                QF[k], vertex, 0, &reconstruction, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
        }
    }
    *paths = reconstruction.paths ;
    *path_count = reconstruction.count ;
    reconstruction.paths = NULL ;

reconstruction_cleanup:
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    LAGraph_Free ((void **) &reconstruction.reverse_path, NULL) ;
    return (info) ;
}

/**
 * @brief Reconstruct trails paths from the completed accumulation matrix.
 * @param[out] paths Non-NULL address receiving owned paths, or NULL on error.
 * @param[out] path_count Non-NULL address receiving their count, or zero.
 * @param[in] P Completed predecessor matrix, borrowed and never modified.
 * @param[in] roots Immutable initial-configuration relation, borrowed.
 * @param[in] QF Array of nqf accepting states; NULL allowed when nqf=0.
 * @param[in] nqf Number of accepting states, including duplicates.
 * @param[in] ng Number of graph vertices, equal to ncols(P).
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error, with no partial result.
 */
static int LG_RpqPath_ProcessTrails
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { 0 } ;
    int info = GrB_SUCCESS ;
    for (GrB_Index vertex = 0 ; vertex < ng ; vertex++)
    {
        for (size_t k = 0 ; k < nqf ; k++)
        {
            info = LG_RpqPath_ReservePath (&reconstruction, 0, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
            reconstruction.reverse_path[0] = vertex ;
            info = LG_RpqPath_ReconstructTrailsCell (P, roots,
                QF[k], vertex, 0, &reconstruction, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
        }
    }
    *paths = reconstruction.paths ;
    *path_count = reconstruction.count ;
    reconstruction.paths = NULL ;

reconstruction_cleanup:
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    LAGraph_Free ((void **) &reconstruction.reverse_path, NULL) ;
    return (info) ;
}

/**
 * @brief Reconstruct shortest paths from the completed accumulation matrix.
 * @param[out] paths Non-NULL address receiving owned paths, or NULL on error.
 * @param[out] path_count Non-NULL address receiving their count, or zero.
 * @param[in] P Completed predecessor matrix, borrowed and never modified.
 * @param[in] roots Immutable initial-configuration relation, borrowed.
 * @param[in] QF Array of nqf accepting states; NULL allowed when nqf=0.
 * @param[in] nqf Number of accepting states, including duplicates.
 * @param[in] ng Number of graph vertices, equal to ncols(P).
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error, with no partial result.
 */
static int LG_RpqPath_ProcessShortest
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { 0 } ;
    int info = GrB_SUCCESS ;
    for (GrB_Index vertex = 0 ; vertex < ng ; vertex++)
    {
        // One minimum covers all accepting states and source configurations
        // for this endpoint.  Earlier endpoints' results remain independent.
        size_t destination_begin = reconstruction.count ;
        size_t shortest_length = SIZE_MAX ;
        for (size_t k = 0 ; k < nqf ; k++)
        {
            info = LG_RpqPath_ReservePath (&reconstruction, 0, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
            reconstruction.reverse_path[0] = vertex ;
            info = LG_RpqPath_ReconstructShortestCell (P, roots,
                QF[k], vertex, 0, &reconstruction, destination_begin, &shortest_length, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
        }
    }
    *paths = reconstruction.paths ;
    *path_count = reconstruction.count ;
    reconstruction.paths = NULL ;

reconstruction_cleanup:
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    LAGraph_Free ((void **) &reconstruction.reverse_path, NULL) ;
    return (info) ;
}

typedef struct
{
    GrB_Index ng ;                   // number of graph vertices
    GrB_Index nr ;                   // number of automaton states
    size_t nl ;                      // number of label slots
    bool inverse ;                   // reverse the whole query

    // Arrays are owned by this workspace; the matrices they reference belong
    // to the caller.  Transposition is requested through GraphBLAS descriptors;
    // no cached transposes are retained or used by the traversal.
    GrB_Matrix *A ;                  // original graph decomposition
    GrB_Matrix *N ;                  // original NFA decomposition
    bool *reverse_graph ;           // inverse XOR inverse_labels[label]

    GrB_Type state_set_type ;        // H value: header and room for nr states
    GrB_Type temporary_set_type ;    // C value: handle to temporary blocks
    GrB_Type stored_set_type ;       // P value: owned array of predecessors

    // Traversal matrices are local to Traverse, never stored in this context.
}
LG_RpqPath_Workspace ;

/**
 * @brief Release a complete or partially initialized workspace.
 *
 * @param[in,out] workspace Address of the owned workspace pointer.  All owned
 *     buffers and GraphBLAS objects are released and *workspace becomes NULL.
 *     A NULL address or an already NULL workspace is accepted.
 *
 * The A/N arrays are freed, but their elements are borrowed input matrices
 * and are never freed here.
 * This context owns no traversal matrices.  Traverse releases them locally
 * before the value types owned by this context can be destroyed.
 */
static void LG_RpqPath_Free (LG_RpqPath_Workspace **workspace)
{
    if (workspace == NULL || *workspace == NULL) return ;
    LG_RpqPath_Workspace *work = *workspace ;
    GrB_free (&work->state_set_type) ;
    GrB_free (&work->temporary_set_type) ;
    GrB_free (&work->stored_set_type) ;
    LAGraph_Free ((void **) &work->A, NULL) ;
    LAGraph_Free ((void **) &work->N, NULL) ;
    LAGraph_Free ((void **) &work->reverse_graph, NULL) ;
    LAGraph_Free ((void **) workspace, NULL) ;
}

#if LG_RPQ_PATH_VALIDATE_INPUT
/**
 * @brief Validate all initialization inputs without allocating a workspace.
 *
 * @param[in] workspace Address intended to receive the workspace in Init;
 *     must not be NULL.  This function does not read or modify *workspace.
 * @param[in] R NFA decomposition, an array of nl graph handles.  R[a] may be
 *     NULL for an absent label; at least one adjacency matrix must exist.
 * @param[in] inverse_labels Non-NULL array of nl flags; true means the label
 *     traverses graph edges in reverse.  Only the pointer is checked here.
 * @param[in] nl Number of label slots shared by G, R and inverse_labels;
 *     must be positive.
 * @param[in] QS Array of nqs initial NFA state indices; NULL allowed if nqs=0.
 * @param[in] nqs Number of entries in QS; duplicates are allowed.
 * @param[in] QF Array of nqf accepting NFA state indices; NULL allowed if nqf=0.
 * @param[in] nqf Number of entries in QF; duplicates are allowed.
 * @param[in] G Graph decomposition, an array of nl graph handles.  G[a] may be
 *     NULL for an absent label; at least one adjacency matrix must exist.
 * @param[in] S Array of ns source vertex indices; NULL allowed if ns=0.
 * @param[in] ns Number of entries in S; duplicates are allowed.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.
 *
 * All indices are zero-based.  Each decomposition must contain square
 * matrices of one common size; the graph and NFA sizes may differ.
 * The caller must supply arrays with the stated lengths: this function cannot
 * discover the actual allocation sizes behind the pointers.
 *
 * @return GrB_SUCCESS on valid input, otherwise a LAGraph/GraphBLAS error code.
 * @note Compiled only when LG_RPQ_PATH_VALIDATE_INPUT is enabled.  This helper
 *     owns no memory; the caller handles any workspace cleanup.
 */
static int LG_RpqPath_ValidateInput
(
    LG_RpqPath_Workspace **workspace,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    char *msg
)
{
    LG_ASSERT (workspace != NULL, GrB_NULL_POINTER) ;
    LG_ASSERT (G != NULL && R != NULL, GrB_NULL_POINTER) ;
    LG_ASSERT (inverse_labels != NULL, GrB_NULL_POINTER) ;
    // Empty sets are valid; a NULL array is allowed only for a zero count.
    LG_ASSERT (S != NULL || ns == 0, GrB_NULL_POINTER) ;
    LG_ASSERT (QS != NULL || nqs == 0, GrB_NULL_POINTER) ;
    LG_ASSERT (QF != NULL || nqf == 0, GrB_NULL_POINTER) ;
    LG_ASSERT_MSG (nl > 0, GrB_INVALID_VALUE,
        "at least one label slot is required to determine graph dimensions") ;

    GrB_Index ng = 0, nr = 0 ;
    bool have_graph = false, have_nfa = false ;

    // Graph matrices must agree with each other; their size need not equal
    // the NFA size.  Missing labels are allowed on either side independently.
    for (size_t a = 0 ; a < nl ; a++)
    {
        if (G[a] == NULL) continue ;
        LG_TRY (LAGraph_CheckGraph (G[a], msg)) ;
        GrB_Index rows = 0, cols = 0 ;
        GRB_TRY (GrB_Matrix_nrows (&rows, G[a]->A)) ;
        GRB_TRY (GrB_Matrix_ncols (&cols, G[a]->A)) ;
        if (!have_graph)
        {
            ng = rows ;
            have_graph = true ;
        }
        LG_ASSERT_MSGF (rows == ng && cols == ng, GrB_DIMENSION_MISMATCH,
            "graph decomposition matrices must be square and have the same "
            "dimensions (label %zu)", a) ;
    }
    LG_ASSERT_MSG (have_graph, GrB_INVALID_VALUE,
        "graph decomposition must contain at least one adjacency matrix") ;

    for (size_t a = 0 ; a < nl ; a++)
    {
        if (R[a] == NULL) continue ;
        LG_TRY (LAGraph_CheckGraph (R[a], msg)) ;
        GrB_Index rows = 0, cols = 0 ;
        GRB_TRY (GrB_Matrix_nrows (&rows, R[a]->A)) ;
        GRB_TRY (GrB_Matrix_ncols (&cols, R[a]->A)) ;
        if (!have_nfa)
        {
            nr = rows ;
            have_nfa = true ;
        }
        LG_ASSERT_MSGF (rows == nr && cols == nr, GrB_DIMENSION_MISMATCH,
            "NFA decomposition matrices must be square and have the same "
            "dimensions (label %zu)", a) ;
    }
    LG_ASSERT_MSG (have_nfa, GrB_INVALID_VALUE,
        "NFA decomposition must contain at least one adjacency matrix") ;

    for (size_t k = 0 ; k < ns ; k++)
    {
        LG_ASSERT_MSG (S[k] < ng, GrB_INVALID_INDEX,
            "invalid graph source vertex") ;
    }
    for (size_t k = 0 ; k < nqs ; k++)
    {
        LG_ASSERT_MSG (QS[k] < nr, GrB_INVALID_INDEX,
            "invalid NFA starting state") ;
    }
    for (size_t k = 0 ; k < nqf ; k++)
    {
        LG_ASSERT_MSG (QF[k] < nr, GrB_INVALID_INDEX,
            "invalid NFA final state") ;
    }
    return (GrB_SUCCESS) ;
}
#endif

/**
 * @brief Prepare references to one decomposition and determine its dimension.
 *
 * @param[in] graphs Array of nl graph handles for either the graph or the NFA.
 *     NULL entries represent absent labels; at least one matrix must exist.
 * @param[in] nl Number of slots in graphs and matrices.
 * @param[out] matrices Caller-allocated array of nl matrix handles.  Receives
 *     graphs[a]->A, or NULL for an absent label.  Matrix ownership stays with
 *     the input graphs; no matrix is copied or allocated.
 * @param[out] dimension Non-NULL output for the number of rows of the first
 *     available matrix: graph vertex count or NFA state count.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.
 *
 * @return GrB_SUCCESS on success, otherwise a GraphBLAS error code.  Outputs
 *     may be partially filled on error; the caller retains their ownership.
 * @pre Inputs satisfy ValidateInput's requirements.  This helper performs
 *     necessary preparation even when input validation is disabled.
 */
static int LG_RpqPath_PrepareDecomposition
(
    LAGraph_Graph *graphs,
    size_t nl,
    GrB_Matrix *matrices,
    GrB_Index *dimension,
    char *msg
)
{
    bool have_dimension = false ;

    for (size_t a = 0 ; a < nl ; a++)
    {
        matrices[a] = NULL ;
        if (graphs[a] == NULL) continue ;
        matrices[a] = graphs[a]->A ;
        if (!have_dimension)
        {
            GRB_TRY (GrB_Matrix_nrows (dimension, matrices[a])) ;
            have_dimension = true ;
        }
    }
    return (GrB_SUCCESS) ;
}

// Only Init owns a workspace.  Its error macros release any partial setup.
#undef LG_FREE_WORK
#define LG_FREE_WORK LG_RpqPath_Free (&work)

/**
 * @brief Initialize the workspace for the future path-query traversal.
 *
 * @param[out] workspace Non-NULL address receiving the newly owned workspace.
 *     On error, *workspace is NULL.  Release a successful result with
 *     LG_RpqPath_Free; this output must not hold an unreleased workspace.
 * @param[in] R NFA decomposition: nl graph handles indexed by label.  Individual
 *     entries may be NULL; at least one adjacency matrix must exist.
 * @param[in] inverse_labels Non-NULL array of nl flags.  A true entry reverses
 *     graph traversal for that label, before whole-query inversion is applied.
 * @param[in] nl Positive number of label slots in R, G and inverse_labels.
 * @param[in] QS Array of nqs initial NFA state indices; NULL allowed if nqs=0.
 * @param[in] nqs Number of entries in QS; duplicates are allowed.
 * @param[in] QF Array of nqf accepting NFA state indices; NULL allowed if nqf=0.
 *     These indices are validated but not retained; pass them to Traverse.
 * @param[in] nqf Number of entries in QF; duplicates are allowed.
 * @param[in] G Graph decomposition: nl graph handles indexed by label.
 *     Individual entries may be NULL; at least one adjacency matrix must exist.
 * @param[in] S Array of ns source vertex indices; NULL allowed if ns=0.
 * @param[in] ns Number of entries in S; duplicates are allowed.
 * @param[in] inverse Reverse the whole query: traverse the NFA backwards and
 *     flip every label's graph direction (inverse XOR inverse_labels[a]).
 *     QS and QF are used as supplied; this function does not swap them.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.  Cleared on entry.
 *
 * All indices are zero-based.  Empty source/start/final sets are valid.
 * Input matrices are borrowed and must remain alive while the workspace is
 * used.  Matrix handles and direction flags are copied into workspace arrays.
 * QS, QF and S are validated but not retained.  Query uses them again
 * when creating roots and reconstructing accepting paths in Query.
 *
 * @return GrB_SUCCESS on success, otherwise a LAGraph/GraphBLAS error code;
 *     any partially allocated workspace is released before returning an error.
 * @note This function prepares metadata and value types only.  Query owns
 *     roots; Traverse builds P, with H/C created inside its loop.
 *     With LG_RPQ_PATH_VALIDATE_INPUT=0, the caller guarantees valid inputs.
 */
int LG_RpqPath_Init
(
    LG_RpqPath_Workspace **workspace,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    char *msg
)
{
    LG_CLEAR_MSG ;
    LG_RpqPath_Workspace *work = NULL ;

    if (workspace != NULL) *workspace = NULL ;
#if LG_RPQ_PATH_VALIDATE_INPUT
    LG_TRY (LG_RpqPath_ValidateInput (workspace, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, msg)) ;
#else
    // These sets are only validated here; Traverse receives them directly.
    (void) QS ;
    (void) nqs ;
    (void) QF ;
    (void) nqf ;
    (void) S ;
    (void) ns ;
#endif

    LG_TRY (LAGraph_Calloc ((void **) &work, 1,
        sizeof (LG_RpqPath_Workspace), msg)) ;
    work->nl = nl ;
    work->inverse = inverse ;
    LG_TRY (LAGraph_Calloc ((void **) &work->A, nl,
        sizeof (GrB_Matrix), msg)) ;
    LG_TRY (LAGraph_Calloc ((void **) &work->N, nl,
        sizeof (GrB_Matrix), msg)) ;
    LG_TRY (LAGraph_Calloc ((void **) &work->reverse_graph, nl,
        sizeof (bool), msg)) ;

    // Prepare the graph decomposition and determine its vertex count.
    LG_TRY (LG_RpqPath_PrepareDecomposition (G, nl,
        work->A, &work->ng, msg)) ;

    // Prepare the NFA decomposition and determine its state count separately.
    LG_TRY (LG_RpqPath_PrepareDecomposition (R, nl,
        work->N, &work->nr, msg)) ;

    // Whole-query inversion reverses the NFA traversal and flips each graph
    // label's direction.  Keep the original label index for predecessor records.
    for (size_t a = 0 ; a < nl ; a++)
    {
        work->reverse_graph[a] = (inverse != inverse_labels[a]) ;
    }

    // H has variable-size values across queries, but one fixed value size
    // within a query.  Reserve all nr state slots in every value.  Check the
    // allocation-size arithmetic even when optional input validation is off.
    LG_ASSERT_MSG (work->nr <=
        (SIZE_MAX - sizeof (LG_RpqPath_StateSet)) / sizeof (GrB_Index),
        GrB_OUT_OF_MEMORY, "state set size exceeds addressable memory") ;
    size_t state_set_size = sizeof (LG_RpqPath_StateSet) +
        (size_t) work->nr * sizeof (GrB_Index) ;
    GRB_TRY (GrB_Type_new (&work->state_set_type, state_set_size)) ;
    GRB_TRY (GrB_Type_new (&work->temporary_set_type,
        sizeof (LG_RpqPath_TemporarySet))) ;
    GRB_TRY (GrB_Type_new (&work->stored_set_type,
        sizeof (LG_RpqPath_StoredSet))) ;

    *workspace = work ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Build and return the accumulation matrix, without reconstructing paths.
 * @param[out] P_handle Non-NULL address receiving an owned, materialized P.
 *     Initially cleared to NULL.  On failure no partial matrix is returned.
 * @param[in,out] P_owner Non-NULL initialized empty owner receiving P's record
 *     buffers on success.  After all matrix readers finish, free P first and
 *     then call StoredRelease on this owner; GraphBLAS does not free UDT pointers.
 * @param[in] work Borrowed metadata and value types from Init.  Keep the value
 *     types alive while the returned P is used by reconstruction.
 * @param[in] roots Borrowed immutable Boolean QS x S relation, sized nr x ng.
 *     Used only to create the initial frontier; never modified or freed here.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes, cleared
 *     on entry; may be NULL.
 * @return GrB_SUCCESS at the fixed point, or an allocation/GraphBLAS error.
 *     All intermediate matrices, operators and arena memory are released here.
 */
int LG_RpqPath_Traverse
(
    GrB_Matrix *P_handle,
    LG_RpqPath_StoredOwner *P_owner,
    LG_RpqPath_Workspace *work,
    GrB_Matrix roots,
    char *msg
)
{
    LG_CLEAR_MSG ;
    *P_handle = NULL ;
    int info = GrB_SUCCESS ;
    bool pool_exhausted = false ;   // preserve exhaustion across arena reset

    // P and frontier outlive a single iteration.  On success P passes to the
    // caller; frontier remains local and roots is borrowed throughout.
    GrB_Matrix P = NULL ;
    GrB_Matrix frontier = NULL ;
    GrB_Index frontier_nvals = 0 ;
    LG_RpqPath_StoredOwner stored_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;

    // The first product uses one query-specific semiring for all labels.
    // Operators are local to this traversal, just like its matrices.
    GrB_BinaryOp state_union = NULL ;
    GrB_Monoid state_union_monoid = NULL ;
    GxB_IndexBinaryOp collect_state = NULL ;
    GrB_BinaryOp state_multiply = NULL ;
    GrB_Semiring state_semiring = NULL ;
    GrB_Scalar state_capacity = NULL ;
    LG_RpqPath_StateSet *empty_state_set = NULL ;

    // The second product reduces with predecessor-set union and binds a pool
    // pointer and label to its indexed multiplier separately for each label.
    GrB_BinaryOp predecessor_union = NULL ;
    GrB_Monoid predecessor_union_monoid = NULL ;
    GxB_IndexBinaryOp collect_predecessors = NULL ;
    GrB_Type predecessor_context_type = NULL ;
    GrB_Descriptor predecessor_product = NULL ;

    // Read-only comparison of C with the old P produces Boolean change flags.
    GrB_BinaryOp has_new_predecessors = NULL ;
    GrB_Scalar empty_temporary = NULL ;
    GrB_Scalar empty_stored = NULL ;

    // A second mixed operator returns StoredSet instead of bool.  Its bound
    // context selects the owner for newly allocated P buffers each iteration.
    GxB_IndexBinaryOp merge_predecessors = NULL ;
    GrB_Type stored_context_type = NULL ;

    // All temporary C values in this traversal will borrow this local pool.
    // Its backing array survives iterations; the reservation index is reset.
    LG_RpqPath_BlockPool pool =
    {
        .blocks = NULL,
        .block_count = 0,
        .next_block = ATOMIC_VAR_INIT (0),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;

    // Reserve the fixed pool before any matrix operator can request a block.
    // Partial initialization is also handled by traversal_cleanup below.
    info = LG_RpqPath_PoolInit (&pool, LG_RPQ_PATH_POOL_BLOCKS, msg) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = GrB_BinaryOp_new (&state_union, LG_RpqPath_UnionStates,
        work->state_set_type, work->state_set_type, work->state_set_type) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    // The identity occupies the full UDT size, not just its C struct header.
    // GrB_Monoid_new_UDT copies those bytes; the source buffer is then released.
    size_t state_set_size = sizeof (LG_RpqPath_StateSet) +
        (size_t) work->nr * sizeof (GrB_Index) ;
    info = LAGraph_Calloc ((void **) &empty_state_set, 1, state_set_size, msg) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    empty_state_set->capacity = (size_t) work->nr ;
    info = GrB_Monoid_new_UDT (&state_union_monoid, state_union,
        empty_state_set) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    LAGraph_Free ((void **) &empty_state_set, NULL) ;

    info = GxB_IndexBinaryOp_new (&collect_state, LG_RpqPath_CollectState,
        work->state_set_type, GrB_BOOL, GrB_BOOL, GrB_UINT64,
        "LG_RpqPath_CollectState", NULL) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Scalar_new (&state_capacity, GrB_UINT64) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Scalar_setElement_UINT64 (state_capacity, (uint64_t) work->nr) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GxB_BinaryOp_new_IndexOp (&state_multiply, collect_state,
        state_capacity) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Semiring_new (&state_semiring, state_union_monoid,
        state_multiply) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = GrB_BinaryOp_new (&predecessor_union, LG_RpqPath_UnionPredecessors,
        work->temporary_set_type, work->temporary_set_type,
        work->temporary_set_type) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    LG_RpqPath_TemporarySet empty_predecessor_set =
        { .pool = &pool, .head = NULL } ;
    info = GrB_Monoid_new_UDT (&predecessor_union_monoid, predecessor_union,
        &empty_predecessor_set) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Type_new (&predecessor_context_type,
        sizeof (LG_RpqPath_PredecessorContext)) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GxB_IndexBinaryOp_new (&collect_predecessors,
        LG_RpqPath_CollectPredecessors, work->temporary_set_type,
        work->state_set_type, GrB_BOOL, predecessor_context_type,
        "LG_RpqPath_CollectPredecessors", NULL) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    // Correctness workaround for SuiteSparse's generic flipped indexed SAXPY
    // kernel: it sizes operand buffers using GB_GENERIC_FLIPXY, overlooking
    // GB_GENERIC_IDX_FLIPXY.  StateSet x bool can therefore copy a full StateSet
    // into a bool-sized buffer when the backend swaps operands for CSR/CSC.
    // The generic dot kernel handles mixed operand sizes correctly.  This is
    // an explicit backend restriction, not a performance tuning decision.
    info = GrB_Descriptor_new (&predecessor_product) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Descriptor_set (predecessor_product,
        GxB_AxB_METHOD, GxB_AxB_DOT) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = GrB_BinaryOp_new (&has_new_predecessors,
        LG_RpqPath_HasNewPredecessors, GrB_BOOL,
        work->temporary_set_type, work->stored_set_type) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Type_new (&stored_context_type,
        sizeof (LG_RpqPath_StoredContext)) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GxB_IndexBinaryOp_new (&merge_predecessors,
        LG_RpqPath_MergePredecessors, work->stored_set_type,
        work->temporary_set_type, work->stored_set_type, stored_context_type,
        "LG_RpqPath_MergePredecessors", NULL) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Scalar_new (&empty_temporary, work->temporary_set_type) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Scalar_setElement_UDT (empty_temporary, &empty_predecessor_set) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Scalar_new (&empty_stored, work->stored_set_type) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    LG_RpqPath_StoredSet empty_stored_set = { .count = 0, .allocation = NULL } ;
    info = GrB_Scalar_setElement_UDT (empty_stored, &empty_stored_set) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = GrB_Matrix_new (&P, work->stored_set_type, work->nr, work->ng) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Matrix_dup (&frontier, roots) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Matrix_nvals (&frontier_nvals, frontier) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    while (frontier_nvals != 0)
    {
        // Created afresh for this iteration; no workspace aliases exist.
        GrB_Matrix H = NULL ;
        GrB_Matrix C = NULL ;
        GrB_Matrix next_frontier = NULL ;

        LG_RpqPath_StoredOwner next_stored_owner =
        {
            .allocations = ATOMIC_VAR_INIT (NULL),
            .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
        } ;
        GrB_Scalar stored_context = NULL ;
        GrB_BinaryOp stored_merge = NULL ;
        bool updating_P = false ;

        // A bound index operator copies its scalar, so the multiplier and its
        // semiring must be recreated when the label changes.  Keep their
        // handles in this scope to clean partial construction on error too.
        GrB_Scalar predecessor_context = NULL ;
        GrB_BinaryOp predecessor_multiply = NULL ;
        GrB_Semiring predecessor_semiring = NULL ;

        info = GrB_Matrix_new (&H, work->state_set_type, work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_new (&C, work->temporary_set_type,
            work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_new (&next_frontier, GrB_BOOL, work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // Every label uses the same input frontier for this iteration.
        for (size_t a = 0 ; a < work->nl ; a++)
        {
            if (work->A[a] == NULL || work->N[a] == NULL) continue ;

            // H[p,j] = {q | N_a[q,p] && frontier[q,j]} for a direct query.
            // Inverse queries instead follow the original N_a rows.  REPLACE
            // discards the previous label's H values; frontier is only read.
            GrB_Descriptor nfa_direction = work->inverse ?
                GrB_DESC_R : GrB_DESC_RT0 ;
            info = GrB_mxm (H, NULL, NULL, state_semiring,
                work->N[a], frontier, nfa_direction) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            // No wait between the products: GraphBLAS manages the dependency
            // when the second multiplication consumes H as an input matrix.
            LG_RpqPath_PredecessorContext context =
                { .pool = &pool, .label = a } ;
            info = GrB_Scalar_new (&predecessor_context,
                predecessor_context_type) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GrB_Scalar_setElement_UDT (predecessor_context, &context) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GxB_BinaryOp_new_IndexOp (&predecessor_multiply,
                collect_predecessors, predecessor_context) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GrB_Semiring_new (&predecessor_semiring,
                predecessor_union_monoid, predecessor_multiply) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;

            // Accumulate all labels into C without replacing previous values.
            // The indexed product records j from H[p,j], which is unchanged
            // when the graph operand is transposed for an inverse label.
            info = GrB_Descriptor_set (predecessor_product, GrB_INP1,
                work->reverse_graph[a] ? GrB_TRAN : GrB_DEFAULT) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GrB_mxm (C, NULL, predecessor_union, predecessor_semiring,
                H, work->A[a], predecessor_product) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GrB_Matrix_wait (C, GrB_MATERIALIZE) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = atomic_load (&pool.error) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;

            // C is materialized and no longer needs these label-bound objects.
            // The arena itself remains live until the whole iteration ends.
            GrB_free (&predecessor_semiring) ;
            GrB_free (&predecessor_multiply) ;
            GrB_free (&predecessor_context) ;
        }

        // Compare against the OLD P, substituting an empty set wherever a
        // cell is absent on either side.  eWiseUnion applies the predicate
        // at C-only and P-only positions too; ordinary eWiseAdd would copy
        // those UDT values instead of producing the required Boolean result.
        info = GxB_Matrix_eWiseUnion (next_frontier, NULL, NULL,
            has_new_predecessors, C, empty_temporary, P, empty_stored,
            GrB_DESC_R) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        // nvals counts explicit false entries too.  Retain only true flags
        // before using this matrix as the next Boolean frontier.
        info = GrB_Matrix_select_BOOL (next_frontier, NULL, NULL,
            GrB_VALUEEQ_BOOL, next_frontier, true, GrB_DESC_R) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_wait (next_frontier, GrB_MATERIALIZE) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // All readers used for frontier construction have finished.  Bind a
        // separate owner so the old P buffers stay alive throughout the merge.
        LG_RpqPath_StoredContext context = { .owner = &next_stored_owner } ;
        info = GrB_Scalar_new (&stored_context, stored_context_type) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Scalar_setElement_UDT (stored_context, &context) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GxB_BinaryOp_new_IndexOp (&stored_merge, merge_predecessors,
            stored_context) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // Update the same P matrix handle.  Every position, including P-only
        // cells, gets a fully copied sorted union with no old-buffer or arena
        // references.  Ordinary eWiseAdd would bypass the operator for cells
        // present on only one side and cannot handle these mixed UDT types.
        updating_P = true ;
        info = GxB_Matrix_eWiseUnion (P, NULL, NULL, stored_merge,
            C, empty_temporary, P, empty_stored, NULL) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_wait (P, GrB_MATERIALIZE) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = atomic_load (&next_stored_owner.error) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // P now refers only to the new owner.  Release all former buffers and
        // transfer ownership; no matrix tuple extraction is needed for cleanup.
        LG_RpqPath_StoredRelease (&stored_owner) ;
        atomic_store (&stored_owner.allocations,
            atomic_exchange (&next_stored_owner.allocations, NULL)) ;
        updating_P = false ;
        info = GrB_Matrix_nvals (&frontier_nvals, next_frontier) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // Release the old frontier, transfer the new handle, and clear its
        // former owner so iteration cleanup cannot free the next input.
        GrB_free (&frontier) ;
        frontier = next_frontier ;
        next_frontier = NULL ;

iteration_cleanup:
        // A pending change predicate may still read both old P and C.  Wait
        // before releasing C's arena handles, including on a failed operation.
        // Preserve the original error if cleanup also fails.
        if (next_frontier != NULL)
        {
            int cleanup_info = GrB_Matrix_wait (next_frontier, GrB_MATERIALIZE) ;
            if (info == GrB_SUCCESS) info = cleanup_info ;
        }
        if (C != NULL)
        {
            int cleanup_info = GrB_Matrix_wait (C, GrB_MATERIALIZE) ;
            if (info == GrB_SUCCESS) info = cleanup_info ;
        }
        if (updating_P)
        {
            // A failed in-place merge may leave handles from either owner in
            // P.  Finish pending callbacks and discard P before freeing either
            // owner's buffers or resetting C's arena.
            int cleanup_info = GrB_Matrix_wait (P, GrB_MATERIALIZE) ;
            if (info == GrB_SUCCESS) info = cleanup_info ;
            GrB_free (&P) ;
        }
        int pool_info = atomic_load (&pool.error) ;
        if (pool_info == GrB_OUT_OF_MEMORY) pool_exhausted = true ;
        if (info == GrB_SUCCESS) info = pool_info ;
        // H owns its state sets inline; freeing H releases their storage too.
        // C only holds arena handles, so free C before resetting that arena.
        // P replacements have finished and own independent record buffers.
        GrB_free (&H) ;
        GrB_free (&C) ;
        GrB_free (&next_frontier) ;
        GrB_free (&predecessor_semiring) ;
        GrB_free (&predecessor_multiply) ;
        GrB_free (&predecessor_context) ;
        GrB_free (&stored_merge) ;
        GrB_free (&stored_context) ;
        LG_RpqPath_StoredRelease (&next_stored_owner) ;
        LG_RpqPath_PoolReset (&pool) ;
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }

    // The completed matrix and its independently allocated records outlive
    // this stage.  Transfer both owners; no arena memory is retained in P.
    *P_handle = P ;
    P = NULL ;
    atomic_store (&P_owner->allocations,
        atomic_exchange (&stored_owner.allocations, NULL)) ;
traversal_cleanup:
    GrB_free (&frontier) ;
    // Drop all matrix handles before freeing any surviving stored buffers.
    // The owner list also tracks buffers whose handles GraphBLAS discarded.
    GrB_free (&P) ;
    LG_RpqPath_StoredRelease (&stored_owner) ;
    // Matrices have been released; their operators can now be released too.
    GrB_free (&has_new_predecessors) ;
    GrB_free (&merge_predecessors) ;
    GrB_free (&stored_context_type) ;
    GrB_free (&empty_temporary) ;
    GrB_free (&empty_stored) ;
    GrB_free (&predecessor_product) ;
    GrB_free (&collect_predecessors) ;
    GrB_free (&predecessor_union_monoid) ;
    GrB_free (&predecessor_union) ;
    GrB_free (&predecessor_context_type) ;
    GrB_free (&state_semiring) ;
    GrB_free (&state_multiply) ;
    GrB_free (&collect_state) ;
    GrB_free (&state_union_monoid) ;
    GrB_free (&state_union) ;
    GrB_free (&state_capacity) ;
    LAGraph_Free ((void **) &empty_state_set, NULL) ;
    LG_RpqPath_PoolDestroy (&pool) ;
    if (info == GrB_OUT_OF_MEMORY && pool_exhausted)
    {
        LG_ERROR_MSG ("RPQ predecessor block pool is exhausted") ;
    }
    else if (info != GrB_SUCCESS && (msg == NULL || msg[0] == '\0'))
    {
        LG_ERROR_MSG ("RPQ matrix traversal failed: info: %d", info) ;
    }
    return (info) ;
}

/**
 * @brief Own initialization, traversal and cleanup for any public query mode.
 * @param[out] paths Non-NULL address receiving independently owned paths, or
 *     NULL on error/empty result.  Must not hold an unreleased array on entry.
 * @param[out] path_count Non-NULL address receiving the result count, or zero.
 * @param[in] R Borrowed NFA decomposition of nl possibly NULL label slots.
 * @param[in] inverse_labels Non-NULL array of nl graph-direction flags.
 * @param[in] nl Number of shared label slots; positive.
 * @param[in] QS Initial NFA state array; NULL allowed if nqs=0.
 * @param[in] nqs Number of entries in QS.
 * @param[in] QF Accepting NFA state array; NULL allowed if nqf=0.
 * @param[in] nqf Number of entries in QF.
 * @param[in] G Borrowed graph decomposition of nl possibly NULL label slots.
 * @param[in] S Source vertex array; NULL allowed if ns=0.
 * @param[in] ns Number of entries in S.
 * @param[in] inverse Reverse the NFA and toggle every label's graph direction.
 * @param[in] process Non-NULL handler consuming the completed matrix P.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes, cleared
 *     on entry.  May be NULL.
 * @return GrB_SUCCESS or an input, allocation or GraphBLAS error.  No query
 *     workspace is retained and no partial path result is returned on error.
 */
static int LG_RpqPath_Query
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    LG_RpqPath_Process process,
    char *msg
)
{
    LG_CLEAR_MSG ;
    if (paths != NULL) *paths = NULL ;
    if (path_count != NULL) *path_count = 0 ;
    if (paths == NULL || path_count == NULL)
    {
        LG_ERROR_MSG ("path result addresses must not be NULL") ;
        return (GrB_NULL_POINTER) ;
    }
    LG_RpqPath_Workspace *work = NULL ;
    GrB_Matrix P = NULL, roots = NULL ;
    LG_RpqPath_StoredOwner P_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;
    int info = LG_RpqPath_Init (&work, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, inverse, msg) ;
    if (info != GrB_SUCCESS) goto query_cleanup ;
    info = GrB_Matrix_new (&roots, GrB_BOOL, work->nr, work->ng) ;
    if (info != GrB_SUCCESS) goto query_cleanup ;
    if (nqs > 0 && ns > 0)
    {
        info = GrB_Matrix_assign_BOOL (roots, NULL, NULL, true,
            QS, nqs, S, ns, NULL) ;
        if (info != GrB_SUCCESS) goto query_cleanup ;
    }

    // Stage 1: finish the matrix algorithm, regardless of path semantics.
    info = LG_RpqPath_Traverse (&P, &P_owner, work, roots, msg) ;
    if (info != GrB_SUCCESS) goto query_cleanup ;

    // Stage 2: the selected handler only reads P and roots.  Their storage
    // remains live until reconstruction and all callback invocations finish.
    info = process (paths, path_count, P, roots, QF, nqf, work->ng, msg) ;

query_cleanup:
    GrB_free (&P) ;
    LG_RpqPath_StoredRelease (&P_owner) ;
    GrB_free (&roots) ;
    LG_RpqPath_Free (&work) ;
    if (info != GrB_SUCCESS && (msg == NULL || msg[0] == '\0'))
    {
        LG_ERROR_MSG ("RPQ query failed: info: %d", info) ;
    }
    return (info) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllPaths
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    char *msg
)
{
    return (LG_RpqPath_Query (paths, path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ProcessAll, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllSimple
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    char *msg
)
{
    return (LG_RpqPath_Query (paths, path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ProcessSimple, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllTrails
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    char *msg
)
{
    return (LG_RpqPath_Query (paths, path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ProcessTrails, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllShortestPaths
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    bool inverse,
    char *msg
)
{
    return (LG_RpqPath_Query (paths, path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ProcessShortest, msg)) ;
}


// See LAGraphX.h for ownership and argument documentation.
int LAGraph_2RpqPath_FreePaths
(
    LAGraph_RpqPath **paths,
    size_t path_count,
    char *msg
)
{
    LG_CLEAR_MSG ;
    LG_RpqPath_FreePaths (paths, path_count) ;
    return (GrB_SUCCESS) ;
}

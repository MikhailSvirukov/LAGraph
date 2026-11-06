//------------------------------------------------------------------------------
// LAGraph_2RpqPath.c: regular path enumeration through predecessor matrices
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause
//
// Query lifecycle: initialize metadata, build P, reconstruct paths, clean up.
// The matrix stage uses a Boolean frontier M.  For each label a (direct case):
//
//   H[p,j] = { q : N_a[q,p] && M[q,j] },
//   C[p,i] = { (q,j,a) : q belongs to H[p,j] && G_a[j,i] }.
//
// Each iteration builds C, computes the new frontier against OLD P, then
// merges C into P and releases temporary storage.  New predecessor records
// reactivate cells; alternative predecessors and cycles remain in P.
// Reconstruction reads the completed P and applies the selected semantics.
// Query owns roots/workspace; Traverse owns its matrices and operator handles.
// Optimizations, including minor ones, require the user's prior approval.

// The input helpers own no memory; workspace cleanup is enabled before Init.
#define LG_FREE_WORK ;
#define LG_FREE_ALL LG_FREE_WORK

#include "LG_internal.h"
#include "LAGraphX.h"
#include <stdatomic.h>

// Input correctness is the caller's responsibility.

// Maximum reconstructed path length, in edges, including for all-paths queries
// whose result could otherwise be infinite.  This does not limit the matrix
// traversal, which terminates when P stops receiving new predecessor records.
#ifndef LG_RPQ_PATH_MAX_LENGTH
#define LG_RPQ_PATH_MAX_LENGTH 60000
#endif
#if LG_RPQ_PATH_MAX_LENGTH < 0
#error "LG_RPQ_PATH_MAX_LENGTH must be nonnegative"
#endif

// Stop reconstruction as soon as this many distinct paths have been saved.
// Return the collected prefix successfully, including for shortest semantics.
#ifndef LG_RPQ_PATH_MAX_COUNT
#define LG_RPQ_PATH_MAX_COUNT 100000
#endif
#if LG_RPQ_PATH_MAX_COUNT < 1
#error "LG_RPQ_PATH_MAX_COUNT must be positive"
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

//------------------------------------------------------------------------------
// Predecessor records and first-product state sets (H)
//------------------------------------------------------------------------------

// One incoming product-graph edge.  Its destination is given by the P/C cell
// indices; these fields identify the predecessor configuration and edge label.
typedef struct
{
    GrB_Index state ;               // predecessor NFA state q
    GrB_Index vertex ;              // predecessor graph vertex j
    size_t label ;                  // traversed label a
}
LG_RpqPath_Predecessor ;

// H value: header + nr state slots, with a fixed GraphBLAS type size per query.
// The first count slots hold sorted distinct states; unused slots are zero.
// capacity == nr lets callbacks fill the entire value without global state.
typedef struct
{
    size_t count ;
    size_t capacity ;
    GrB_Index states [] ;
}
LG_RpqPath_StateSet ;

/**
 * @brief Union two sorted state sets without allocation.
 * @param[out] z Full StateSet buffer (header + capacity slots); may alias x or y.
 * @param[in] x Sorted distinct states in the query-specific StateSet type.
 * @param[in] y Sorted distinct states with the same type and capacity as x.
 * The result is sorted and distinct, with unused slots zeroed.  States lie in
 * [0, capacity), so the union fits.  Merge/move costs O(x->count + y->count);
 * clearing unused slots costs O(capacity - result->count).
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

//------------------------------------------------------------------------------
// Temporary predecessor sets (C): pool and operations
//------------------------------------------------------------------------------

// next links blocks of one immutable temporary value.  allocation_next links
// every malloc allocation owned by the iteration, including intermediate blocks
// whose UDT handles GraphBLAS has discarded.  The two chains are independent.
typedef struct LG_RpqPath_PredecessorBlock
{
    size_t count ;
    LG_RpqPath_Predecessor records [LG_RPQ_PATH_BLOCK_CAPACITY] ;
    struct LG_RpqPath_PredecessorBlock *next ;
    struct LG_RpqPath_PredecessorBlock *allocation_next ;
}
LG_RpqPath_PredecessorBlock ;

// Blocks are allocated lazily by callbacks and registered with an atomic list
// push.  No block is removed until all readers finish at the end of the step.
// The error flag carries malloc failures out of callbacks with void returns.
typedef struct
{
    _Atomic (LG_RpqPath_PredecessorBlock *) allocations ;
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
 * @brief Allocate an empty block and register it before publishing its handle.
 * @param[in,out] pool Initialized allocations/error atomics.  Allocation uses
 *     LAGraph_Malloc; failure sets error to GrB_OUT_OF_MEMORY.
 * @return A pool-owned block with count=0 and next=NULL, or NULL on failure.
 * CAS publishes an immutable ownership link; no lock is held across malloc.
 * No nodes are removed while callbacks run, so retries cannot encounter ABA.
 * PoolReset releases all blocks after their readers finish.
 */
static LG_RpqPath_PredecessorBlock *LG_RpqPath_PoolAcquire
(
    LG_RpqPath_BlockPool *pool
)
{
    if (atomic_load (&pool->error) != GrB_SUCCESS) return (NULL) ;
    LG_RpqPath_PredecessorBlock *block = NULL ;
    int info = LAGraph_Malloc ((void **) &block, 1,
        sizeof (LG_RpqPath_PredecessorBlock), NULL) ;
    if (info != GrB_SUCCESS)
    {
        atomic_store (&pool->error, GrB_OUT_OF_MEMORY) ;
        return (NULL) ;
    }
    block->count = 0 ;
    block->next = NULL ;
    LG_RpqPath_PredecessorBlock *head = atomic_load (&pool->allocations) ;
    do
    {
        block->allocation_next = head ;
    }
    while (!atomic_compare_exchange_weak (&pool->allocations, &head, block)) ;
    return (block) ;
}

/**
 * @brief Free all temporary blocks and clear the pool error flag.
 * @param[in,out] pool Initialized pool; may be empty.  No blocks are retained.
 * @pre All readers have finished and temporary handles have been discarded.
 *     On success, P already owns deep copies.  Read pool->error before reset.
 */
static void LG_RpqPath_PoolReset (LG_RpqPath_BlockPool *pool)
{
    LG_RpqPath_PredecessorBlock *block =
        atomic_exchange (&pool->allocations, NULL) ;
    while (block != NULL)
    {
        LG_RpqPath_PredecessorBlock *next = block->allocation_next ;
        LAGraph_Free ((void **) &block, NULL) ;
        block = next ;
    }
    atomic_store (&pool->error, GrB_SUCCESS) ;
}

/**
 * @brief Release any blocks remaining after traversal completion or failure.
 * @param[in,out] pool Non-NULL initialized pool; may already be empty.
 * @pre No callbacks are active and no surviving value references these blocks.
 */
static void LG_RpqPath_PoolDestroy (LG_RpqPath_BlockPool *pool)
{
    LG_RpqPath_PoolReset (pool) ;
}

/**
 * @brief Append a predecessor to a private temporary value.
 * @param[in,out] set Unpublished set with a valid pool and an unshared chain.
 * @param[in,out] tail Local last-block pointer, initially NULL; retained across
 *     calls and updated when a new block is attached.
 * @param[in] record Record to copy, in strictly increasing lexicographic order.
 * @return True on success; false on allocation failure (pool error is set).
 * Partial chains remain pool-owned and are released at the end of the step.
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
 * @brief Union immutable temporary sets into a new private block chain.
 * @param[out] z TemporarySet buffer; may alias x or y (handles are read first).
 * @param[in] x Sorted first set, including the empty monoid identity.
 * @param[in] y Sorted second set from the same pool.
 * Two cursors merge and deduplicate in O(|x| + |y|); a local tail appends records.
 * Allocation failure returns an empty handle and sets the pool error; the caller
 * must wait and discard the failed result.  Input chains are never modified.
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
 * empty handle; the caller checks the flag after all readers finish, before
 * resetting the temporary pool at the end of the iteration.
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

//------------------------------------------------------------------------------
// Stored predecessor sets (P): ownership and operations
//------------------------------------------------------------------------------

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

//------------------------------------------------------------------------------
// Query workspace and input decomposition
//------------------------------------------------------------------------------

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
 * @param[in,out] workspace Owned pointer address; cleared on return.
 *     NULL/already NULL is accepted.  A/N arrays are owned, their matrices borrowed.
 * @pre Traverse has released its matrices before their value types are freed.
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


/**
 * @brief Borrow one decomposition and determine its dimension.
 * @param[in] graphs Graph or NFA handles; NULL entries denote absent labels.
 * @param[in] nl Number of slots in graphs and matrices.
 * @param[out] matrices Preallocated nl slots receiving graphs[a]->A or NULL.
 * @param[out] dimension Row count of the first available matrix.
 * @param[out] msg Optional LAGRAPH_MSG_LEN error buffer.
 * @return GrB_SUCCESS or GraphBLAS error; outputs may be partially filled.
 * @pre At least one matrix exists; all input dimensions are correct.
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
 * @brief Create metadata and value types for one query.
 * @param[out] workspace Receives owned workspace, or NULL on error; free with
 *     LG_RpqPath_Free.  Must not contain an unreleased workspace.
 * @param[in] R Borrowed NFA decomposition, nl slots; absent labels may be NULL.
 * @param[in] inverse_labels nl flags reversing individual graph labels.
 * @param[in] nl Positive number of slots in R, G and inverse_labels.
 * @param[in] G Borrowed graph decomposition, nl slots; absent labels may be NULL.
 * @param[in] inverse Reverse the NFA and toggle each graph-label direction.
 * @param[out] msg Optional LAGRAPH_MSG_LEN buffer, cleared on entry.
 * @return GrB_SUCCESS or LAGraph/GraphBLAS error; partial setup is freed.
 * Each decomposition must contain a matrix.  Inputs remain alive for the query;
 * only handles and direction flags are copied.  Query owns roots; Traverse owns
 * its working matrices.  Indices are zero-based.
 */
int LG_RpqPath_Init
(
    LG_RpqPath_Workspace **workspace,
    LAGraph_Graph *R,
    const bool *inverse_labels,
    size_t nl,
    LAGraph_Graph *G,
    bool inverse,
    char *msg
)
{
    LG_CLEAR_MSG ;
    LG_RpqPath_Workspace *work = NULL ;

    *workspace = NULL ;

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
    // within a query.  Reserve all nr state slots in every value.  Guard the
    // allocation-size arithmetic before allocating the value type.
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

//------------------------------------------------------------------------------
// GraphBLAS operator construction and cleanup
//------------------------------------------------------------------------------

// Traversal-local GraphBLAS handles only; this bundle owns no matrices.
typedef struct
{
    GrB_BinaryOp state_union ;
    GrB_Monoid state_union_monoid ;
    GxB_IndexBinaryOp collect_state ;
    GrB_BinaryOp state_multiply ;
    GrB_Semiring state_semiring ;
    GrB_Scalar state_capacity ;
    GrB_BinaryOp predecessor_union ;
    GrB_Monoid predecessor_union_monoid ;
    GxB_IndexBinaryOp collect_predecessors ;
    GrB_Type predecessor_context_type ;
    GrB_Descriptor predecessor_product ;
    GrB_BinaryOp has_new_predecessors ;
    GrB_Scalar empty_temporary ;
    GrB_Scalar empty_stored ;
    GxB_IndexBinaryOp merge_predecessors ;
    GrB_Type stored_context_type ;
}
LG_RpqPath_Operators ;

// One immutable binding per label, reused by every traversal iteration.
typedef struct
{
    GrB_Semiring semiring ;
    GrB_BinaryOp multiply ;
    GrB_Scalar context ;
}
LG_RpqPath_LabelOperators ;

/**
 * @brief Free a complete or partially initialized traversal operator bundle.
 * @param[in,out] ops Non-NULL bundle initially zero-initialized before creation.
 *     Owned handles are freed and cleared; repeat calls are safe.
 * @pre All operations using these handles have completed, and their per-label
 *     and stored-merge bindings have been freed.  Materialized P may survive.
 */
static void LG_RpqPath_FreeOperators (LG_RpqPath_Operators *ops)
{
    // Queued operations and temporary bindings no longer use these handles.
    GrB_free (&ops->has_new_predecessors) ;
    GrB_free (&ops->merge_predecessors) ;
    GrB_free (&ops->stored_context_type) ;
    GrB_free (&ops->empty_temporary) ;
    GrB_free (&ops->empty_stored) ;
    GrB_free (&ops->predecessor_product) ;
    GrB_free (&ops->collect_predecessors) ;
    GrB_free (&ops->predecessor_union_monoid) ;
    GrB_free (&ops->predecessor_union) ;
    GrB_free (&ops->predecessor_context_type) ;
    GrB_free (&ops->state_semiring) ;
    GrB_free (&ops->state_multiply) ;
    GrB_free (&ops->collect_state) ;
    GrB_free (&ops->state_union_monoid) ;
    GrB_free (&ops->state_union) ;
    GrB_free (&ops->state_capacity) ;
}

/**
 * @brief Create the operators and semiring for the first matrix product.
 * @param[in,out] ops Non-NULL zero-initialized bundle; its state handles receive
 *     newly owned objects.  On failure FreeOperators releases partial setup.
 * @param[in] work Borrowed value types and NFA state count from Init.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or an allocation/GraphBLAS error.  The temporary monoid
 *     identity buffer is always released before returning.
 */
static int LG_RpqPath_CreateStateOperators
(
    LG_RpqPath_Operators *ops,
    const LG_RpqPath_Workspace *work,
    char *msg
)
{
    int info = GrB_SUCCESS ;
    LG_RpqPath_StateSet *empty_state_set = NULL ;
    info = GrB_BinaryOp_new (&ops->state_union, LG_RpqPath_UnionStates,
        work->state_set_type, work->state_set_type, work->state_set_type) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;

    // The identity occupies the full UDT size, not just its C struct header.
    // GrB_Monoid_new_UDT copies those bytes; the source buffer is then released.
    size_t state_set_size = sizeof (LG_RpqPath_StateSet) +
        (size_t) work->nr * sizeof (GrB_Index) ;
    info = LAGraph_Calloc ((void **) &empty_state_set, 1, state_set_size, msg) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    empty_state_set->capacity = (size_t) work->nr ;
    info = GrB_Monoid_new_UDT (&ops->state_union_monoid, ops->state_union,
        empty_state_set) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    LAGraph_Free ((void **) &empty_state_set, NULL) ;

    info = GxB_IndexBinaryOp_new (&ops->collect_state, LG_RpqPath_CollectState,
        work->state_set_type, GrB_BOOL, GrB_BOOL, GrB_UINT64,
        "LG_RpqPath_CollectState", NULL) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Scalar_new (&ops->state_capacity, GrB_UINT64) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Scalar_setElement_UINT64 (ops->state_capacity, (uint64_t) work->nr) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GxB_BinaryOp_new_IndexOp (&ops->state_multiply, ops->collect_state,
        ops->state_capacity) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Semiring_new (&ops->state_semiring, ops->state_union_monoid,
        ops->state_multiply) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;

state_cleanup:
    LAGraph_Free ((void **) &empty_state_set, NULL) ;
    return (info) ;
}

/**
 * @brief Create predecessor-set addition and the indexed second-product operator.
 * @param[in,out] ops Non-NULL bundle with zero predecessor handles.  Partial
 *     setup remains registered here for FreeOperators if creation fails.
 * @param[in] work Borrowed value types from Init.
 * @param[in] pool Non-NULL initialized arena, borrowed through all uses of its
 *     empty-set identity and label-bound multipliers.
 * @return GrB_SUCCESS or a GraphBLAS error.  The multiplier is bound per label
 *     separately; this function creates its reusable indexed operator only.
 */
static int LG_RpqPath_CreatePredecessorOperators
(
    LG_RpqPath_Operators *ops,
    const LG_RpqPath_Workspace *work,
    LG_RpqPath_BlockPool *pool
)
{
    int info = GrB_SUCCESS ;
    info = GrB_BinaryOp_new (&ops->predecessor_union, LG_RpqPath_UnionPredecessors,
        work->temporary_set_type, work->temporary_set_type,
        work->temporary_set_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    LG_RpqPath_TemporarySet empty_predecessor_set =
        { .pool = pool, .head = NULL } ;
    info = GrB_Monoid_new_UDT (&ops->predecessor_union_monoid,
        ops->predecessor_union, &empty_predecessor_set) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Type_new (&ops->predecessor_context_type,
        sizeof (LG_RpqPath_PredecessorContext)) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GxB_IndexBinaryOp_new (&ops->collect_predecessors,
        LG_RpqPath_CollectPredecessors, work->temporary_set_type,
        work->state_set_type, GrB_BOOL, ops->predecessor_context_type,
        "LG_RpqPath_CollectPredecessors", NULL) ;
    if (info != GrB_SUCCESS) return (info) ;

    // Correctness workaround for SuiteSparse's generic flipped indexed SAXPY
    // kernel: it sizes operand buffers using GB_GENERIC_FLIPXY, overlooking
    // GB_GENERIC_IDX_FLIPXY.  StateSet x bool can therefore copy a full StateSet
    // into a bool-sized buffer when the backend swaps operands for CSR/CSC.
    // The generic dot kernel handles mixed operand sizes correctly.  This is
    // an explicit backend restriction, not a performance tuning decision.
    info = GrB_Descriptor_new (&ops->predecessor_product) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Descriptor_set (ops->predecessor_product,
        GxB_AxB_METHOD, GxB_AxB_DOT) ;
    if (info != GrB_SUCCESS) return (info) ;

    return (GrB_SUCCESS) ;
}

/**
 * @brief Create the mixed operators and empty scalars for P and the new frontier.
 * @param[in,out] ops Non-NULL bundle with zero accumulation handles.  Partial
 *     setup remains registered here for FreeOperators on failure.
 * @param[in] work Borrowed temporary/stored predecessor value types from Init.
 * @param[in] pool Non-NULL arena borrowed by the empty temporary-set scalar.
 * @return GrB_SUCCESS or a GraphBLAS error.  The stored-set merger is bound to
 *     a reusable new-buffer owner separately, before traversal starts.
 */
static int LG_RpqPath_CreateAccumulationOperators
(
    LG_RpqPath_Operators *ops,
    const LG_RpqPath_Workspace *work,
    LG_RpqPath_BlockPool *pool
)
{
    int info = GrB_SUCCESS ;
    LG_RpqPath_TemporarySet empty_predecessor_set =
        { .pool = pool, .head = NULL } ;
    info = GrB_BinaryOp_new (&ops->has_new_predecessors,
        LG_RpqPath_HasNewPredecessors, GrB_BOOL,
        work->temporary_set_type, work->stored_set_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Type_new (&ops->stored_context_type,
        sizeof (LG_RpqPath_StoredContext)) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GxB_IndexBinaryOp_new (&ops->merge_predecessors,
        LG_RpqPath_MergePredecessors, work->stored_set_type,
        work->temporary_set_type, work->stored_set_type, ops->stored_context_type,
        "LG_RpqPath_MergePredecessors", NULL) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Scalar_new (&ops->empty_temporary, work->temporary_set_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Scalar_setElement_UDT (ops->empty_temporary, &empty_predecessor_set) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Scalar_new (&ops->empty_stored, work->stored_set_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    LG_RpqPath_StoredSet empty_stored_set = { .count = 0, .allocation = NULL } ;
    info = GrB_Scalar_setElement_UDT (ops->empty_stored, &empty_stored_set) ;
    if (info != GrB_SUCCESS) return (info) ;

    return (GrB_SUCCESS) ;
}

/**
 * @brief Bind the current pool/label and create the second-product semiring.
 * @param[out] semiring Non-NULL address of a NULL handle receiving the semiring.
 * @param[out] multiply Non-NULL address of a NULL handle receiving its operator.
 * @param[out] scalar Non-NULL address of a NULL handle receiving the bound scalar.
 * @param[in] ops Borrowed initialized predecessor operators and monoid.
 * @param[in] pool Non-NULL traversal arena, alive through all products.
 * @param[in] label Current decomposition label index to store in predecessors.
 * @return GrB_SUCCESS or a GraphBLAS error.  All created handles, including
 *     partial setup on failure, belong to the caller.  Reuse them across
 *     iterations and free them after all traversal products have completed.
 */
static int LG_RpqPath_CreatePredecessorSemiring
(
    GrB_Semiring *semiring,
    GrB_BinaryOp *multiply,
    GrB_Scalar *scalar,
    const LG_RpqPath_Operators *ops,
    LG_RpqPath_BlockPool *pool,
    size_t label
)
{
    LG_RpqPath_PredecessorContext context = { .pool = pool, .label = label } ;
    int info = GrB_Scalar_new (scalar, ops->predecessor_context_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Scalar_setElement_UDT (*scalar, &context) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GxB_BinaryOp_new_IndexOp (multiply, ops->collect_predecessors,
        *scalar) ;
    if (info != GrB_SUCCESS) return (info) ;
    return (GrB_Semiring_new (semiring, ops->predecessor_union_monoid,
        *multiply)) ;
}

/**
 * @brief Bind the P-merging operator to a reusable new-buffer owner.
 * @param[out] merge Non-NULL address of a NULL handle receiving the operator.
 * @param[out] scalar Non-NULL address of a NULL handle receiving its bound scalar.
 * @param[in] ops Borrowed initialized accumulation operators and context type.
 * @param[in] owner Non-NULL initialized new-buffer owner, alive throughout
 *     traversal.  Transfer its allocations and reset it only after wait(P).
 * @return GrB_SUCCESS or a GraphBLAS error.  Created handles, including partial
 *     setup on failure, belong to the caller and are freed in traversal cleanup.
 */
static int LG_RpqPath_CreateStoredMerge
(
    GrB_BinaryOp *merge,
    GrB_Scalar *scalar,
    const LG_RpqPath_Operators *ops,
    LG_RpqPath_StoredOwner *owner
)
{
    LG_RpqPath_StoredContext context = { .owner = owner } ;
    int info = GrB_Scalar_new (scalar, ops->stored_context_type) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Scalar_setElement_UDT (*scalar, &context) ;
    if (info != GrB_SUCCESS) return (info) ;
    return (GxB_BinaryOp_new_IndexOp (merge, ops->merge_predecessors, *scalar)) ;
}

//------------------------------------------------------------------------------
// Stage 1: matrix traversal
//------------------------------------------------------------------------------

/**
 * @brief Build P to a fixed point without reconstructing paths.
 * @param[out] P_handle Receives owned materialized P, or NULL on error.
 * @param[in,out] P_owner Initialized empty owner receiving P's record buffers.
 *     After all readers finish, free P, then StoredRelease(P_owner).
 * @param[in] work Borrowed metadata/types, alive through reconstruction.
 * @param[in] roots Borrowed immutable Boolean QS x S relation (nr x ng).
 * @param[out] msg Optional LAGRAPH_MSG_LEN buffer, cleared on entry.
 * @return GrB_SUCCESS or allocation/GraphBLAS error; no partial P is returned.
 * Operators live for this traversal; H/C/next_frontier and temporary blocks live
 * for one iteration.  All intermediate storage is released on success or error.
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
    bool pool_allocation_failed = false ; // preserve failure across reset

    // P and frontier outlive a single iteration.  On success P passes to the
    // caller; frontier remains local and roots is borrowed throughout.
    GrB_Matrix P = NULL ;
    GrB_Matrix frontier = NULL ;
    bool frontier_active = false ;
    LG_RpqPath_StoredOwner stored_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;

    // The bound merger keeps this address for the entire traversal.  Each
    // completed iteration transfers its allocations to stored_owner.
    LG_RpqPath_StoredOwner next_stored_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;
    GrB_Scalar stored_context = NULL ;
    GrB_BinaryOp stored_merge = NULL ;
    LG_RpqPath_LabelOperators *label_ops = NULL ;
    LG_RpqPath_Operators ops = { 0 } ;

    // All temporary C values in this traversal will borrow this local pool.
    // Its ownership list is emptied and all blocks freed after each step.
    LG_RpqPath_BlockPool pool =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;

    // Setup: create shared operators, per-label bindings, P and the frontier.
    info = LG_RpqPath_CreateStateOperators (&ops, work, msg) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = LG_RpqPath_CreatePredecessorOperators (&ops, work, &pool) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = LG_RpqPath_CreateAccumulationOperators (&ops, work, &pool) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = LAGraph_Calloc ((void **) &label_ops, work->nl,
        sizeof (LG_RpqPath_LabelOperators), msg) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    for (size_t a = 0 ; a < work->nl ; a++)
    {
        if (work->A[a] == NULL || work->N[a] == NULL) continue ;
        info = LG_RpqPath_CreatePredecessorSemiring (
            &label_ops[a].semiring, &label_ops[a].multiply,
            &label_ops[a].context, &ops, &pool, a) ;
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }
    info = LG_RpqPath_CreateStoredMerge (&stored_merge, &stored_context,
        &ops, &next_stored_owner) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    info = GrB_Matrix_new (&P, work->stored_set_type, work->nr, work->ng) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Matrix_dup (&frontier, roots) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Matrix_reduce_BOOL (&frontier_active, NULL,
        GrB_LOR_MONOID_BOOL, frontier, NULL) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    while (frontier_active)
    {
        // 1. Create the matrices owned by this iteration.
        GrB_Matrix H = NULL ;
        GrB_Matrix C = NULL ;
        GrB_Matrix next_frontier = NULL ;

        bool updating_P = false ;

        info = GrB_Matrix_new (&H, work->state_set_type, work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_new (&C, work->temporary_set_type,
            work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_new (&next_frontier, GrB_BOOL, work->nr, work->ng) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // 2. Build C across labels, using the same input frontier for each.
        for (size_t a = 0 ; a < work->nl ; a++)
        {
            if (work->A[a] == NULL || work->N[a] == NULL) continue ;

            // H[p,j] = {q | N_a[q,p] && frontier[q,j]} for a direct query.
            // Inverse queries instead follow the original N_a rows.  REPLACE
            // discards the previous label's H values; frontier is only read.
            GrB_Descriptor nfa_direction = work->inverse ?
                GrB_DESC_R : GrB_DESC_RT0 ;
            info = GrB_mxm (H, NULL, NULL, ops.state_semiring,
                work->N[a], frontier, nfa_direction) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            // GraphBLAS resolves H's dependency without an intermediate wait.
            // Accumulate into C; H's column j identifies the predecessor vertex
            // even when the graph operand is transposed.
            info = GrB_Descriptor_set (ops.predecessor_product, GrB_INP1,
                work->reverse_graph[a] ? GrB_TRAN : GrB_DEFAULT) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            info = GrB_mxm (C, NULL, ops.predecessor_union, label_ops[a].semiring,
                H, work->A[a], ops.predecessor_product) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
        }

        // 3. Compute the new frontier against OLD P, restricting the output
        // to C's structure.  Keep explicit false flags; termination uses OR
        // of the values rather than the number of stored entries.
        info = GxB_Matrix_eWiseUnion (next_frontier, C, NULL,
            ops.has_new_predecessors, C, ops.empty_temporary, P, ops.empty_stored,
            GrB_DESC_RS) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        // Reduce to a C scalar before updating P.  In SuiteSparse:GraphBLAS
        // this resolves pending frontier values without a separate wait.
        info = GrB_Matrix_reduce_BOOL (&frontier_active, NULL,
            GrB_LOR_MONOID_BOOL, next_frontier, NULL) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // 4. Update P in place with independent deep copies, including P-only
        // cells.  eWiseAdd would bypass the merger at one-sided positions.
        updating_P = true ;
        info = GxB_Matrix_eWiseUnion (P, NULL, NULL, stored_merge,
            C, ops.empty_temporary, P, ops.empty_stored, NULL) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = GrB_Matrix_wait (P, GrB_MATERIALIZE) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = atomic_load (&next_stored_owner.error) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // 5. After wait(P), release old buffers and transfer the new ownership.
        LG_RpqPath_StoredRelease (&stored_owner) ;
        atomic_store (&stored_owner.allocations,
            atomic_exchange (&next_stored_owner.allocations, NULL)) ;
        updating_P = false ;

        // Transfer the frontier; cleanup must not free the next input.
        GrB_free (&frontier) ;
        frontier = next_frontier ;
        next_frontier = NULL ;

iteration_cleanup:
        // 6. On success, the frontier reduction and P wait have finished all
        // readers of old P and C.  Only failures need extra cleanup waits.
        // Preserve the first error and check pool.error before resetting it.
        if (info != GrB_SUCCESS && next_frontier != NULL)
        {
            int cleanup_info = GrB_Matrix_wait (next_frontier, GrB_MATERIALIZE) ;
            if (info == GrB_SUCCESS) info = cleanup_info ;
        }
        if (info != GrB_SUCCESS && C != NULL)
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
        if (pool_info == GrB_OUT_OF_MEMORY) pool_allocation_failed = true ;
        if (info == GrB_SUCCESS) info = pool_info ;
        // H owns inline values; discard C's handles before resetting the pool.
        GrB_free (&H) ;
        GrB_free (&C) ;
        GrB_free (&next_frontier) ;
        LG_RpqPath_StoredRelease (&next_stored_owner) ;
        LG_RpqPath_PoolReset (&pool) ;
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }

    // Return P and its independent buffers for reconstruction.
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
    LG_RpqPath_StoredRelease (&next_stored_owner) ;
    GrB_free (&stored_merge) ;
    GrB_free (&stored_context) ;
    if (label_ops != NULL)
    {
        for (size_t a = 0 ; a < work->nl ; a++)
        {
            GrB_free (&label_ops[a].semiring) ;
            GrB_free (&label_ops[a].multiply) ;
            GrB_free (&label_ops[a].context) ;
        }
        LAGraph_Free ((void **) &label_ops, NULL) ;
    }
    LG_RpqPath_FreeOperators (&ops) ;
    LG_RpqPath_PoolDestroy (&pool) ;
    if (info == GrB_OUT_OF_MEMORY && pool_allocation_failed)
    {
        LG_ERROR_MSG ("unable to allocate an RPQ predecessor block") ;
    }
    else if (info != GrB_SUCCESS && (msg == NULL || msg[0] == '\0'))
    {
        LG_ERROR_MSG ("RPQ matrix traversal failed: info: %d", info) ;
    }
    return (info) ;
}

//------------------------------------------------------------------------------
// Stage 2: path reconstruction and semantics
//------------------------------------------------------------------------------

// One graph path, independent of the accepting run of the NFA.  length counts
// edges; elements owns exactly 2 * length + 1 integers in traversal order:
// vertex, label, vertex, ..., label, vertex.  A zero-edge path owns one vertex.
// The result has no pointers into P, roots, the temporary pool or DFS storage.
typedef LAGraph_RpqPath LG_RpqPath_Path ;

/**
 * @brief Free the result array and every owned path buffer.
 * @param[in,out] paths Array address; set to NULL.  NULL/already NULL is allowed.
 * @param[in] path_count Initialized entry count; ignored for a NULL array.
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
 * @brief Reserve the working backward prefix for length edges.
 * @param[in,out] reconstruction Owns the buffer, which may move.  Existing
 *     prefix elements are preserved; access the buffer through this state.
 * @param[in] length Required edge count, including zero; needs 2*length+1 slots.
 * @param[out] msg Optional LAGRAPH_MSG_LEN error buffer.
 * @return GrB_SUCCESS or allocation error; the old buffer survives failure.
 * Capacity starts at INITIAL_CAPACITY and grows by GROWTH_FACTOR.
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
 * @brief Save a distinct forward copy of the current backward prefix.
 * @param[in,out] reconstruction Owns a valid reverse_path of 2*length+1 slots
 *     and all saved paths, including after allocation failure.
 * @param[in] length Edge count in the prefix; may be zero.
 * @param[out] msg Optional LAGRAPH_MSG_LEN error buffer.
 * @return GrB_SUCCESS or allocation error.
 * A linear scan compares full vertex/label sequences, deduplicating NFA runs.
 * The working prefix stays unchanged; the saved path owns a separate buffer.
 */
static int LG_RpqPath_SavePath
(
    LG_RpqPath_Reconstruction *reconstruction,
    size_t length,
    char *msg
)
{
    if (reconstruction->count >= LG_RPQ_PATH_MAX_COUNT) return (GrB_SUCCESS) ;
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
 * @brief Decide whether a path prefix satisfies the selected semantics.
 * @param[in] path Alternating vertex/label prefix in either traversal order.
 *     During DFS it is backward; during final result filtering it is forward.
 * @param[in] length Number of edges; slots 0 through 2*length are valid.
 * @param[in] destination Final vertex in the query traversal direction.
 * @param[in] reconstruction Read-only saved forward paths, used by shortest.
 * @return True to accept this prefix and allow its extension.  Predicates do
 *     not modify results, cache minima, or maintain visited sets.
 */
typedef bool (*LG_RpqPath_Continue)
(
    const uint64_t *path,
    size_t length,
    GrB_Index destination,
    const LG_RpqPath_Reconstruction *reconstruction
) ;

// All paths permit every prefix; the shared DFS enforces the length bound.
static bool LG_RpqPath_ContinueAll
(
    const uint64_t *path,
    size_t length,
    GrB_Index destination,
    const LG_RpqPath_Reconstruction *reconstruction
)
{
    (void) path ;
    (void) length ;
    (void) destination ;
    (void) reconstruction ;
    return (true) ;
}

// The earlier prefix is already simple.  Scan it for the newly added vertex:
// O(length) per extension, O(length^2) along one path, without a visited set.
static bool LG_RpqPath_ContinueSimple
(
    const uint64_t *path,
    size_t length,
    GrB_Index destination,
    const LG_RpqPath_Reconstruction *reconstruction
)
{
    (void) destination ;
    (void) reconstruction ;
    for (size_t i = 0 ; i < length ; i++)
        if (path[2 * i] == path[2 * length]) return (false) ;
    return (true) ;
}

// Compare the new directed labeled edge with each earlier edge.  Reversing
// the entire representation preserves equality of edge triples.
static bool LG_RpqPath_ContinueTrails
(
    const uint64_t *path,
    size_t length,
    GrB_Index destination,
    const LG_RpqPath_Reconstruction *reconstruction
)
{
    (void) destination ;
    (void) reconstruction ;
    if (length == 0) return (true) ;
    for (size_t i = 0 ; i + 1 < length ; i++)
    {
        if (path[2 * i] == path[2 * length - 2] &&
            path[2 * i + 1] == path[2 * length - 1] &&
            path[2 * i + 2] == path[2 * length]) return (false) ;
    }
    return (true) ;
}

// Scan saved paths directly, keeping ties and comparing only the same final
// vertex.  A later shorter path is handled by the common final filtering pass.
static bool LG_RpqPath_ContinueShortest
(
    const uint64_t *path,
    size_t length,
    GrB_Index destination,
    const LG_RpqPath_Reconstruction *reconstruction
)
{
    (void) path ;
    for (size_t k = 0 ; k < reconstruction->count ; k++)
    {
        const LG_RpqPath_Path *saved = &reconstruction->paths[k] ;
        if (saved->elements[2 * saved->length] == destination &&
            saved->length < length) return (false) ;
    }
    return (true) ;
}

/**
 * @brief Reconstruct paths through one shared backward recursive traversal.
 * @param[in] P Completed immutable predecessor matrix; borrowed.
 * @param[in] roots Immutable Boolean initial-configuration relation; borrowed.
 * @param[in] state Current NFA state, a valid row of P.
 * @param[in] vertex Current graph vertex, a valid column of P.
 * @param[in] length Number of edges in the current backward prefix.
 * @param[in,out] reconstruction Working prefix and independently owned paths.
 *     Slots through 2*length are valid; deeper slots may be overwritten.
 * @param[in] should_continue Pure semantics predicate, called before saving
 *     a root or descending.  The destination is reverse_path[0].
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error; buffers remain owned
 *     by reconstruction on failure.  The maximum path length is inclusive.
 */
static int LG_RpqPath_ReconstructCell
(
    GrB_Matrix P,
    GrB_Matrix roots,
    GrB_Index state,
    GrB_Index vertex,
    size_t length,
    LG_RpqPath_Reconstruction *reconstruction,
    LG_RpqPath_Continue should_continue,
    char *msg
)
{
    if (reconstruction->count >= LG_RPQ_PATH_MAX_COUNT) return (GrB_SUCCESS) ;
    if (!should_continue (reconstruction->reverse_path, length,
        reconstruction->reverse_path[0], reconstruction)) return (GrB_SUCCESS) ;

    bool root = false ;
    int info = GrB_Matrix_extractElement_BOOL (&root, roots, state, vertex) ;
    if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
    if (info == GrB_SUCCESS && root)
    {
        info = LG_RpqPath_SavePath (reconstruction, length, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    if (length >= LG_RPQ_PATH_MAX_LENGTH ||
        reconstruction->count >= LG_RPQ_PATH_MAX_COUNT) return (GrB_SUCCESS) ;

    LG_RpqPath_StoredSet predecessors = { .count = 0, .allocation = NULL } ;
    info = GrB_Matrix_extractElement_UDT (&predecessors, P, state, vertex) ;
    if (info == GrB_NO_VALUE) return (GrB_SUCCESS) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < predecessors.count ; k++)
    {
        if (reconstruction->count >= LG_RPQ_PATH_MAX_COUNT) break ;
        const LG_RpqPath_Predecessor *predecessor =
            &predecessors.allocation->records[k] ;
        info = LG_RpqPath_ReservePath (reconstruction, length + 1, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        reconstruction->reverse_path[2 * length + 1] = predecessor->label ;
        reconstruction->reverse_path[2 * length + 2] = predecessor->vertex ;
        info = LG_RpqPath_ReconstructCell (P, roots,
            predecessor->state, predecessor->vertex, length + 1,
            reconstruction, should_continue, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
    }
    return (GrB_SUCCESS) ;
}

/**
 * @brief Reconstruct paths from the completed matrix using one predicate.
 * @param[out] paths Non-NULL address receiving owned paths, or NULL on error.
 * @param[out] path_count Non-NULL address receiving their count, or zero.
 * @param[in] P Completed predecessor matrix, borrowed and never modified.
 * @param[in] roots Immutable initial-configuration relation, borrowed.
 * @param[in] QF Array of nqf accepting states; NULL allowed when nqf=0.
 * @param[in] nqf Number of accepting states, including duplicates.
 * @param[in] ng Number of graph vertices, equal to ncols(P).
 * @param[in] should_continue Predicate used for DFS and final result checking.
 * @param[out] msg Optional buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or a GraphBLAS/allocation error, with no partial result.
 * @note The final pass removes paths invalidated by later results (shortest).
 *     It uses the same predicate and scans results without cached minima.
 */
static int LG_RpqPath_Process
(
    LG_RpqPath_Path **paths,
    size_t *path_count,
    GrB_Matrix P,
    GrB_Matrix roots,
    const GrB_Index *QF,
    size_t nqf,
    GrB_Index ng,
    LG_RpqPath_Continue should_continue,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { 0 } ;
    int info = GrB_SUCCESS ;
    for (GrB_Index vertex = 0 ; vertex < ng &&
         reconstruction.count < LG_RPQ_PATH_MAX_COUNT ; vertex++)
    {
        for (size_t k = 0 ; k < nqf &&
             reconstruction.count < LG_RPQ_PATH_MAX_COUNT ; k++)
        {
            info = LG_RpqPath_ReservePath (&reconstruction, 0, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
            reconstruction.reverse_path[0] = vertex ;
            info = LG_RpqPath_ReconstructCell (P, roots,
                QF[k], vertex, 0, &reconstruction, should_continue, msg) ;
            if (info != GrB_SUCCESS) goto reconstruction_cleanup ;
        }
    }
    for (size_t k = 0 ; k < reconstruction.count ; )
    {
        LG_RpqPath_Path *path = &reconstruction.paths[k] ;
        if (should_continue (path->elements, path->length,
            path->elements[2 * path->length], &reconstruction))
        {
            k++ ;
            continue ;
        }
        LAGraph_Free ((void **) &path->elements, NULL) ;
        reconstruction.count-- ;
        memmove (path, path + 1,
            (reconstruction.count - k) * sizeof (LG_RpqPath_Path)) ;
    }
    *paths = reconstruction.paths ;
    *path_count = reconstruction.count ;
    reconstruction.paths = NULL ;

reconstruction_cleanup:
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    LAGraph_Free ((void **) &reconstruction.reverse_path, NULL) ;
    return (info) ;
}

//------------------------------------------------------------------------------
// Query lifecycle and public API
//------------------------------------------------------------------------------

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
 * @param[in] should_continue Non-NULL semantics predicate for reconstruction.
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
    LG_RpqPath_Continue should_continue,
    char *msg
)
{
    LG_CLEAR_MSG ;
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Workspace *work = NULL ;
    GrB_Matrix P = NULL, roots = NULL ;
    LG_RpqPath_StoredOwner P_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;
    int info = LG_RpqPath_Init (&work, R, inverse_labels, nl,
        G, inverse, msg) ;
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

    // Stage 2: the shared reconstruction only reads P and roots.  Their
    // storage remains live until reconstruction and result filtering finish.
    info = LG_RpqPath_Process (paths, path_count, P, roots, QF, nqf,
        work->ng, should_continue, msg) ;

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
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ContinueAll, msg)) ;
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
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ContinueSimple, msg)) ;
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
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ContinueTrails, msg)) ;
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
        QS, nqs, QF, nqf, G, S, ns, inverse, LG_RpqPath_ContinueShortest, msg)) ;
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

//------------------------------------------------------------------------------
// LAGraph_2RpqPath.c: regular path enumeration through predecessor matrices
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause
//
// Query lifecycle: initialize metadata, build P, reconstruct paths, clean up.
// The matrix stage uses a Boolean frontier M.  For each label a:
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
#include "LG_RpqPath_profile.h"

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
    LG_RpqPath_Profile *profile ;
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
    LG_RpqPath_ProfileAdd (pool->profile, LG_RPQ_temp_allocations, 1) ;
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
 *     On success, P has copied new triples into persistent blocks.  Read pool->error before reset.
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
    uint64_t written = 0, duplicates = 0 ;

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
                if (order == 0) duplicates++ ;
                if (order >= 0)
                {
                    LG_RpqPath_TemporaryAdvance (&right_block, &right_index) ;
                }
            }
            written++ ;
            if (!LG_RpqPath_TemporaryAppend (&result, &tail, record))
            {
                // Partial output remains in the arena until iteration reset.
                result.head = NULL ;
                break ;
            }
        }
    }
    LG_RpqPath_ProfileAdd (result.pool->profile, LG_RPQ_union_calls, 1) ;
    LG_RpqPath_ProfileAdd (result.pool->profile, LG_RPQ_union_input_records, written + duplicates) ;
    LG_RpqPath_ProfileAdd (result.pool->profile, LG_RPQ_union_duplicates, duplicates) ;
    LG_RpqPath_ProfileAdd (result.pool->profile, LG_RPQ_temp_records_written, written) ;
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
    LG_RpqPath_ProfileAdd (context->pool->profile, LG_RPQ_product_calls, 1) ;
    size_t produced = *(const bool *) y ? states->count : 0 ;
    LG_RpqPath_ProfileAdd (context->pool->profile, LG_RPQ_product_records, produced) ;
    LG_RpqPath_ProfileAdd (context->pool->profile, LG_RPQ_temp_records_written, produced) ;
    *(LG_RpqPath_TemporarySet *) z = result ;
}

//------------------------------------------------------------------------------
// Stored predecessor sets (P): ownership and operations
//------------------------------------------------------------------------------

// Each cell is an immutable chain of iteration deltas.  A new block contains
// only newly discovered triples and points to the previous head.  The separate
// allocation list owns all blocks until reconstruction finishes; GraphBLAS
// copies handles without managing the pointed-to memory.
typedef struct LG_RpqPath_StoredAllocation
{
    size_t count ;
    const struct LG_RpqPath_StoredAllocation *previous ;
    struct LG_RpqPath_StoredAllocation *allocation_next ;
    LG_RpqPath_Predecessor records [] ;
}
LG_RpqPath_StoredAllocation ;

// P values refer to ordinary heap allocations, never to the temporary arena.
// count is the total across the chain.  Each block is sorted, not the chain.
// The 128-bit Bloom filter covers the whole set; positives need exact lookup.
typedef struct
{
    size_t count ;
    LG_RpqPath_StoredAllocation *allocation ; // NULL denotes the empty set
    uint64_t bloom [2] ;
}
LG_RpqPath_StoredSet ;

// Callbacks may allocate concurrently.  They only prepend to this owner list;
// nothing is removed or freed until all callbacks have completed.  This is
// independent of the unchanged fixed-block pool used by temporary C values.
typedef struct
{
    _Atomic (LG_RpqPath_StoredAllocation *) allocations ;
    atomic_int error ;
    LG_RpqPath_Profile *profile ;
}
LG_RpqPath_StoredOwner ;

// Bound scalar for P's mixed-type binary operator; indices are not needed.
typedef struct
{
    LG_RpqPath_StoredOwner *owner ;
}
LG_RpqPath_StoredContext ;

// Matrix snapshots run only after materialization, outside operation timers.
// kind: 0 BOOL, 1 H state sets, 2 C temporary sets, 3 P stored sets.
static int LG_RpqPath_ProfilePointerOrder (const void *a, const void *b)
{
    uintptr_t x = (uintptr_t) *(const void *const *) a ;
    uintptr_t y = (uintptr_t) *(const void *const *) b ;
    return (x > y) - (x < y) ;
}
static void LG_RpqPath_ProfileMatrix (LG_RpqPath_Profile *p,
    const char *name, GrB_Matrix matrix, int kind)
{
    if (p == NULL || matrix == NULL) return ;
    double start = LAGraph_WallClockTime () ;
    GrB_Index nvals = 0, rows = 0, cols = 0 ;
    size_t bytes = 0 ;
    int32_t format = 0, sparsity = 0 ;
    GxB_Iterator it = NULL ;
    void *value = NULL ;
    const void **blocks = NULL ;
    size_t block_count = 0, block_capacity = 0 ;
    uint64_t records = 0, nonempty = 0, max_records = 0, chain_sum = 0, chain_max = 0 ;
    int info = GrB_Matrix_nvals (&nvals, matrix) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GrB_Matrix_nrows (&rows, matrix) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GrB_Matrix_ncols (&cols, matrix) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GxB_Matrix_memoryUsage (&bytes, matrix) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GxB_Matrix_Option_get_INT32 (matrix, GxB_FORMAT, &format) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GxB_Matrix_Option_get_INT32 (matrix, GxB_SPARSITY_STATUS, &sparsity) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    size_t value_size = kind == 1 ? sizeof (LG_RpqPath_StateSet) + rows * sizeof (GrB_Index) :
        kind == 2 ? sizeof (LG_RpqPath_TemporarySet) : sizeof (LG_RpqPath_StoredSet) ;
    value = malloc (value_size) ;
    if (value == NULL) { info = GrB_OUT_OF_MEMORY ; goto snapshot_end ; }
    info = GxB_Iterator_new (&it) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    info = GxB_Matrix_Iterator_attach (it, matrix, NULL) ;
    if (info != GrB_SUCCESS) goto snapshot_end ;
    for (info = GxB_Matrix_Iterator_seek (it, 0) ; info == GrB_SUCCESS ;
         info = GxB_Matrix_Iterator_next (it))
    {
        uint64_t count = 0, chain = 0 ;
        if (kind == 0) count = GxB_Iterator_get_BOOL (it) ? 1 : 0 ;
        else
        {
            GxB_Iterator_get_UDT (it, value) ;
            if (kind == 1) count = ((LG_RpqPath_StateSet *) value)->count ;
            else if (kind == 2)
            {
                for (const LG_RpqPath_PredecessorBlock *b = ((LG_RpqPath_TemporarySet *) value)->head ;
                     b != NULL ; b = b->next)
                {
                    count += b->count ; chain++ ;
                    if (block_count == block_capacity)
                    {
                        if (block_capacity > SIZE_MAX / 2 / sizeof (*blocks))
                        { info = GrB_OUT_OF_MEMORY ; goto snapshot_end ; }
                        size_t cap = block_capacity == 0 ? 64 : 2 * block_capacity ;
                        const void **grown = realloc (blocks, cap * sizeof (*blocks)) ;
                        if (grown == NULL) { info = GrB_OUT_OF_MEMORY ; goto snapshot_end ; }
                        blocks = grown ; block_capacity = cap ;
                    }
                    blocks[block_count++] = b ;
                }
            }
            else
            {
                const LG_RpqPath_StoredSet *set = value ; count = set->count ;
                for (const LG_RpqPath_StoredAllocation *b = set->allocation ; b != NULL ; b = b->previous) chain++ ;
            }
        }
        records += count ; nonempty += count != 0 ;
        if (count > max_records) max_records = count ;
        chain_sum += chain ; if (chain > chain_max) chain_max = chain ;
    }
    if (info == GxB_EXHAUSTED) info = GrB_SUCCESS ;
snapshot_end: ;
    char key[96] ;
#define SNAP_U(suffix, n) do { snprintf (key, sizeof (key), "%s_%s", name, suffix) ; LG_RpqPath_ProfileU (p, key, n) ; } while (0)
    snprintf (key, sizeof (key), "%s_snapshot_status", name) ;
    LG_RpqPath_ProfileD (p, key, info) ;
    if (info == GrB_SUCCESS)
    {
        SNAP_U ("nvals", nvals) ; SNAP_U ("rows", rows) ; SNAP_U ("cols", cols) ;
        SNAP_U ("matrix_bytes", bytes) ; SNAP_U ("format", format) ; SNAP_U ("sparsity", sparsity) ;
        SNAP_U ("records", records) ; SNAP_U ("nonempty", nonempty) ; SNAP_U ("records_max", max_records) ;
        SNAP_U ("chain_sum", chain_sum) ; SNAP_U ("chain_max", chain_max) ;
        if (kind == 2)
        {
            if (block_count > 1) qsort (blocks, block_count, sizeof (*blocks), LG_RpqPath_ProfilePointerOrder) ;
            uint64_t unique = 0 ;
            for (size_t k = 0 ; k < block_count ; k++)
                if (k == 0 || blocks[k] != blocks[k-1]) unique++ ;
            SNAP_U ("reachable_blocks", unique) ;
            SNAP_U ("reachable_bytes", unique * sizeof (LG_RpqPath_PredecessorBlock)) ;
            SNAP_U ("snapshot_scratch_bytes", block_capacity * sizeof (*blocks) + value_size) ;
        }
    }
    else p->failed = true ;
#undef SNAP_U
    GrB_free (&it) ; free (value) ; free (blocks) ;
    double elapsed = 1000 * (LAGraph_WallClockTime () - start) ;
    p->stats_ms += elapsed ;
    snprintf (key, sizeof (key), "%s_snapshot_ms", name) ;
    LG_RpqPath_ProfileD (p, key, elapsed) ;
}
static void LG_RpqPath_ProfilePool (LG_RpqPath_Profile *p, LG_RpqPath_BlockPool *pool)
{
    if (p == NULL) return ;
    double start = LAGraph_WallClockTime () ;
    uint64_t count = 0, records = 0 ;
    for (const LG_RpqPath_PredecessorBlock *b = atomic_load (&pool->allocations) ;
         b != NULL ; b = b->allocation_next) { count++ ; records += b->count ; }
    LG_RpqPath_ProfileU (p, "pool_blocks", count) ;
    LG_RpqPath_ProfileU (p, "pool_bytes", count * sizeof (LG_RpqPath_PredecessorBlock)) ;
    LG_RpqPath_ProfileU (p, "pool_records", records) ;
    LG_RpqPath_ProfileU (p, "pool_slots", count * LG_RPQ_PATH_BLOCK_CAPACITY) ;
    p->stats_ms += 1000 * (LAGraph_WallClockTime () - start) ;
}
static void LG_RpqPath_ProfileStored (LG_RpqPath_Profile *p, LG_RpqPath_StoredOwner *owner,
    const LG_RpqPath_StoredAllocation *previous)
{
    if (p == NULL) return ;
    double start = LAGraph_WallClockTime () ;
    uint64_t count = 0, records = 0, new_count = 0, new_records = 0, min = UINT64_MAX, max = 0 ;
    uint64_t hist[8] = { 0 } ; bool fresh = true ;
    for (const LG_RpqPath_StoredAllocation *b = atomic_load (&owner->allocations) ;
         b != NULL ; b = b->allocation_next)
    {
        if (b == previous) fresh = false ;
        count++ ; records += b->count ;
        if (!fresh) continue ;
        new_count++ ; new_records += b->count ;
        if (b->count < min) min = b->count ;
        if (b->count > max) max = b->count ;
        size_t bucket = 0, limit = 1 ;
        while (bucket < 7 && b->count > limit) { bucket++ ; limit *= 4 ; }
        hist[bucket]++ ;
    }
    LG_RpqPath_ProfileU (p, "P_owned_blocks", count) ;
    LG_RpqPath_ProfileU (p, "P_owned_records", records) ;
    LG_RpqPath_ProfileU (p, "P_owned_bytes", count * sizeof (LG_RpqPath_StoredAllocation) + records * sizeof (LG_RpqPath_Predecessor)) ;
    LG_RpqPath_ProfileU (p, "P_new_blocks", new_count) ;
    LG_RpqPath_ProfileU (p, "P_new_records", new_records) ;
    LG_RpqPath_ProfileU (p, "P_new_block_min_records", new_count ? min : 0) ;
    LG_RpqPath_ProfileU (p, "P_new_block_max_records", max) ;
    LG_RpqPath_ProfileD (p, "P_new_block_mean_records", new_count ? (double) new_records / new_count : 0) ;
    for (size_t k = 0 ; k < 8 ; k++)
    {
        char key[64] ; snprintf (key, sizeof (key), "P_new_block_bucket_%zu", k) ;
        LG_RpqPath_ProfileU (p, key, hist[k]) ;
    }
    p->stats_ms += 1000 * (LAGraph_WallClockTime () - start) ;
}
static void LG_RpqPath_ProfileCounters (LG_RpqPath_Profile *p, bool reset)
{
    if (p == NULL) return ;
    for (int k = 0 ; k < LG_RPQ_COUNTER_COUNT ; k++)
    {
        uint64_t value = reset ? atomic_exchange (&p->counters[k], 0) : atomic_load (&p->counters[k]) ;
        LG_RpqPath_ProfileU (p, LG_RpqPath_CounterNames[k], value) ;
    }
}



/**
 * @brief Allocate one immutable delta block and register its query owner.
 *
 * @param[in,out] owner Non-NULL owner of the new P buffers.  Concurrent
 *     registrations are allowed; removal is deferred until callbacks finish.
 * @param[in] capacity Number of new triples to store in the block.
 * @param[out] result Receives the registered block, or NULL on failure.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes.
 * @return GrB_SUCCESS or an allocation error.  Registration happens before
 *     the handle can be given to GraphBLAS, so error cleanup never needs to
 *     discover ownership by reading a potentially failed output matrix.
 */
static int LG_RpqPath_StoredAllocate
(
    LG_RpqPath_StoredOwner *owner,
    size_t capacity,
    LG_RpqPath_StoredAllocation **result,
    char *msg
)
{
    *result = NULL ;
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
    LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_allocations, 1) ;
    LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_allocated_bytes, bytes) ;
    allocation->count = capacity ;
    allocation->previous = NULL ;
    // Only the new private node's link changes on a retry.  Existing nodes
    // remain immutable, and none can be freed while registration is active.
    LG_RpqPath_StoredAllocation *head = atomic_load (&owner->allocations) ;
    do
    {
        allocation->allocation_next = head ;
    }
    while (!atomic_compare_exchange_weak (&owner->allocations, &head,
        allocation)) ;
    *result = allocation ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Free all P buffers registered with an owner.
 *
 * @param[in,out] owner Non-NULL initialized owner.  Its list is cleared and
 *     error flag reset; calling again on an empty owner is safe.
 * @pre No callback, surviving matrix value or reconstruction uses the blocks.
 *     This owner is released only on query completion or traversal failure.
 */
static void LG_RpqPath_StoredRelease (LG_RpqPath_StoredOwner *owner)
{
    LG_RpqPath_StoredAllocation *allocation =
        atomic_exchange (&owner->allocations, NULL) ;
    while (allocation != NULL)
    {
        LG_RpqPath_StoredAllocation *next = allocation->allocation_next ;
        LAGraph_Free ((void **) &allocation, NULL) ;
        allocation = next ;
    }
    atomic_store (&owner->error, GrB_SUCCESS) ;
}

// SplitMix64 finalizer: unsigned arithmetic is intentional.  The filter is
// only a negative test; hash collisions never replace exact triple comparison.
static uint64_t LG_RpqPath_Hash (uint64_t x)
{
    x = (x ^ (x >> 30)) * UINT64_C (0xbf58476d1ce4e5b9) ;
    x = (x ^ (x >> 27)) * UINT64_C (0x94d049bb133111eb) ;
    return (x ^ (x >> 31)) ;
}

static void LG_RpqPath_BloomBits
(
    const LG_RpqPath_Predecessor *record,
    uint64_t bits [2]
)
{
    uint64_t h = LG_RpqPath_Hash (record->state +
        UINT64_C (0x9e3779b97f4a7c15)) ;
    h = LG_RpqPath_Hash (h ^ record->vertex) ;
    h = LG_RpqPath_Hash (h ^ (uint64_t) record->label) ;
    bits[0] = (UINT64_C (1) << (h & 63)) |
              (UINT64_C (1) << ((h >> 6) & 63)) ;
    bits[1] = (UINT64_C (1) << ((h >> 12) & 63)) |
              (UINT64_C (1) << ((h >> 18) & 63)) ;
}

/**
 * @brief Test membership using Bloom rejection, then binary search per block.
 * @param[in] stored Immutable P snapshot, including its cumulative filter.
 * @param[in] record Triple to find, compared in full on every Bloom positive.
 * @return True exactly when the triple occurs in one of the sorted blocks.
 */
static bool LG_RpqPath_StoredContains
(
    const LG_RpqPath_StoredSet *stored,
    const LG_RpqPath_Predecessor *record,
    LG_RpqPath_Profile *profile, bool merging
)
{
    int base = merging ? LG_RPQ_merge_checks : LG_RPQ_front_checks ;
    LG_RpqPath_ProfileAdd (profile, base, 1) ;
    uint64_t blocks = 0, comparisons = 0 ;
    uint64_t bits [2] ;
    LG_RpqPath_BloomBits (record, bits) ;
    if ((stored->bloom[0] & bits[0]) != bits[0] ||
        (stored->bloom[1] & bits[1]) != bits[1])
    { LG_RpqPath_ProfileAdd (profile, base + 1, 1) ; return (false) ; }

    for (const LG_RpqPath_StoredAllocation *block = stored->allocation ;
         block != NULL ; block = block->previous)
    {
        blocks++ ;
        size_t low = 0, high = block->count ;
        while (low < high)
        {
            size_t mid = low + (high - low) / 2 ;
            int order = LG_RpqPath_ComparePredecessors (
                record, &block->records[mid]) ;
            comparisons++ ;
            if (order == 0)
            {
                LG_RpqPath_ProfileAdd (profile, base + 3, 1) ;
                LG_RpqPath_ProfileAdd (profile, base + 4, blocks) ;
                LG_RpqPath_ProfileAdd (profile, base + 5, comparisons) ;
                return (true) ;
            }
            if (order < 0) high = mid ;
            else low = mid + 1 ;
        }
    }
    LG_RpqPath_ProfileAdd (profile, base + 2, 1) ;
    LG_RpqPath_ProfileAdd (profile, base + 4, blocks) ;
    LG_RpqPath_ProfileAdd (profile, base + 5, comparisons) ;
    return (false) ;
}

/**
 * @brief Return one Boolean per cell, stopping at the first new C triple.
 * @param[out] z Boolean GraphBLAS result.
 * @param[in] x Sorted temporary C set, or the empty substitute scalar.
 * @param[in] y Immutable P snapshot, or the empty substitute scalar.
 */
static void LG_RpqPath_HasNewPredecessors (void *z, const void *x, const void *y)
{
    const LG_RpqPath_TemporarySet *temporary = x ;
    const LG_RpqPath_StoredSet *stored = y ;
    for (const LG_RpqPath_PredecessorBlock *block = temporary->head ;
         block != NULL ; block = block->next)
    {
        for (size_t k = 0 ; k < block->count ; k++)
        {
            if (!LG_RpqPath_StoredContains (stored, &block->records[k], temporary->pool->profile, false))
            {
                *(bool *) z = true ;
                return ;
            }
        }
    }
    *(bool *) z = false ;
}

/**
 * @brief Prepend one block containing C minus old P, sharing the old chain.
 * @param[in] stored Immutable P snapshot; globally sorted order is unnecessary.
 * @param[in] temporary Sorted distinct C records; owns no persistent memory.
 * @param[in,out] owner Query owner of all persistent delta blocks.
 * @param[out] result Updated handle, or the unchanged handle for an empty delta.
 * @param[out] msg Optional allocation error message.
 * @return GrB_SUCCESS or an allocation/size error; old blocks never change.
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
    *result = *stored ;
    size_t added = 0, incoming = 0 ;
    // Count first so duplicate-heavy updates do not reserve space for old
    // triples.  Recheck against the same immutable snapshot when filling.
    for (const LG_RpqPath_PredecessorBlock *block = temporary->head ;
         block != NULL ; block = block->next)
    {
        for (size_t k = 0 ; k < block->count ; k++)
        {
            incoming++ ;
            if (LG_RpqPath_StoredContains (stored, &block->records[k], owner->profile, true)) continue ;
            if (added == SIZE_MAX - stored->count)
            {
                LG_ERROR_MSG ("stored predecessor count exceeds addressable memory") ;
                return (GrB_OUT_OF_MEMORY) ;
            }
            added++ ;
        }
    }
    LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_added_records, added) ;
    LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_duplicate_records, incoming - added) ;
    if (added == 0) return (GrB_SUCCESS) ;
    LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_changed_cells, 1) ;
    if (stored->count == 0) LG_RpqPath_ProfileAdd (owner->profile, LG_RPQ_p_new_cells, 1) ;

    LG_RpqPath_StoredAllocation *delta = NULL ;
    int info = LG_RpqPath_StoredAllocate (owner, added, &delta, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    delta->previous = stored->allocation ;
    size_t used = 0 ;
    for (const LG_RpqPath_PredecessorBlock *block = temporary->head ;
         block != NULL ; block = block->next)
    {
        for (size_t k = 0 ; k < block->count ; k++)
        {
            const LG_RpqPath_Predecessor *record = &block->records[k] ;
            if (LG_RpqPath_StoredContains (stored, record, owner->profile, true)) continue ;
            delta->records[used++] = *record ;
            uint64_t bits [2] ;
            LG_RpqPath_BloomBits (record, bits) ;
            result->bloom[0] |= bits[0] ;
            result->bloom[1] |= bits[1] ;
        }
    }
    result->count += added ;
    result->allocation = delta ;
    return (GrB_SUCCESS) ;
}

/**
 * @brief Extend an immutable P chain with one block of new C triples.
 *
 * @param[out] z StoredSet handle sharing old blocks and owning its new delta.
 * @param[in] x TemporarySet from C, or the empty substitute scalar.
 * @param[in] ix Row of x; unused because records contain all required fields.
 * @param[in] jx Column of x; unused.
 * @param[in] y StoredSet from the old P, or the empty substitute scalar.
 * @param[in] iy Row of y; unused.
 * @param[in] jy Column of y; unused.
 * @param[in] theta Non-NULL bound StoredContext with the query block owner.
 *
 * Used by eWiseUnion at every position of C union P, including P-only cells.
 * Only new records are copied; old blocks are shared, never modified or freed.
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

    // Arrays are owned by this workspace; the matrices they reference belong
    // to the caller, who supplies the graph and NFA traversal directions.
    GrB_Matrix *A ;                  // prepared graph decomposition
    GrB_Matrix *N ;                  // prepared NFA decomposition

    GrB_Type state_set_type ;        // H value: header and room for nr states
    GrB_Type temporary_set_type ;    // C value: handle to temporary blocks
    GrB_Type stored_set_type ;       // P value: immutable chain and Bloom filter

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
 * @param[in] nl Positive number of slots in R and G.
 * @param[in] G Borrowed graph decomposition, nl slots; absent labels may be NULL.
 * @param[out] msg Optional LAGRAPH_MSG_LEN buffer, cleared on entry.
 * @return GrB_SUCCESS or LAGraph/GraphBLAS error; partial setup is freed.
 * Each decomposition must contain a matrix.  Inputs remain alive for the query;
 * only handles are copied.  Query owns roots; Traverse owns
 * its working matrices.  Indices are zero-based.
 */
int LG_RpqPath_Init
(
    LG_RpqPath_Workspace **workspace,
    LAGraph_Graph *R,
    size_t nl,
    LAGraph_Graph *G,
    char *msg
)
{
    LG_CLEAR_MSG ;
    LG_RpqPath_Workspace *work = NULL ;

    *workspace = NULL ;

    LG_TRY (LAGraph_Calloc ((void **) &work, 1,
        sizeof (LG_RpqPath_Workspace), msg)) ;
    work->nl = nl ;
    LG_TRY (LAGraph_Calloc ((void **) &work->A, nl,
        sizeof (GrB_Matrix), msg)) ;
    LG_TRY (LAGraph_Calloc ((void **) &work->N, nl,
        sizeof (GrB_Matrix), msg)) ;

    // Prepare the graph decomposition and determine its vertex count.
    LG_TRY (LG_RpqPath_PrepareDecomposition (G, nl,
        work->A, &work->ng, msg)) ;

    // Prepare the NFA decomposition and determine its state count separately.
    LG_TRY (LG_RpqPath_PrepareDecomposition (R, nl,
        work->N, &work->nr, msg)) ;

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
    GrB_Descriptor state_product ;
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
    GrB_free (&ops->state_product) ;
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
    info = GrB_Descriptor_new (&ops->state_product) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Descriptor_set (ops->state_product, GrB_OUTP, GrB_REPLACE) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Descriptor_set (ops->state_product, GrB_INP0, GrB_TRAN) ;
    if (info != GrB_SUCCESS) goto state_cleanup ;
    info = GrB_Descriptor_set (ops->state_product,
        GxB_AxB_METHOD, GxB_DEFAULT) ;
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
 *     separately; this function creates its indexed operator and AUTO descriptor.
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
    info = GrB_Descriptor_new (&ops->predecessor_product) ;
    if (info != GrB_SUCCESS) return (info) ;
    info = GrB_Descriptor_set (ops->predecessor_product,
        GxB_AxB_METHOD, GxB_DEFAULT) ;
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
 *     the persistent block owner separately, before traversal starts.
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
 * @brief Bind the P-merging operator to its persistent query block owner.
 * @param[out] merge Non-NULL address of a NULL handle receiving the operator.
 * @param[out] scalar Non-NULL address of a NULL handle receiving its bound scalar.
 * @param[in] ops Borrowed initialized accumulation operators and context type.
 * @param[in] owner Non-NULL initialized owner, alive throughout traversal.
 *     Its blocks survive all iterations and are transferred for reconstruction.
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
    LG_RpqPath_Profile *profile,
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
    GrB_Index frontier_nvals = 0 ;
    LG_RpqPath_StoredOwner stored_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS), .profile = profile
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
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS), .profile = profile
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
        &ops, &stored_owner) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    LG_RPQ_CALL ("new_P", P, GrB_Matrix_new (&P, work->stored_set_type, work->nr, work->ng), traversal_cleanup) ;
    LG_RpqPath_ProfileMatrix (profile, "P", P, 3) ;
    LG_RPQ_CALL ("dup_frontier", frontier, GrB_Matrix_dup (&frontier, roots), traversal_cleanup) ;
    LG_RpqPath_ProfileMatrix (profile, "frontier", frontier, 0) ;
    info = GrB_Matrix_nvals (&frontier_nvals, frontier) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;

    while (frontier_nvals != 0)
    {
        double iteration_start = LG_RpqPath_ProfileClock (profile) ;
        double stats_before = profile == NULL ? 0 : profile->stats_ms ;
        const LG_RpqPath_StoredAllocation *previous_allocations = atomic_load (&stored_owner.allocations) ;
        if (profile != NULL) { profile->iteration++ ; profile->label = -1 ; }
        LG_RpqPath_ProfileEvent (profile, "begin") ;
        LG_RpqPath_ProfileMatrix (profile, "frontier", frontier, 0) ;
        LG_RpqPath_ProfileMatrix (profile, "P", P, 3) ;
        // 1. Create the matrices owned by this iteration.
        GrB_Matrix H = NULL ;
        GrB_Matrix C = NULL ;
        GrB_Matrix next_frontier = NULL ;

        bool updating_P = false ;

        LG_RPQ_CALL ("new_H", H, GrB_Matrix_new (&H, work->state_set_type, work->nr, work->ng), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "H", H, 1) ;
        LG_RPQ_CALL ("new_C", C, GrB_Matrix_new (&C, work->temporary_set_type,
            work->nr, work->ng), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "C", C, 2) ;
        LG_RPQ_CALL ("new_next_frontier", next_frontier, GrB_Matrix_new (&next_frontier, GrB_BOOL, work->nr, work->ng), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "next_frontier", next_frontier, 0) ;

        // 2. Build C across labels, using the same input frontier for each.
        for (size_t a = 0 ; a < work->nl ; a++)
        {
            if (profile != NULL) profile->label = (int64_t) a ;
            LG_RpqPath_ProfileEvent (profile, "label") ;
            if (work->A[a] == NULL || work->N[a] == NULL)
            { LG_RpqPath_ProfileText (profile, "skip", "missing_matrix") ; continue ; }

            // H[p,j] = {q | N_a[q,p] && frontier[q,j]}.  REPLACE discards
            // the previous label's H values; frontier is only read.
            LG_RPQ_CALL ("mxm1", H, GrB_mxm (H, NULL, NULL, ops.state_semiring,
                work->N[a], frontier, ops.state_product), iteration_cleanup) ;
            LG_RpqPath_ProfileMatrix (profile, "H", H, 1) ;
            // An inactive label contributes nothing.  Skip its product before
            // the backend prepares the graph operand for multiplication.
            GrB_Index h_nvals = 0 ;
            info = GrB_Matrix_nvals (&h_nvals, H) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;
            if (h_nvals == 0)
            { LG_RpqPath_ProfileText (profile, "skip", "empty_H") ; continue ; }
            // The caller supplies graph directions.  Use AUTO multiplication;
            // H's column j identifies the predecessor vertex.
            LG_RPQ_CALL ("mxm2", C, GrB_mxm (C, NULL, ops.predecessor_union, label_ops[a].semiring,
                H, work->A[a], ops.predecessor_product), iteration_cleanup) ;
            LG_RpqPath_ProfileMatrix (profile, "C", C, 2) ;
            LG_RpqPath_ProfilePool (profile, &pool) ;
        }

        if (profile != NULL) profile->label = -1 ;
        LG_RpqPath_ProfileEvent (profile, "products_done") ;
        LG_RpqPath_ProfileMatrix (profile, "C", C, 2) ;
        LG_RpqPath_ProfilePool (profile, &pool) ;
        // 3. Compute the new frontier against OLD P without a mask.  P-only
        // cells and unchanged candidates produce false; remove those entries
        // before this matrix is used by the next iteration's products.
        LG_RPQ_CALL ("front_union", next_frontier, GxB_Matrix_eWiseUnion (next_frontier, NULL, NULL,
            ops.has_new_predecessors, C, ops.empty_temporary, P, ops.empty_stored,
            GrB_DESC_R), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "next_frontier", next_frontier, 0) ;
        LG_RPQ_CALL ("front_select", next_frontier, GrB_Matrix_select_BOOL (next_frontier, NULL, NULL,
            GrB_VALUEEQ_BOOL, next_frontier, true, GrB_DESC_R), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "next_frontier", next_frontier, 0) ;
        // Selection leaves only true entries, so nvals is the termination
        // test.  It also resolves pending entries before P is updated.
        info = GrB_Matrix_nvals (&frontier_nvals, next_frontier) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // 4. Extend P with one delta block per changed cell.  P-only cells
        // reuse their old handles; eWiseUnion also converts C-only values.
        updating_P = true ;
        LG_RPQ_CALL ("P_merge", P, GxB_Matrix_eWiseUnion (P, NULL, NULL, stored_merge,
            C, ops.empty_temporary, P, ops.empty_stored, NULL), iteration_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "P", P, 3) ;
        info = GrB_Matrix_wait (P, GrB_MATERIALIZE) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;
        info = atomic_load (&stored_owner.error) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        LG_RpqPath_ProfileStored (profile, &stored_owner, previous_allocations) ;
        // 5. All persistent blocks stay query-owned for shared old chains.
        // The P wait allows this iteration's temporary C pool to be reset.
        updating_P = false ;

        // Transfer the frontier; cleanup must not free the next input.
        double free_front_start = LG_RpqPath_ProfileClock (profile) ;
        GrB_free (&frontier) ;
        if (profile != NULL)
        {
            LG_RpqPath_ProfileEvent (profile, "free_frontier") ;
            LG_RpqPath_ProfileD (profile, "total_ms", 1000 * (LAGraph_WallClockTime () - free_front_start)) ;
        }
        frontier = next_frontier ;
        next_frontier = NULL ;

iteration_cleanup: ;
        double cleanup_start = LG_RpqPath_ProfileClock (profile) ;
        LG_RpqPath_ProfileEvent (profile, "iteration_end") ;
        // 6. On success, the frontier nvals and P wait have finished all
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
            // A failed merge may leave partial handles in P.  Finish its
            // callbacks before resetting C's arena or releasing query blocks.
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
        LG_RpqPath_PoolReset (&pool) ;
        LG_RpqPath_ProfileCounters (profile, true) ;
        if (profile != NULL)
        {
            LG_RpqPath_ProfileEvent (profile, "iteration_end") ;
            LG_RpqPath_ProfileD (profile, "cleanup_ms", 1000 * (LAGraph_WallClockTime () - cleanup_start)) ;
            LG_RpqPath_ProfileD (profile, "iteration_ms", 1000 * (LAGraph_WallClockTime () - iteration_start)) ;
            LG_RpqPath_ProfileD (profile, "snapshots_ms", profile->stats_ms - stats_before) ;
            LG_RpqPath_ProfileD (profile, "status", info) ;
            LG_RpqPath_ProfileU (profile, "frontier_out", frontier_nvals) ;
            LG_RpqPath_ProfileFlush (profile) ;
        }
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }

    // Return P and all persistent delta blocks for reconstruction.
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

// Result paths share immutable prefix nodes.  One hidden result header owns
// the node blocks and descriptor array; neither nodes nor prefixes are freed
// separately.  No node interning is performed between different memo cells.
typedef LAGraph_RpqPath LG_RpqPath_Path ;
typedef LAGraph_RpqPathNode LG_RpqPath_Node ;

// Private metadata supports exact per-cell memo lookup and result deduplication.
// Public prefix nodes are immutable; there is no interning across NFA cells.
typedef struct LG_RpqPath_CachedNode
{
    LG_RpqPath_Node node ;
    uint64_t hash ;
    struct LG_RpqPath_CachedNode *hash_next, *output_next ;
}
LG_RpqPath_CachedNode ;

typedef struct LG_RpqPath_PathBlock
{
    struct LG_RpqPath_PathBlock *next ;
    size_t count ;
    LG_RpqPath_CachedNode nodes [64] ;
}
LG_RpqPath_PathBlock ;

typedef struct
{
    LG_RpqPath_PathBlock *blocks ;
    size_t capacity ;
    LG_RpqPath_Path paths [] ;
}
LG_RpqPath_Result ;

typedef struct LG_RpqPath_MemoCell LG_RpqPath_MemoCell ;
typedef struct LG_RpqPath_MemoEdge
{
    LG_RpqPath_MemoCell *source, *destination ;
    size_t label, cursor ;
    // Reentrant cycles leave new source entries for this invocation's loop.
    bool active ;
    struct LG_RpqPath_MemoEdge *dependent_next, *allocation_next ;
}
LG_RpqPath_MemoEdge ;

struct LG_RpqPath_MemoCell
{
    GrB_Index state, vertex ;
    const LG_RpqPath_Node **paths ;
    LG_RpqPath_CachedNode **index ;
    size_t count, capacity, distance ;
    bool loaded, scheduled, distance_queued ;
    LG_RpqPath_MemoEdge *dependents ;
    LG_RpqPath_MemoCell *load_next, *distance_next ;
} ;

typedef struct
{
    GrB_Matrix P, roots ;
    LG_RpqPath_Result *result ;
    LG_RpqPath_Path *paths ;
    size_t count ;
    LG_RpqPath_MemoCell **memo ;
    size_t memo_count, memo_capacity ;
    LG_RpqPath_MemoCell *load_head, *distance_head, *distance_tail ;
    LG_RpqPath_MemoEdge *edges ;
    LG_RpqPath_MemoCell *target ;    // accepting cell currently emitting results
    LG_RpqPath_CachedNode **output_index ;
    size_t output_capacity ;
    bool shortest ;
    LG_RpqPath_Profile *profile ;
}
LG_RpqPath_Reconstruction ;

// Cumulative progress, sampled at safe points in the single-threaded driver.
static void LG_RpqPath_ProfileReconstruction (LG_RpqPath_Reconstruction *work, bool force)
{
    LG_RpqPath_Profile *p = work->profile ;
    if (p == NULL || (!force && LAGraph_WallClockTime () < p->next_sample)) return ;
    double start = LAGraph_WallClockTime () ;
    p->next_sample = start + 0.1 ;
    LG_RpqPath_ProfileEvent (p, force ? "final" : "sample") ;
    p->iteration = ++p->samples ;
#define RU(n) LG_RpqPath_ProfileU (p, #n, p->n)
    RU(pairs) ; RU(propagate_calls) ; RU(active_returns) ; RU(max_depth) ;
    RU(reject_length) ; RU(reject_shortest) ; RU(reject_semantics) ; RU(accepted) ;
    RU(memo_attempts) ; RU(memo_duplicates) ; RU(prefixes) ; RU(prefix_max) ; RU(path_blocks) ;
    RU(publish_attempts) ; RU(publish_duplicates) ; RU(published) ;
    RU(published_length_sum) ; RU(published_length_max) ;
    RU(loaded_cells) ; RU(dependencies) ; RU(read_blocks) ; RU(read_records) ;
    RU(activate_steps) ; RU(visit_inserts) ; RU(visit_erases) ; RU(visited_count) ; RU(visited_capacity) ;
    RU(load_pending) ; RU(load_peak) ; RU(distance_pending) ; RU(distance_peak) ; RU(distance_relaxations) ; RU(targets) ;
#undef RU
    LG_RpqPath_ProfileU (p, "memo_cells", work->memo_count) ;
    LG_RpqPath_ProfileU (p, "answers_before_filter", p->published) ;
    LG_RpqPath_ProfileU (p, "answers", work->count) ;
    LG_RpqPath_ProfileU (p, "count_limit", p->count_limit) ;
    LG_RpqPath_ProfileD (p, "join_ms", p->join_ms) ;
    LG_RpqPath_ProfileD (p, "memo_ms", p->memo_ms) ;
    LG_RpqPath_ProfileD (p, "publish_ms", p->publish_ms) ;
    LG_RpqPath_ProfileD (p, "prepare_ms", p->prepare_ms) ;
    LG_RpqPath_ProfileD (p, "first_answer_ms", p->first_answer_ms) ;
    size_t memo_bytes = work->memo_capacity * sizeof (*work->memo) + work->memo_count * sizeof (LG_RpqPath_MemoCell) ;
    for (size_t k = 0 ; k < work->memo_capacity ; k++)
        if (work->memo[k] != NULL)
            memo_bytes += work->memo[k]->capacity * (sizeof (*work->memo[k]->paths) + sizeof (*work->memo[k]->index)) ;
    size_t result_bytes = work->result == NULL ? 0 : offsetof (LG_RpqPath_Result, paths) +
        work->result->capacity * sizeof (LG_RpqPath_Path) ;
    LG_RpqPath_ProfileU (p, "memo_bytes", memo_bytes) ;
    LG_RpqPath_ProfileU (p, "dependency_bytes", p->dependencies * sizeof (LG_RpqPath_MemoEdge)) ;
    LG_RpqPath_ProfileU (p, "node_bytes", p->path_blocks * sizeof (LG_RpqPath_PathBlock)) ;
    LG_RpqPath_ProfileU (p, "result_bytes", result_bytes) ;
    LG_RpqPath_ProfileU (p, "output_index_bytes", work->output_capacity * sizeof (*work->output_index)) ;
    LG_RpqPath_ProfileU (p, "visited_bytes", p->visited_bytes) ;
    LG_RpqPath_ProfileU (p, "profile_buffer_bytes", p->capacity) ;
    p->stats_ms += 1000 * (LAGraph_WallClockTime () - start) ;
    LG_RpqPath_ProfileFlush (p) ;
}

static LG_RpqPath_CachedNode *LG_RpqPath_NodeStorage (const LG_RpqPath_Node *node)
{
    // node is the first member of its pool-owned private allocation.
    return ((LG_RpqPath_CachedNode *) node) ;
}

static void LG_RpqPath_FreePaths (LG_RpqPath_Path **paths, size_t path_count)
{
    (void) path_count ;
    if (paths == NULL || *paths == NULL) return ;
    LG_RpqPath_Result *result = (LG_RpqPath_Result *)
        ((char *) *paths - offsetof (LG_RpqPath_Result, paths)) ;
    LG_RpqPath_PathBlock *block = result->blocks ;
    while (block != NULL)
    {
        LG_RpqPath_PathBlock *next = block->next ;
        LAGraph_Free ((void **) &block, NULL) ;
        block = next ;
    }
    LAGraph_Free ((void **) &result, NULL) ;
    *paths = NULL ;
}

static int LG_RpqPath_ReserveResults
(
    LG_RpqPath_Reconstruction *work,
    size_t needed,
    char *msg
)
{
    size_t old = work->result == NULL ? 0 : work->result->capacity ;
    if (needed <= old) return (GrB_SUCCESS) ;
    size_t capacity = old == 0 ? 16 : old ;
    const size_t max = (SIZE_MAX - offsetof (LG_RpqPath_Result, paths)) /
        sizeof (LG_RpqPath_Path) ;
    if (needed > max) return (GrB_OUT_OF_MEMORY) ;
    while (capacity < needed)
        capacity = capacity > max / 2 ? needed : 2 * capacity ;
    size_t bytes = offsetof (LG_RpqPath_Result, paths) +
        capacity * sizeof (LG_RpqPath_Path) ;
    size_t old_bytes = old == 0 ? 0 : offsetof (LG_RpqPath_Result, paths) +
        old * sizeof (LG_RpqPath_Path) ;
    int info = LAGraph_Realloc ((void **) &work->result, bytes, old_bytes, 1, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    if (old == 0) work->result->blocks = NULL ;
    work->result->capacity = capacity ;
    work->paths = work->result->paths ;
    return (GrB_SUCCESS) ;
}

static bool LG_RpqPath_EqualNodes
(
    const LG_RpqPath_Node *a,
    const LG_RpqPath_Node *b
)
{
    if (a == b) return (true) ;
    if (a == NULL || b == NULL || a->length != b->length) return (false) ;
    while (a != b)
    {
        if (a == NULL || b == NULL || a->vertex != b->vertex ||
            (a->prefix != NULL && a->label != b->label)) return (false) ;
        a = a->prefix ;
        b = b->prefix ;
    }
    return (true) ;
}

static size_t LG_RpqPath_MemoHash (GrB_Index state, GrB_Index vertex)
{
    return ((size_t) LG_RpqPath_Hash (LG_RpqPath_Hash (state +
        UINT64_C (0x9e3779b97f4a7c15)) ^ vertex)) ;
}

static LG_RpqPath_MemoCell *LG_RpqPath_MemoFind
(
    const LG_RpqPath_Reconstruction *work,
    GrB_Index state, GrB_Index vertex
)
{
    if (work->memo_capacity == 0) return (NULL) ;
    size_t slot = LG_RpqPath_MemoHash (state, vertex) & (work->memo_capacity - 1) ;
    while (work->memo[slot] != NULL)
    {
        LG_RpqPath_MemoCell *cell = work->memo[slot] ;
        if (cell->state == state && cell->vertex == vertex) return (cell) ;
        slot = (slot + 1) & (work->memo_capacity - 1) ;
    }
    return (NULL) ;
}

static int LG_RpqPath_MemoGet
(
    LG_RpqPath_Reconstruction *work,
    GrB_Index state, GrB_Index vertex,
    LG_RpqPath_MemoCell **cell,
    char *msg
)
{
    *cell = LG_RpqPath_MemoFind (work, state, vertex) ;
    if (*cell != NULL) return (GrB_SUCCESS) ;
    if (work->memo_count >= work->memo_capacity / 2)
    {
        if (work->memo_capacity > SIZE_MAX / 2 / sizeof (*work->memo))
            return (GrB_OUT_OF_MEMORY) ;
        size_t capacity = work->memo_capacity == 0 ? 16 : 2 * work->memo_capacity ;
        LG_RpqPath_MemoCell **table = NULL ;
        int info = LAGraph_Calloc ((void **) &table, capacity, sizeof (*table), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        for (size_t k = 0 ; k < work->memo_capacity ; k++)
        {
            LG_RpqPath_MemoCell *old = work->memo[k] ;
            if (old == NULL) continue ;
            size_t slot = LG_RpqPath_MemoHash (old->state, old->vertex) & (capacity - 1) ;
            while (table[slot] != NULL) slot = (slot + 1) & (capacity - 1) ;
            table[slot] = old ;
        }
        LAGraph_Free ((void **) &work->memo, NULL) ;
        work->memo = table ;
        work->memo_capacity = capacity ;
    }
    size_t slot = LG_RpqPath_MemoHash (state, vertex) & (work->memo_capacity - 1) ;
    while (work->memo[slot] != NULL)
    {
        if (work->memo[slot]->state == state && work->memo[slot]->vertex == vertex)
        {
            *cell = work->memo[slot] ;
            return (GrB_SUCCESS) ;
        }
        slot = (slot + 1) & (work->memo_capacity - 1) ;
    }
    int info = LAGraph_Calloc ((void **) cell, 1, sizeof (**cell), msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    (*cell)->state = state ;
    (*cell)->vertex = vertex ;
    (*cell)->distance = SIZE_MAX ;
    work->memo[slot] = *cell ;
    work->memo_count++ ;
    return (GrB_SUCCESS) ;
}

static int LG_RpqPath_MemoExtend
(
    LG_RpqPath_Reconstruction *work,
    LG_RpqPath_MemoCell *cell,
    const LG_RpqPath_Node *prefix,
    size_t label,
    char *msg
)
{
    LG_RpqPath_Profile *profile = work->profile ;
    if (profile != NULL) profile->memo_attempts++ ;
    uint64_t hash = LG_RpqPath_Hash (cell->vertex + UINT64_C (0x9e3779b97f4a7c15)) ;
    if (prefix != NULL) hash = LG_RpqPath_Hash (hash ^
        LG_RpqPath_NodeStorage (prefix)->hash ^ LG_RpqPath_Hash (label)) ;
    if (cell->capacity != 0)
    {
        for (LG_RpqPath_CachedNode *saved = cell->index[hash & (cell->capacity - 1)] ;
             saved != NULL ; saved = saved->hash_next)
        {
            if (saved->hash == hash && (prefix == NULL || saved->node.label == label) &&
                LG_RpqPath_EqualNodes (saved->node.prefix, prefix))
            { if (profile != NULL) profile->memo_duplicates++ ; return (GrB_SUCCESS) ; }
        }
    }
    if (cell->count == cell->capacity)
    {
        if (cell->capacity > SIZE_MAX / 2 / sizeof (*cell->paths))
            return (GrB_OUT_OF_MEMORY) ;
        size_t capacity = cell->capacity == 0 ? 4 : 2 * cell->capacity ;
        int info = LAGraph_Realloc ((void **) &cell->paths, capacity,
            cell->capacity, sizeof (*cell->paths), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        LG_RpqPath_CachedNode **index = NULL ;
        info = LAGraph_Calloc ((void **) &index, capacity, sizeof (*index), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        for (size_t k = 0 ; k < cell->count ; k++)
        {
            LG_RpqPath_CachedNode *node = LG_RpqPath_NodeStorage (cell->paths[k]) ;
            size_t slot = node->hash & (capacity - 1) ;
            node->hash_next = index[slot] ;
            index[slot] = node ;
        }
        LAGraph_Free ((void **) &cell->index, NULL) ;
        cell->index = index ;
        cell->capacity = capacity ;
    }
    int info = LG_RpqPath_ReserveResults (work, work->count + 1, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    LG_RpqPath_PathBlock *block = work->result->blocks ;
    if (block == NULL || block->count == 64)
    {
        LG_RpqPath_PathBlock *next = NULL ;
        info = LAGraph_Malloc ((void **) &next, 1, sizeof (*next), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        next->next = block ;
        next->count = 0 ;
        work->result->blocks = block = next ;
        if (profile != NULL) profile->path_blocks++ ;
    }
    size_t slot = hash & (cell->capacity - 1) ;
    LG_RpqPath_CachedNode *stored = &block->nodes[block->count++] ;
    *stored = (LG_RpqPath_CachedNode) { .node =
        { .prefix = prefix, .vertex = cell->vertex,
          .label = prefix == NULL ? 0 : label,
          .length = prefix == NULL ? 0 : prefix->length + 1 },
        .hash = hash, .hash_next = cell->index[slot] } ;
    cell->index[slot] = stored ;
    cell->paths[cell->count++] = &stored->node ;
    if (profile != NULL)
    { profile->prefixes++ ; if (cell->count > profile->prefix_max) profile->prefix_max = cell->count ; }
    return (GrB_SUCCESS) ;
}

static int LG_RpqPath_Publish
(
    LG_RpqPath_Reconstruction *work,
    const LG_RpqPath_Node *path,
    char *msg
)
{
    LG_RpqPath_Profile *profile = work->profile ;
    if (profile != NULL) profile->publish_attempts++ ;
    LG_RpqPath_CachedNode *node = LG_RpqPath_NodeStorage (path) ;
    if (work->output_capacity != 0)
    {
        for (LG_RpqPath_CachedNode *saved =
            work->output_index[node->hash & (work->output_capacity - 1)] ;
            saved != NULL ; saved = saved->output_next)
            if (saved->hash == node->hash && LG_RpqPath_EqualNodes (&saved->node, path))
                { if (profile != NULL) profile->publish_duplicates++ ; return (GrB_SUCCESS) ; }
    }
    if (work->count >= work->output_capacity)
    {
        if (work->output_capacity > SIZE_MAX / 2 / sizeof (*work->output_index))
            return (GrB_OUT_OF_MEMORY) ;
        size_t capacity = work->output_capacity == 0 ? 16 : 2 * work->output_capacity ;
        LG_RpqPath_CachedNode **index = NULL ;
        int info = LAGraph_Calloc ((void **) &index, capacity, sizeof (*index), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        for (size_t k = 0 ; k < work->count ; k++)
        {
            LG_RpqPath_CachedNode *saved = LG_RpqPath_NodeStorage (work->paths[k].tail) ;
            size_t slot = saved->hash & (capacity - 1) ;
            saved->output_next = index[slot] ;
            index[slot] = saved ;
        }
        LAGraph_Free ((void **) &work->output_index, NULL) ;
        work->output_index = index ;
        work->output_capacity = capacity ;
    }
    int info = LG_RpqPath_ReserveResults (work, work->count + 1, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    size_t slot = node->hash & (work->output_capacity - 1) ;
    node->output_next = work->output_index[slot] ;
    work->output_index[slot] = node ;
    work->paths[work->count++] = (LG_RpqPath_Path) { .length = path->length, .tail = path } ;
    if (profile != NULL)
    {
        if (profile->published++ == 0) profile->first_answer_ms = 1000 * (LAGraph_WallClockTime () - profile->start) ;
        profile->published_length_sum += path->length ;
        if (path->length > profile->published_length_max) profile->published_length_max = path->length ;
        if (work->count >= LG_RPQ_PATH_MAX_COUNT) profile->count_limit = true ;
    }
    return (GrB_SUCCESS) ;
}

// Path-local membership table, shared by simple vertices and trail edges.
// Keys are (vertex,0,0) or (from,label,to), never NFA configurations.  Linear
// probing with backward-shift deletion retains no tombstones between branches.
typedef struct
{
    uint64_t key [3] ;
    bool used ;
}
LG_RpqPath_VisitedEntry ;

typedef struct
{
    LG_RpqPath_VisitedEntry *entries ;
    size_t count, capacity ;
}
LG_RpqPath_Visited ;

static size_t LG_RpqPath_VisitHash (const uint64_t key [3])
{
    uint64_t h = LG_RpqPath_Hash (key[0] + UINT64_C (0x9e3779b97f4a7c15)) ;
    h = LG_RpqPath_Hash (h ^ key[1]) ;
    return ((size_t) LG_RpqPath_Hash (h ^ key[2])) ;
}

static size_t LG_RpqPath_VisitSlot
(
    const LG_RpqPath_Visited *set,
    const uint64_t key [3]
)
{
    size_t slot = LG_RpqPath_VisitHash (key) & (set->capacity - 1) ;
    while (set->entries[slot].used &&
        memcmp (set->entries[slot].key, key, 3 * sizeof (uint64_t)) != 0)
        slot = (slot + 1) & (set->capacity - 1) ;
    return (slot) ;
}

/** Insert a path-local key, reporting an existing key without changing it.
 * Growth keeps the load at most one half; allocation failure preserves set.
 */
static int LG_RpqPath_VisitInsert
(
    LG_RpqPath_Visited *set,
    const uint64_t key [3],
    bool *inserted,
    char *msg
)
{
    *inserted = false ;
    if (set->capacity != 0 &&
        set->entries[LG_RpqPath_VisitSlot (set, key)].used)
        return (GrB_SUCCESS) ;
    if (set->count >= set->capacity / 2)
    {
        if (set->capacity > SIZE_MAX / 2 / sizeof (LG_RpqPath_VisitedEntry))
        {
            LG_ERROR_MSG ("path membership table exceeds addressable memory") ;
            return (GrB_OUT_OF_MEMORY) ;
        }
        LG_RpqPath_Visited grown = { .capacity =
            set->capacity == 0 ? 16 : 2 * set->capacity } ;
        int info = LAGraph_Calloc ((void **) &grown.entries, grown.capacity,
            sizeof (LG_RpqPath_VisitedEntry), msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        for (size_t k = 0 ; k < set->capacity ; k++)
        {
            if (!set->entries[k].used) continue ;
            size_t slot = LG_RpqPath_VisitSlot (&grown, set->entries[k].key) ;
            grown.entries[slot] = set->entries[k] ;
        }
        grown.count = set->count ;
        LAGraph_Free ((void **) &set->entries, NULL) ;
        *set = grown ;
    }
    size_t slot = LG_RpqPath_VisitSlot (set, key) ;
    memcpy (set->entries[slot].key, key, 3 * sizeof (uint64_t)) ;
    set->entries[slot].used = true ;
    set->count++ ;
    *inserted = true ;
    return (GrB_SUCCESS) ;
}

// Remove a key when moving away from the active prefix.  Look up its slot
// again because previous prefix activations may have resized the table.
static void LG_RpqPath_VisitErase
(
    LG_RpqPath_Visited *set,
    const uint64_t key [3]
)
{
    size_t mask = set->capacity - 1 ;
    size_t hole = LG_RpqPath_VisitSlot (set, key) ;
    for (size_t slot = (hole + 1) & mask ; set->entries[slot].used ;
         slot = (slot + 1) & mask)
    {
        size_t home = LG_RpqPath_VisitHash (set->entries[slot].key) & mask ;
        if (((hole - home) & mask) < ((slot - home) & mask))
        {
            set->entries[hole] = set->entries[slot] ;
            hole = slot ;
        }
    }
    set->entries[hole].used = false ;
    set->count-- ;
}

// The active membership table follows immutable prefixes.  Moving between
// related prefixes removes/adds only their nonshared tails; a chain extension
// therefore does not rescan all its ancestors or copy a per-path hash table.
typedef struct
{
    LG_RpqPath_Visited visited ;
    const LG_RpqPath_Node *active ;
    bool edges ;
    LG_RpqPath_Profile *profile ;
}
LG_RpqPath_JoinContext ;

typedef int (*LG_RpqPath_JoinFn)
(
    const LG_RpqPath_Node *, const LG_RpqPath_MemoEdge *, void *, bool *, char *
) ;

static void LG_RpqPath_NodeKey
(
    const LG_RpqPath_Node *node, bool edges, uint64_t key [3]
)
{
    key[0] = edges ? node->prefix->vertex : node->vertex ;
    key[1] = edges ? node->label : 0 ;
    key[2] = edges ? node->vertex : 0 ;
}

static int LG_RpqPath_ActivatePrefix
(
    LG_RpqPath_JoinContext *context,
    const LG_RpqPath_Node *path,
    char *msg
)
{
    const LG_RpqPath_Node *old = context->active, *common = path ;
    uint64_t key [3] ;
    while (old != common)
    {
        if (common == NULL || (old != NULL && old->length >= common->length))
        {
            if (!context->edges || old->prefix != NULL)
            {
                LG_RpqPath_NodeKey (old, context->edges, key) ;
                LG_RpqPath_VisitErase (&context->visited, key) ;
                if (context->profile != NULL) context->profile->visit_erases++ ;
            }
            if (context->profile != NULL) context->profile->activate_steps++ ;
            old = old->prefix ;
        }
        else { if (context->profile != NULL) context->profile->activate_steps++ ; common = common->prefix ; }
    }
    for (const LG_RpqPath_Node *node = path ; node != common ; node = node->prefix)
    {
        if (context->profile != NULL) context->profile->activate_steps++ ;
        if (context->edges && node->prefix == NULL) continue ;
        LG_RpqPath_NodeKey (node, context->edges, key) ;
        bool inserted ;
        int info = LG_RpqPath_VisitInsert (&context->visited, key, &inserted, msg) ;
        if (info != GrB_SUCCESS) return (info) ;
        if (context->profile != NULL) context->profile->visit_inserts += inserted ;
    }
    if (context->profile != NULL)
    {
        context->profile->visited_count = context->visited.count ;
        context->profile->visited_capacity = context->visited.capacity ;
        context->profile->visited_bytes = context->visited.capacity * sizeof (LG_RpqPath_VisitedEntry) ;
    }
    context->active = path ;
    return (GrB_SUCCESS) ;
}

static int LG_RpqPath_JoinAll
(
    const LG_RpqPath_Node *prefix, const LG_RpqPath_MemoEdge *edge,
    void *context, bool *accept, char *msg
)
{
    (void) prefix ; (void) edge ; (void) context ; (void) msg ;
    *accept = true ;
    return (GrB_SUCCESS) ;
}

static int LG_RpqPath_JoinRestricted
(
    const LG_RpqPath_Node *prefix, const LG_RpqPath_MemoEdge *edge,
    void *state, bool *accept, char *msg
)
{
    LG_RpqPath_JoinContext *context = state ;
    int info = LG_RpqPath_ActivatePrefix (context, prefix, msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    uint64_t key [3] = { edge->destination->vertex, 0, 0 } ;
    if (context->edges)
    {
        key[0] = prefix->vertex ;
        key[1] = edge->label ;
        key[2] = edge->destination->vertex ;
    }
    *accept = context->visited.count == 0 ||
        !context->visited.entries[LG_RpqPath_VisitSlot (&context->visited, key)].used ;
    return (GrB_SUCCESS) ;
}

static void LG_RpqPath_RelaxDistance
(
    LG_RpqPath_Reconstruction *work, LG_RpqPath_MemoCell *cell, size_t distance
)
{
    if (!work->shortest || distance >= cell->distance) return ;
    cell->distance = distance ;
    if (work->profile != NULL) work->profile->distance_relaxations++ ;
    if (cell->distance_queued) return ;
    if (work->profile != NULL)
    {
        work->profile->distance_pending++ ;
        if (work->profile->distance_pending > work->profile->distance_peak)
            work->profile->distance_peak = work->profile->distance_pending ;
    }
    cell->distance_queued = true ;
    cell->distance_next = NULL ;
    if (work->distance_tail != NULL) work->distance_tail->distance_next = cell ;
    else work->distance_head = cell ;
    work->distance_tail = cell ;
}

// Load each cell's incoming predecessor blocks once.  Cyclic dependencies
// are registered as subscriptions, not followed recursively for each path.
static int LG_RpqPath_PrepareCell
(
    LG_RpqPath_Reconstruction *work, LG_RpqPath_MemoCell *target, char *msg
)
{
    if (target->loaded) return (GrB_SUCCESS) ;
    if (work->profile != NULL) { work->profile->load_pending++ ; if (work->profile->load_peak == 0) work->profile->load_peak = 1 ; }
    target->scheduled = true ;
    target->load_next = work->load_head ;
    work->load_head = target ;
    while (work->load_head != NULL)
    {
        LG_RpqPath_MemoCell *cell = work->load_head ;
        work->load_head = cell->load_next ;
        cell->scheduled = false ;
        bool root = false ;
        LG_RpqPath_StoredSet predecessors = { 0 } ;
        int info = GrB_Matrix_extractElement_BOOL (&root, work->roots,
            cell->state, cell->vertex) ;
        if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
        info = GrB_Matrix_extractElement_UDT (&predecessors, work->P,
            cell->state, cell->vertex) ;
        if (info != GrB_SUCCESS && info != GrB_NO_VALUE) return (info) ;
        cell->loaded = true ;
        if (work->profile != NULL) { work->profile->loaded_cells++ ; work->profile->load_pending-- ; }
        for (const LG_RpqPath_StoredAllocation *block = predecessors.allocation ;
             block != NULL ; block = block->previous)
        {
            if (work->profile != NULL) { work->profile->read_blocks++ ; work->profile->read_records += block->count ; }
            for (size_t k = 0 ; k < block->count ; k++)
            {
                const LG_RpqPath_Predecessor *record = &block->records[k] ;
                LG_RpqPath_MemoCell *source = NULL ;
                info = LG_RpqPath_MemoGet (work, record->state, record->vertex, &source, msg) ;
                if (info != GrB_SUCCESS) return (info) ;
                LG_RpqPath_MemoEdge *edge = NULL ;
                info = LAGraph_Calloc ((void **) &edge, 1, sizeof (*edge), msg) ;
                if (info != GrB_SUCCESS) return (info) ;
                *edge = (LG_RpqPath_MemoEdge) { .source = source, .destination = cell,
                    .label = record->label, .dependent_next = source->dependents,
                    .allocation_next = work->edges } ;
                work->edges = source->dependents = edge ;
                if (work->profile != NULL) work->profile->dependencies++ ;
                if (source->distance != SIZE_MAX)
                    LG_RpqPath_RelaxDistance (work, cell, source->distance + 1) ;
                if (!source->loaded && !source->scheduled)
                {
                    if (work->profile != NULL)
                    {
                        work->profile->load_pending++ ;
                        if (work->profile->load_pending > work->profile->load_peak) work->profile->load_peak = work->profile->load_pending ;
                    }
                    source->scheduled = true ;
                    source->load_next = work->load_head ;
                    work->load_head = source ;
                }
            }
        }
        if (work->profile != NULL && (work->profile->loaded_cells & 4095) == 0) LG_RpqPath_ProfileReconstruction (work, false) ;
        if (root)
        {
            LG_RpqPath_RelaxDistance (work, cell, 0) ;
            info = LG_RpqPath_MemoExtend (work, cell, NULL, 0, msg) ;
            if (info != GrB_SUCCESS) return (info) ;
        }
    }
    // Shortest uses context-independent minimum distances.  Dependencies are
    // settled before enumerating ties; positive edge lengths make them a DAG.
    while (work->distance_head != NULL)
    {
        LG_RpqPath_MemoCell *cell = work->distance_head ;
        work->distance_head = cell->distance_next ;
        if (work->distance_head == NULL) work->distance_tail = NULL ;
        cell->distance_queued = false ;
        if (work->profile != NULL) work->profile->distance_pending-- ;
        for (LG_RpqPath_MemoEdge *edge = cell->dependents ; edge != NULL ;
             edge = edge->dependent_next)
            LG_RpqPath_RelaxDistance (work, edge->destination, cell->distance + 1) ;
    }
    return (GrB_SUCCESS) ;
}

// Recursively consume each (dependency, source-prefix) pair exactly once.
// A new destination prefix is passed to its dependents immediately.  An edge
// already active on this call stack is not entered again: its outer loop will
// consume any source entries appended by the cycle before it returns.
static int LG_RpqPath_Propagate
(
    LG_RpqPath_Reconstruction *work, LG_RpqPath_MemoEdge *edge,
    LG_RpqPath_JoinFn join, void *context, char *msg
)
{
    LG_RpqPath_Profile *profile = work->profile ;
    if (profile != NULL) profile->propagate_calls++ ;
    if (edge->active)
    { if (profile != NULL) profile->active_returns++ ; return (GrB_SUCCESS) ; }
    if (profile != NULL) { profile->depth++ ; if (profile->depth > profile->max_depth) profile->max_depth = profile->depth ; }
    edge->active = true ;
    int info = GrB_SUCCESS ;
    while (edge->cursor < edge->source->count && work->count < LG_RPQ_PATH_MAX_COUNT)
    {
        // Cache vectors may move during recursion; immutable prefix nodes do not.
        const LG_RpqPath_Node *prefix = edge->source->paths[edge->cursor++] ;
        if (profile != NULL)
        {
            profile->pairs++ ;
            if ((profile->pairs & 4095) == 0) LG_RpqPath_ProfileReconstruction (work, false) ;
        }
        if (prefix->length >= LG_RPQ_PATH_MAX_LENGTH)
        { if (profile != NULL) profile->reject_length++ ; continue ; }
        if (work->shortest && prefix->length + 1 != edge->destination->distance)
        { if (profile != NULL) profile->reject_shortest++ ; continue ; }
        bool accept = false ;
        double timer = LG_RpqPath_ProfileClock (profile) ;
        info = join (prefix, edge, context, &accept, msg) ;
        if (profile != NULL) profile->join_ms += 1000 * (LAGraph_WallClockTime () - timer) ;
        if (info != GrB_SUCCESS) break ;
        if (!accept) { if (profile != NULL) profile->reject_semantics++ ; continue ; }
        if (profile != NULL) profile->accepted++ ;
        size_t count = edge->destination->count ;
        timer = LG_RpqPath_ProfileClock (profile) ;
        info = LG_RpqPath_MemoExtend (work, edge->destination, prefix, edge->label, msg) ;
        if (profile != NULL) profile->memo_ms += 1000 * (LAGraph_WallClockTime () - timer) ;
        if (info != GrB_SUCCESS) break ;
        if (count == edge->destination->count) continue ;
        if (edge->destination == work->target)
        {
            timer = LG_RpqPath_ProfileClock (profile) ;
            info = LG_RpqPath_Publish (work, edge->destination->paths[count], msg) ;
            if (profile != NULL) profile->publish_ms += 1000 * (LAGraph_WallClockTime () - timer) ;
            if (info != GrB_SUCCESS) break ;
        }
        for (LG_RpqPath_MemoEdge *next = edge->destination->dependents ; next != NULL &&
             work->count < LG_RPQ_PATH_MAX_COUNT ; next = next->dependent_next)
        {
            info = LG_RpqPath_Propagate (work, next, join, context, msg) ;
            if (info != GrB_SUCCESS) break ;
        }
        if (info != GrB_SUCCESS) break ;
    }
    if (profile != NULL) profile->depth-- ;
    edge->active = false ;
    return (info) ;
}

// Collect only columns present in accepting rows, including zero-edge roots.
// Sparse Wikidata dimensions must not cause one empty lookup per graph vertex.
static int LG_RpqPath_TargetColumns
(
    GrB_Matrix matrix, const GrB_Index *QF, size_t nqf, GrB_Index ng,
    GrB_Index **columns, GrB_Index *count, char *msg
)
{
    *columns = NULL ; *count = 0 ;
    if (nqf == 0) return (GrB_SUCCESS) ;
    GrB_Type type = NULL ;
    GrB_Matrix selected = NULL ;
    int info = GxB_Matrix_type (&type, matrix) ;
    if (info != GrB_SUCCESS) goto target_cleanup ;
    info = GrB_Matrix_new (&selected, type, nqf, ng) ;
    if (info != GrB_SUCCESS) goto target_cleanup ;
    info = GrB_Matrix_extract (selected, NULL, NULL, matrix, QF, nqf, GrB_ALL, ng, NULL) ;
    if (info != GrB_SUCCESS) goto target_cleanup ;
    info = GrB_Matrix_nvals (count, selected) ;
    if (info != GrB_SUCCESS || *count == 0) goto target_cleanup ;
    info = LAGraph_Malloc ((void **) columns, *count, sizeof (GrB_Index), msg) ;
    if (info != GrB_SUCCESS) goto target_cleanup ;
    info = type == GrB_BOOL ?
        GrB_Matrix_extractTuples_BOOL (NULL, *columns, NULL, count, selected) :
        GrB_Matrix_extractTuples_UDT (NULL, *columns, NULL, count, selected) ;
target_cleanup:
    GrB_free (&selected) ;
    return (info) ;
}

static int LG_RpqPath_CompareTargets (const void *a, const void *b)
{
    GrB_Index x = *(const GrB_Index *) a, y = *(const GrB_Index *) b ;
    return ((x > y) - (x < y)) ;
}

static int LG_RpqPath_GenerateTargets
(
    LG_RpqPath_Reconstruction *work, const GrB_Index *QF, size_t nqf,
    GrB_Index ng, LG_RpqPath_JoinFn join, void *context, char *msg
)
{
    GrB_Index *vertices = NULL, *roots = NULL, count = 0, root_count = 0 ;
    int info = LG_RpqPath_TargetColumns (work->P, QF, nqf, ng, &vertices, &count, msg) ;
    if (info != GrB_SUCCESS) goto generate_cleanup ;
    info = LG_RpqPath_TargetColumns (work->roots, QF, nqf, ng, &roots, &root_count, msg) ;
    if (info != GrB_SUCCESS) goto generate_cleanup ;
    if (root_count > SIZE_MAX / sizeof (GrB_Index) - count)
    { info = GrB_OUT_OF_MEMORY ; goto generate_cleanup ; }
    if (root_count != 0)
    {
        info = LAGraph_Realloc ((void **) &vertices, count + root_count, count,
            sizeof (GrB_Index), msg) ;
        if (info != GrB_SUCCESS) goto generate_cleanup ;
        memcpy (vertices + count, roots, root_count * sizeof (GrB_Index)) ;
        count += root_count ;
    }
    if (count > 1) qsort (vertices, count, sizeof (GrB_Index), LG_RpqPath_CompareTargets) ;
    for (GrB_Index i = 0 ; i < count && work->count < LG_RPQ_PATH_MAX_COUNT ; i++)
    {
        if (i != 0 && vertices[i] == vertices[i-1]) continue ;
        for (size_t k = 0 ; k < nqf && work->count < LG_RPQ_PATH_MAX_COUNT ; k++)
        {
            LG_RpqPath_MemoCell *target = NULL ;
            info = LG_RpqPath_MemoGet (work, QF[k], vertices[i], &target, msg) ;
            if (info != GrB_SUCCESS) goto generate_cleanup ;
            LG_RpqPath_MemoEdge *previous_edges = work->edges ;
            double prepare_start = LG_RpqPath_ProfileClock (work->profile) ;
            if (work->profile != NULL) work->profile->targets++ ;
            info = LG_RpqPath_PrepareCell (work, target, msg) ;
            if (work->profile != NULL) work->profile->prepare_ms += 1000 * (LAGraph_WallClockTime () - prepare_start) ;
            if (info != GrB_SUCCESS) goto generate_cleanup ;
            work->target = target ;
            for (size_t emitted = 0 ; emitted < target->count &&
                 work->count < LG_RPQ_PATH_MAX_COUNT ; emitted++)
            {
                info = LG_RpqPath_Publish (work, target->paths[emitted], msg) ;
                if (info != GrB_SUCCESS) goto generate_cleanup ;
            }
            // Newly registered dependencies replay existing source prefixes;
            // old dependencies were drained by the previous target.  Further
            // source additions reach them recursively, without a global scan.
            for (LG_RpqPath_MemoEdge *edge = work->edges ; edge != previous_edges &&
                 work->count < LG_RPQ_PATH_MAX_COUNT ; edge = edge->allocation_next)
            {
                info = LG_RpqPath_Propagate (work, edge, join, context, msg) ;
                if (info != GrB_SUCCESS) goto generate_cleanup ;
            }
        }
    }
generate_cleanup:
    LAGraph_Free ((void **) &vertices, NULL) ;
    LAGraph_Free ((void **) &roots, NULL) ;
    return (info) ;
}

static int LG_RpqPath_ReconstructAll
(
    LG_RpqPath_Reconstruction *work, const GrB_Index *QF, size_t nqf, GrB_Index ng, char *msg
)
{
    return (LG_RpqPath_GenerateTargets (work, QF, nqf, ng, LG_RpqPath_JoinAll, NULL, msg)) ;
}

static int LG_RpqPath_ReconstructSimple
(
    LG_RpqPath_Reconstruction *work, const GrB_Index *QF, size_t nqf, GrB_Index ng, char *msg
)
{
    LG_RpqPath_JoinContext context = { .profile = work->profile } ;
    int info = LG_RpqPath_GenerateTargets (work, QF, nqf, ng,
        LG_RpqPath_JoinRestricted, &context, msg) ;
    LAGraph_Free ((void **) &context.visited.entries, NULL) ;
    return (info) ;
}

static int LG_RpqPath_ReconstructTrails
(
    LG_RpqPath_Reconstruction *work, const GrB_Index *QF, size_t nqf, GrB_Index ng, char *msg
)
{
    LG_RpqPath_JoinContext context = { .edges = true, .profile = work->profile } ;
    int info = LG_RpqPath_GenerateTargets (work, QF, nqf, ng,
        LG_RpqPath_JoinRestricted, &context, msg) ;
    LAGraph_Free ((void **) &context.visited.entries, NULL) ;
    return (info) ;
}

typedef int (*LG_RpqPath_ReconstructFn)
(
    LG_RpqPath_Reconstruction *, const GrB_Index *, size_t, GrB_Index, char *
) ;

static int LG_RpqPath_ReconstructShortest
(
    LG_RpqPath_Reconstruction *reconstruction,
    const GrB_Index *QF, size_t nqf, GrB_Index ng, char *msg
)
{
    reconstruction->shortest = true ;
    int info = LG_RpqPath_GenerateTargets (reconstruction, QF, nqf, ng,
        LG_RpqPath_JoinAll, NULL, msg) ;
    if (info != GrB_SUCCESS) return (info) ;

    // Keep the original count-cap behavior: filter only after enumeration.
    // Results are grouped by endpoint, so minima and stable compaction take
    // two linear passes per group rather than scans over all saved paths.
    size_t kept = 0 ;
    for (size_t begin = 0 ; begin < reconstruction->count ; )
    {
        const LG_RpqPath_Path *first = &reconstruction->paths[begin] ;
        GrB_Index destination = first->tail->vertex ;
        size_t end = begin, best = SIZE_MAX ;
        while (end < reconstruction->count)
        {
            const LG_RpqPath_Path *path = &reconstruction->paths[end] ;
            if (path->tail->vertex != destination) break ;
            if (path->length < best) best = path->length ;
            end++ ;
        }
        for (size_t k = begin ; k < end ; k++)
        {
            LG_RpqPath_Path path = reconstruction->paths[k] ;
            if (path.length == best) reconstruction->paths[kept++] = path ;
        }
        begin = end ;
    }
    reconstruction->count = kept ;
    return (GrB_SUCCESS) ;
}

/** Own common reconstruction buffers; semantics drivers own their contexts.
 * Memo vectors are temporary; shared nodes belong to the returned array.
 * No result node refers to P, roots or the reconstruction stack.
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
    LG_RpqPath_ReconstructFn reconstruct,
    LG_RpqPath_Profile *profile,
    char *msg
)
{
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Reconstruction reconstruction = { .P = P, .roots = roots, .profile = profile } ;
    int info = reconstruct (&reconstruction, QF, nqf, ng, msg) ;
    LG_RpqPath_ProfileReconstruction (&reconstruction, true) ;
    if (info == GrB_SUCCESS)
    {
        *paths = reconstruction.paths ;
        *path_count = reconstruction.count ;
        reconstruction.paths = NULL ;
    }
    for (size_t k = 0 ; k < reconstruction.memo_capacity ; k++)
    {
        LG_RpqPath_MemoCell *cell = reconstruction.memo[k] ;
        if (cell == NULL) continue ;
        LAGraph_Free ((void **) &cell->paths, NULL) ;
        LAGraph_Free ((void **) &cell->index, NULL) ;
        LAGraph_Free ((void **) &cell, NULL) ;
    }
    LAGraph_Free ((void **) &reconstruction.memo, NULL) ;
    while (reconstruction.edges != NULL)
    {
        LG_RpqPath_MemoEdge *edge = reconstruction.edges ;
        reconstruction.edges = edge->allocation_next ;
        LAGraph_Free ((void **) &edge, NULL) ;
    }
    LAGraph_Free ((void **) &reconstruction.output_index, NULL) ;
    if (info == GrB_SUCCESS && reconstruction.count == 0)
    {
        // An empty result owns no public array, even if an intermediate
        // memo entry caused allocation of node storage.
        reconstruction.paths = *paths ;
        *paths = NULL ;
    }
    LG_RpqPath_FreePaths (&reconstruction.paths, reconstruction.count) ;
    return (info) ;
}

//------------------------------------------------------------------------------
// Query lifecycle and public API
//------------------------------------------------------------------------------

/**
 * @brief Own initialization, traversal and cleanup for any public query mode.
 * @param[out] paths Non-NULL address receiving an array owning shared nodes, or
 *     NULL on error/empty result.  Must not hold an unreleased array on entry.
 * @param[out] path_count Non-NULL address receiving the result count, or zero.
 * @param[in] R Borrowed NFA decomposition of nl possibly NULL label slots.
 * @param[in] nl Number of shared label slots; positive.
 * @param[in] QS Initial NFA state array; NULL allowed if nqs=0.
 * @param[in] nqs Number of entries in QS.
 * @param[in] QF Accepting NFA state array; NULL allowed if nqf=0.
 * @param[in] nqf Number of entries in QF.
 * @param[in] G Borrowed graph decomposition of nl possibly NULL label slots.
 * @param[in] S Source vertex array; NULL allowed if ns=0.
 * @param[in] ns Number of entries in S.
 * @param[in] reconstruct Non-NULL semantics-specific reconstruction driver.
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
    size_t nl,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *QF,
    size_t nqf,
    LAGraph_Graph *G,
    const GrB_Index *S,
    size_t ns,
    LG_RpqPath_ReconstructFn reconstruct,
    char *msg
)
{
    LG_CLEAR_MSG ;
    *paths = NULL ;
    *path_count = 0 ;
    LG_RpqPath_Profile profile_storage ;
    LG_RpqPath_Profile *profile = LG_RpqPath_ProfileOpen (&profile_storage) ;
    double stage_start = LG_RpqPath_ProfileClock (profile) ;
    LG_RpqPath_ProfileText (profile, "baseline", "fa40ffd3") ;
    LG_RpqPath_ProfileText (profile, "semantics", reconstruct == LG_RpqPath_ReconstructSimple ? "simple" :
        reconstruct == LG_RpqPath_ReconstructTrails ? "trails" : reconstruct == LG_RpqPath_ReconstructShortest ? "shortest" : "all") ;
    LG_RpqPath_ProfileU (profile, "labels", nl) ;
    LG_RpqPath_ProfileU (profile, "nqs", nqs) ; LG_RpqPath_ProfileU (profile, "nqf", nqf) ;
    LG_RpqPath_ProfileU (profile, "ns", ns) ;
    LG_RpqPath_ProfileU (profile, "max_length", LG_RPQ_PATH_MAX_LENGTH) ;
    LG_RpqPath_ProfileU (profile, "max_count", LG_RPQ_PATH_MAX_COUNT) ;
    int32_t threads = 0, jit = 0 ;
    if (profile != NULL)
    {
        GxB_Global_Option_get_INT32 (GxB_NTHREADS, &threads) ;
        GxB_Global_Option_get_INT32 (GxB_JIT_C_CONTROL, &jit) ;
        LG_RpqPath_ProfileU (profile, "threads", threads) ; LG_RpqPath_ProfileU (profile, "jit", jit) ;
    }
    LG_RpqPath_Workspace *work = NULL ;
    GrB_Matrix P = NULL, roots = NULL ;
    LG_RpqPath_StoredOwner P_owner =
    {
        .allocations = ATOMIC_VAR_INIT (NULL),
        .error = ATOMIC_VAR_INIT (GrB_SUCCESS)
    } ;
    int info = LG_RpqPath_Init (&work, R, nl, G, msg) ;
    if (info != GrB_SUCCESS) goto query_cleanup ;
    LG_RpqPath_ProfileU (profile, "vertices", work->ng) ;
    LG_RpqPath_ProfileU (profile, "states", work->nr) ;
    for (size_t a = 0 ; profile != NULL && a < nl ; a++)
    {
        profile->label = (int64_t) a ;
        LG_RpqPath_ProfileMatrix (profile, "N", work->N[a], 0) ;
        LG_RpqPath_ProfileMatrix (profile, "A", work->A[a], 0) ;
    }
    if (profile != NULL) profile->label = -1 ;
    LG_RPQ_CALL ("new_roots", roots,
        GrB_Matrix_new (&roots, GrB_BOOL, work->nr, work->ng), query_cleanup) ;
    if (nqs > 0 && ns > 0)
    {
        LG_RPQ_CALL ("assign_roots", roots, GrB_Matrix_assign_BOOL (roots, NULL, NULL, true,
            QS, nqs, S, ns, NULL), query_cleanup) ;
        LG_RpqPath_ProfileMatrix (profile, "roots", roots, 0) ;
    }

    if (profile != NULL)
    {
        LG_RpqPath_ProfileEvent (profile, "setup_end") ;
        LG_RpqPath_ProfileD (profile, "total_ms", 1000 * (LAGraph_WallClockTime () - stage_start)) ;
        profile->phase = "traverse" ; stage_start = LAGraph_WallClockTime () ;
    }
    // Stage 1: finish the matrix algorithm, regardless of path semantics.
    info = LG_RpqPath_Traverse (&P, &P_owner, work, roots, profile, msg) ;
    if (info != GrB_SUCCESS) goto query_cleanup ;

    if (profile != NULL)
    {
        LG_RpqPath_ProfileEvent (profile, "end") ;
        LG_RpqPath_ProfileD (profile, "total_ms", 1000 * (LAGraph_WallClockTime () - stage_start)) ;
        LG_RpqPath_ProfileU (profile, "iterations", profile->iteration) ;
        LG_RpqPath_ProfileFlush (profile) ;
        profile->phase = "reconstruct" ; profile->iteration = 0 ; stage_start = LAGraph_WallClockTime () ;
    }
    // Stage 2: the shared reconstruction only reads P and roots.  Their
    // storage remains live until reconstruction and result filtering finish.
    info = LG_RpqPath_Process (paths, path_count, P, roots, QF, nqf,
        work->ng, reconstruct, profile, msg) ;

query_cleanup:
    if (profile != NULL)
    {
        LG_RpqPath_ProfileEvent (profile, "end") ;
        LG_RpqPath_ProfileD (profile, "total_ms", 1000 * (LAGraph_WallClockTime () - stage_start)) ;
        profile->phase = "query" ; profile->iteration = 0 ;
    }
    stage_start = LG_RpqPath_ProfileClock (profile) ;
    GrB_free (&P) ;
    LG_RpqPath_StoredRelease (&P_owner) ;
    GrB_free (&roots) ;
    LG_RpqPath_Free (&work) ;
    if (profile != NULL)
    {
        LG_RpqPath_ProfileEvent (profile, "end") ;
        LG_RpqPath_ProfileD (profile, "cleanup_ms", 1000 * (LAGraph_WallClockTime () - stage_start)) ;
        LG_RpqPath_ProfileD (profile, "total_ms", 1000 * (LAGraph_WallClockTime () - profile->start)) ;
        LG_RpqPath_ProfileD (profile, "snapshot_ms", profile->stats_ms) ;
        LG_RpqPath_ProfileD (profile, "io_ms", profile->io_ms) ;
        LG_RpqPath_ProfileD (profile, "status", info) ;
        LG_RpqPath_ProfileU (profile, "paths", *path_count) ;
        LG_RpqPath_ProfileClose (profile) ;
    }
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
    return (LG_RpqPath_Query (paths, path_count, R, nl,
        QS, nqs, QF, nqf, G, S, ns, LG_RpqPath_ReconstructAll, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllSimple
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
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
    return (LG_RpqPath_Query (paths, path_count, R, nl,
        QS, nqs, QF, nqf, G, S, ns, LG_RpqPath_ReconstructSimple, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllTrails
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
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
    return (LG_RpqPath_Query (paths, path_count, R, nl,
        QS, nqs, QF, nqf, G, S, ns, LG_RpqPath_ReconstructTrails, msg)) ;
}

// See LAGraphX.h for the public contract and argument documentation.
int LAGraph_2RpqPath_AllShortestPaths
(
    LAGraph_RpqPath **paths,
    size_t *path_count,
    LAGraph_Graph *R,
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
    return (LG_RpqPath_Query (paths, path_count, R, nl,
        QS, nqs, QF, nqf, G, S, ns, LG_RpqPath_ReconstructShortest, msg)) ;
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

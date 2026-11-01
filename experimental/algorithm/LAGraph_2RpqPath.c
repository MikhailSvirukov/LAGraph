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
// Increments 1 through 3 prepare the traversal and its first multiplication.
// All owned matrices are local variables in LG_RpqPath_Traverse.
// Predecessor allocation, the second multiplication and reconstruction follow.
// The internal workspace is not yet a public path-result interface.
// Optimizations, including minor ones, require the user's prior approval.

// The input helpers own no memory; workspace cleanup is enabled before Init.
#define LG_FREE_WORK ;
#define LG_FREE_ALL LG_FREE_WORK

#include "LG_internal.h"
#include "LAGraphX.h"

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

// Block layout and allocation are introduced in the allocator increment.
// GraphBLAS copies this handle by value, not the blocks it will reference.
typedef struct LG_RpqPath_PredecessorBlock LG_RpqPath_PredecessorBlock ;

typedef struct
{
    LG_RpqPath_PredecessorBlock *head ;  // NULL denotes an empty temporary set
}
LG_RpqPath_TemporarySet ;

// P owns its records independently of the temporary blocks used by C.
// Appending records and deep copying their contents are implemented later.
typedef struct
{
    size_t count ;
    LG_RpqPath_Predecessor *records ;    // malloc/realloc storage; NULL if empty
}
LG_RpqPath_StoredSet ;

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
 *     This increment only validates these indices; QF is not retained.
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
 * QS, QF and S are validated but not retained.  Supply QS and S to Traverse
 * again when creating the local initial frontier.
 *
 * @return GrB_SUCCESS on success, otherwise a LAGraph/GraphBLAS error code;
 *     any partially allocated workspace is released before returning an error.
 * @note This function prepares metadata and value types only.  Traverse owns
 *     P, roots and the frontier locally, with H/C created inside its loop.
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
    // These sets are only validated here; Traverse receives QS and S directly.
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
 * @brief Set up local traversal matrices and the per-iteration lifecycle.
 *
 * @param[in] work Initialized metadata and value types from LG_RpqPath_Init.
 *     Borrowed for this call; the caller retains ownership of the context.
 * @param[in] QS Array of nqs initial NFA states, already validated by Init.
 *     NULL is allowed when nqs is zero; duplicates collapse in roots.
 * @param[in] nqs Number of entries in QS.
 * @param[in] S Array of ns source vertices, already validated by Init.
 *     NULL is allowed when ns is zero; duplicates collapse in roots.
 * @param[in] ns Number of entries in S.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.  Cleared on entry.
 *
 * @return GrB_SUCCESS if no product-graph step is needed, GrB_NOT_IMPLEMENTED
 *     after the first multiplication when the second product is required,
 *     or an error from a GraphBLAS operation.
 * @note This increment implements H = N^T x frontier (or N x frontier for
 *     inverse queries).  The second product, accumulation and reconstruction
 *     are still missing.  No paths are returned yet.  All owned matrices and
 *     operators are released before returning.
 */
int LG_RpqPath_Traverse
(
    LG_RpqPath_Workspace *work,
    const GrB_Index *QS,
    size_t nqs,
    const GrB_Index *S,
    size_t ns,
    char *msg
)
{
    LG_CLEAR_MSG ;
    int info = GrB_SUCCESS ;

    // These matrices outlive a single iteration, but belong to this call.
    // P accumulates predecessors; roots remains immutable for reconstruction.
    // frontier changes ownership when the next frontier replaces it below.
    GrB_Matrix P = NULL ;
    GrB_Matrix roots = NULL ;
    GrB_Matrix frontier = NULL ;
    GrB_Index frontier_nvals = 0 ;

    // The first product uses one query-specific semiring for all labels.
    // Operators are local to this traversal, just like its matrices.
    GrB_BinaryOp state_union = NULL ;
    GrB_Monoid state_union_monoid = NULL ;
    GxB_IndexBinaryOp collect_state = NULL ;
    GrB_BinaryOp state_multiply = NULL ;
    GrB_Semiring state_semiring = NULL ;
    GrB_Scalar state_capacity = NULL ;
    LG_RpqPath_StateSet *empty_state_set = NULL ;

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

    info = GrB_Matrix_new (&P, work->stored_set_type, work->nr, work->ng) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    info = GrB_Matrix_new (&roots, GrB_BOOL, work->nr, work->ng) ;
    if (info != GrB_SUCCESS) goto traversal_cleanup ;
    if (nqs > 0 && ns > 0)
    {
        info = GrB_Matrix_assign_BOOL (roots, NULL, NULL, true,
            QS, nqs, S, ns, NULL) ;
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }
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
            // Finish the product before its H values are consumed or freed.
            info = GrB_Matrix_wait (H, GrB_MATERIALIZE) ;
            if (info != GrB_SUCCESS) goto iteration_cleanup ;

            // TODO: C += H x G_a, including the label in every predecessor.
            // Stop here until the allocator and second product are implemented.
            info = GrB_NOT_IMPLEMENTED ;
            break ;
        }
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // TODO: Deep copy new C records into P.  Set next_frontier[p,i] only
        // if this union adds at least one previously absent predecessor.
        info = GrB_Matrix_nvals (&frontier_nvals, next_frontier) ;
        if (info != GrB_SUCCESS) goto iteration_cleanup ;

        // Release the old frontier, transfer the new handle, and clear its
        // former owner so iteration cleanup cannot free the next input.
        GrB_free (&frontier) ;
        frontier = next_frontier ;
        next_frontier = NULL ;

iteration_cleanup:
        // H owns its state sets inline; freeing H releases their storage too.
        // C still has no values.  When temporary blocks are added, complete
        // operations, copy into P and return the blocks here too.
        GrB_free (&H) ;
        GrB_free (&C) ;
        GrB_free (&next_frontier) ;
        if (info != GrB_SUCCESS) goto traversal_cleanup ;
    }

    // TODO: Reconstruct paths from local P and roots before releasing them.
traversal_cleanup:
    GrB_free (&frontier) ;
    GrB_free (&roots) ;
    // P is still empty.  Once populated, release its owned record arrays here
    // as well: GrB_free alone does not free pointers stored inside UDT values.
    GrB_free (&P) ;
    // Matrices have been released; their operators can now be released too.
    GrB_free (&state_semiring) ;
    GrB_free (&state_multiply) ;
    GrB_free (&collect_state) ;
    GrB_free (&state_union_monoid) ;
    GrB_free (&state_union) ;
    GrB_free (&state_capacity) ;
    LAGraph_Free ((void **) &empty_state_set, NULL) ;
    if (info == GrB_NOT_IMPLEMENTED)
    {
        LG_ERROR_MSG ("second RPQ multiplication is not implemented yet") ;
    }
    else if (info != GrB_SUCCESS)
    {
        LG_ERROR_MSG ("GraphBLAS failure during RPQ traversal: info: %d", info) ;
    }
    return (info) ;
}

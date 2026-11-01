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
// Increment 1 implements only preparation, ending before the traversal loop.
// The internal workspace is not yet a public path-result interface.

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

    GrB_Matrix frontier ;           // M: active (state, vertex) configurations
    GrB_Matrix roots ;              // immutable initial QS x S relation
    GrB_Index frontier_nvals ;      // actual initial frontier size

    // P and the per-iteration H/C matrices are introduced in the next increment.
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
 */
static void LG_RpqPath_Free (LG_RpqPath_Workspace **workspace)
{
    if (workspace == NULL || *workspace == NULL) return ;
    LG_RpqPath_Workspace *work = *workspace ;
    GrB_free (&work->frontier) ;
    GrB_free (&work->roots) ;
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
 * @param[in] nqs Number of entries in QS; duplicates collapse in the frontier.
 * @param[in] QF Array of nqf accepting NFA state indices; NULL allowed if nqf=0.
 *     This increment only validates these indices; QF is not retained.
 * @param[in] nqf Number of entries in QF; duplicates are allowed.
 * @param[in] G Graph decomposition: nl graph handles indexed by label.
 *     Individual entries may be NULL; at least one adjacency matrix must exist.
 * @param[in] S Array of ns source vertex indices; NULL allowed if ns=0.
 * @param[in] ns Number of entries in S; duplicates collapse in the frontier.
 * @param[in] inverse Reverse the whole query: traverse the NFA backwards and
 *     flip every label's graph direction (inverse XOR inverse_labels[a]).
 *     QS and QF are used as supplied; this function does not swap them.
 * @param[out] msg Optional error buffer of at least LAGRAPH_MSG_LEN bytes;
 *     may be NULL.  Cleared on entry.
 *
 * All indices are zero-based.  The initial frontier and immutable roots are
 * the Cartesian product QS x S.  Empty source/start/final sets are valid.
 * Input matrices are borrowed and must remain alive while the workspace is
 * used.  Input arrays are read during initialization; their contents are
 * copied into workspace arrays or GraphBLAS objects as needed.
 *
 * @return GrB_SUCCESS on success, otherwise a LAGraph/GraphBLAS error code;
 *     any partially allocated workspace is released before returning an error.
 * @note This increment stops before P/H/C allocation and the main traversal.
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
    // Accepting states will be consumed at the path-reconstruction stage.
    (void) QF ;
    (void) nqf ;
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

    // Seed precisely the Cartesian product QS x S.  Duplicates in either input
    // set collapse naturally.  Keep a separate copy of this relation: reaching
    // a root during reconstruction emits a path (possibly of length zero), but
    // must not discard additional paths through predecessors of that root.
    GRB_TRY (GrB_Matrix_new (&work->roots, GrB_BOOL, work->nr, work->ng)) ;
    if (nqs > 0 && ns > 0)
    {
        GRB_TRY (GrB_Matrix_assign_BOOL (work->roots, NULL, NULL, true,
            QS, nqs, S, ns, NULL)) ;
    }
    GRB_TRY (GrB_Matrix_dup (&work->frontier, work->roots)) ;
    GRB_TRY (GrB_Matrix_nvals (&work->frontier_nvals, work->frontier)) ;

    // End of increment 1.  The main loop and P/H/C allocation follow in the
    // next increments.  No multiplication or path reconstruction runs yet.
    *workspace = work ;
    return (GrB_SUCCESS) ;
}

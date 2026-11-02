//------------------------------------------------------------------------------
// test_2RpqPath: graph + NFA -> expected paths through the public query API
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause

#include <LAGraph_test.h>
#include <LAGraphX.h>

#define TEST_LABELS 3
#define EXPECTED_PATH_SLOTS 17
#define ARRAY_COUNT(a) (sizeof (a) / sizeof ((a)[0]))

// All diagrams and input arrays use zero-based indices.  Labels a, b, c map to
// 0, 1, 2.  [v] marks a graph source; -->q marks an initial NFA state;
// ((q)) marks an accepting state.  Arrows in diagrams show stored edge
// directions; inverse-query flags are stated explicitly where they apply.
typedef struct
{
    GrB_Index from ;
    size_t label ;
    GrB_Index to ;
}
TestEdge ;

typedef struct
{
    size_t length ;                 // number of edges
    uint64_t elements [EXPECTED_PATH_SLOTS] ;
}
ExpectedPath ;

// All four public query functions share their argument and ownership contract.
typedef int (*TestQueryFunction)
(
    LAGraph_RpqPath **paths, size_t *path_count,
    LAGraph_Graph *R, const bool *inverse_labels, size_t nl,
    const GrB_Index *QS, size_t nqs, const GrB_Index *QF, size_t nqf,
    LAGraph_Graph *G, const GrB_Index *S, size_t ns, bool inverse, char *msg
) ;

typedef struct
{
    GrB_Index graph_vertices, automaton_states ;
    const TestEdge *graph_edges, *automaton_edges ;
    size_t graph_edge_count, automaton_edge_count ;
    GrB_Index QS [4], QF [4], S [4] ;
    size_t nqs, nqf, ns ;
    bool inverse_labels [TEST_LABELS] ;
    bool inverse ;
    const ExpectedPath *expected ;
    size_t expected_count ;
    TestQueryFunction run ;          // NULL selects AllPaths for existing cases
}
TestQuery ;

static char msg [LAGRAPH_MSG_LEN] ;

/**
 * @brief Construct label matrices from the edges in a test's diagram.
 * @param[out] decomposition Array of TEST_LABELS owned graph handles.  Absent
 *     labels are NULL; label a always has a matrix, even for an empty graph,
 *     so its dimension is known.  Release handles with LAGraph_Delete.
 * @param[in] vertices Number of graph vertices or automaton states.
 * @param[in] edges Array of edge_count triples (source, label, destination);
 *     NULL allowed when edge_count=0.
 * @param[in] edge_count Number of stored edges.
 */
static void test_build_decomposition
(
    LAGraph_Graph *decomposition,
    GrB_Index vertices,
    const TestEdge *edges,
    size_t edge_count
)
{
    for (size_t a = 0 ; a < TEST_LABELS ; a++)
    {
        bool present = (a == 0) ;
        for (size_t k = 0 ; k < edge_count ; k++)
            present |= edges[k].label == a ;
        decomposition[a] = NULL ;
        if (!present) continue ;

        GrB_Matrix A = NULL ;
        TEST_ASSERT (GrB_Matrix_new (&A, GrB_BOOL,
            vertices, vertices) == GrB_SUCCESS) ;
        // This is an input requirement of LAGraph_CheckGraph, including 1x1.
        TEST_ASSERT (GrB_set (A, GrB_ROWMAJOR,
            GrB_STORAGE_ORIENTATION_HINT) == GrB_SUCCESS) ;
        for (size_t k = 0 ; k < edge_count ; k++)
        {
            if (edges[k].label != a) continue ;
            TEST_ASSERT (GrB_Matrix_setElement_BOOL (A, true,
                edges[k].from, edges[k].to) == GrB_SUCCESS) ;
        }
        TEST_ASSERT (LAGraph_New (&decomposition[a], &A,
            LAGraph_ADJACENCY_DIRECTED, msg) == GrB_SUCCESS) ;
    }
}

/**
 * @brief Run one graph/NFA pair as a black-box query.
 * @param[in] query Immutable diagram data and query parameters.
 * @param[out] paths Receives an owned public result array.
 * @param[out] count Receives its number of paths.
 * @note Initializes LAGraph and releases all input graphs before returning.
 *     The caller frees the results and finalizes LAGraph after checking them.
 */
static void test_run_query
(
    const TestQuery *query,
    LAGraph_RpqPath **paths,
    size_t *count
)
{
    TEST_ASSERT (LAGraph_Init (msg) == GrB_SUCCESS) ;
    LAGraph_Graph G [TEST_LABELS] = { NULL } ;
    LAGraph_Graph R [TEST_LABELS] = { NULL } ;
    test_build_decomposition (G, query->graph_vertices,
        query->graph_edges, query->graph_edge_count) ;
    test_build_decomposition (R, query->automaton_states,
        query->automaton_edges, query->automaton_edge_count) ;

    TestQueryFunction run = query->run == NULL ?
        LAGraph_2RpqPath_AllPaths : query->run ;
    int info = run (paths, count, R,
        query->inverse_labels, TEST_LABELS, query->QS, query->nqs,
        query->QF, query->nqf, G, query->S, query->ns, query->inverse, msg) ;
    TEST_ASSERT_ (info == GrB_SUCCESS, "RPQ query info=%d: %s", info, msg) ;
    for (size_t a = 0 ; a < TEST_LABELS ; a++)
    {
        TEST_CHECK (LAGraph_Delete (&G[a], msg) == GrB_SUCCESS) ;
        TEST_CHECK (LAGraph_Delete (&R[a], msg) == GrB_SUCCESS) ;
    }
}

/**
 * @brief Compare returned paths with the test's explicit expected set.
 * @param[in] query One graph/NFA fixture and its manually specified paths.
 * @note Output ordering is unspecified.  Every expected sequence must occur
 *     exactly once, and the total count must match, including empty results.
 */
static void test_check_query (const TestQuery *query)
{
    LAGraph_RpqPath *paths = NULL ;
    size_t count = 0 ;
    test_run_query (query, &paths, &count) ;
    TEST_CHECK_ (count == query->expected_count,
        "got %zu paths, expected %zu", count, query->expected_count) ;
    TEST_ASSERT ((count == 0) == (paths == NULL)) ;
    for (size_t k = 0 ; k < count ; k++)
        TEST_ASSERT (paths[k].elements != NULL) ;
    for (size_t j = 0 ; j < query->expected_count ; j++)
    {
        const ExpectedPath *expected = &query->expected[j] ;
        size_t matches = 0 ;
        for (size_t k = 0 ; k < count ; k++)
        {
            if (paths[k].length == expected->length &&
                memcmp (paths[k].elements, expected->elements,
                    (2 * expected->length + 1) * sizeof (uint64_t)) == 0)
                matches++ ;
        }
        TEST_CHECK_ (matches == 1,
            "expected path %zu occurs %zu times", j, matches) ;
    }
    TEST_CHECK (LAGraph_2RpqPath_FreePaths (&paths, count,
        msg) == GrB_SUCCESS) ;
    TEST_CHECK (paths == NULL) ;
    TEST_CHECK (LAGraph_Finalize (msg) == GrB_SUCCESS) ;
}

/*
 * Graph:  [0] -a-> 1 -b-> 2
 * NFA:   -->q0 -a-> q1 -b-> ((q2))
 *
 * Only the complete word ab is accepted.
 */
static void test_chain (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 1, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a       a
 *             +----> 1 ----+
 *             |   a       a|
 * Graph:    [0] ----> 2 ----+--> 4 -a-> 5
 *             |   a       a|
 *             +----> 3 ----+
 * NFA:     -->q0 -a-> q1 -a-> q2 -a-> ((q3))
 *
 * Three graph paths merge at vertex 4 and share their final edge.
 */
static void test_branching (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 0, 2 },
        { 0, 0, 3 },
        { 1, 0, 4 },
        { 2, 0, 4 },
        { 3, 0, 4 },
        { 4, 0, 5 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 0, 1, 0, 4, 0, 5 } },
        { 3, { 0, 0, 2, 0, 4, 0, 5 } },
        { 3, { 0, 0, 3, 0, 4, 0, 5 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 6, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a
 *             +----------> 3 -b-> 4
 * Graph:    [0] -a-> 1 -a-> 2 -a-> 3
 * NFA:          +--a--+
 *               v     |
 *           -->q0 ----+--b--> ((q1))
 *
 * The paths a b and a a a b reach the same accepting endpoint.
 * The longer branch must survive after the short branch has reached it.
 */
static void test_unequal_branches (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 3 },
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 3 },
        { 3, 1, 4 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 },
        { 0, 1, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 3, 1, 4 } },
        { 4, { 0, 0, 1, 0, 2, 0, 3, 1, 4 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 5, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a                     a
 * Graph:  [0] -----> 1       NFA: -->q0 -----> ((q1))
 *           +--b--->                 +--b--->
 *
 * Equal vertex sequences with different edge labels are different paths.
 */
static void test_parallel_labels (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 1, { 0, 1, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-> 1 -b-> 2
 *                   a       b
 * NFA:         +----> q1 ----+
 *           -->q0            +--> ((q3))
 *              +----> q2 ----+
 *                   a       b
 *
 * Two accepting NFA runs describe the same graph path; emit it once.
 */
static void test_nondeterministic_runs (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 0, 2 },
        { 1, 1, 3 },
        { 2, 1, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 1, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-> 1
 *                        a
 * NFA:    -->q0 ---------> ((q1))
 *              +---a-----> ((q2))
 *
 * QS={q0,q0}, QF={q1,q2,q2}, S={0,0}.
 * Different accepting states and repeated input entries must not duplicate paths.
 */
static void test_duplicate_accepting_states (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 0, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0, 0 }, .nqs = 2,
        .QF = { 1, 2, 2 }, .nqf = 3,
        .S = { 0, 0 }, .ns = 2,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-+
 *                +--> 2 -b-> 3
 *         [1] -a-+
 * NFA:   -->q0 -a-> q1 -b-> ((q2))
 *
 * Both source vertices contribute a complete path.
 */
static void test_multiple_sources (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 2 },
        { 1, 0, 2 },
        { 2, 1, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 2, 1, 3 } },
        { 2, { 1, 0, 2, 1, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0, 1 }, .ns = 2,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-> [1] -a-> 2
 *                  a
 * NFA:          +-----+
 *               v     |
 *           -->((q0))-+
 *
 * S={0,1}.  The empty paths at both roots are accepted.  Reaching root 1
 * while reconstructing a longer path must still allow continuing to root 0.
 */
static void test_continue_through_roots (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 }
    } ;
    const ExpectedPath expected [] =
    {
        { 0, { 0 } },
        { 0, { 1 } },
        { 1, { 0, 0, 1 } },
        { 1, { 1, 0, 2 } },
        { 2, { 0, 0, 1, 0, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 1,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0, 1 }, .ns = 2,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0]                  (no edges)
 * NFA:   -->((q0))             (no transitions)
 *
 * The sole result is the zero-edge path consisting of vertex 0.
 */
static void test_zero_length (void)
{
    const ExpectedPath expected [] =
    {
        { 0, { 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 1, .automaton_states = 1,
        .graph_edges = NULL, .graph_edge_count = 0,
        .automaton_edges = NULL,
        .automaton_edge_count = 0,
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -b-> 1
 * NFA:   -->q0 -c-> ((q1))
 *
 * The graph and NFA decompositions have no matching nonempty label slot.
 */
static void test_no_shared_label (void)
{
    const TestEdge graph [] =
    {
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 2, 1 }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = NULL,
        .expected_count = 0
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-> 1 -a-> 2
 * NFA:   -->q0 -a-> q1 -b-> ((q2))
 *
 * The graph supplies aa, but the NFA requires ab.  No path is accepted.
 */
static void test_rejected_word (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = NULL,
        .expected_count = 0
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:  [0] -a-> 1 <-b- 2
 * NFA:   -->q0 -a-> q1 -b-> ((q2))
 *
 * inverse_labels[b]=true.  The returned traversal is 0 -a-> 1 -b-> 2;
 * the label index remains b although its graph edge is traversed backwards.
 */
static void test_inverse_label (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 2, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 1, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .inverse_labels = { false, true, false },
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:   0 -a-> 1 -b-> [2]
 * NFA:   ((q0)) -a-> q1 -b-> q2 <-- initial
 *
 * inverse=true, QS={q2}, QF={q0}, S={2}.
 * The query traverses both decompositions backwards and returns 2 -b-> 1 -a-> 0.
 */
static void test_inverse_query (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 2, 1, 1, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 2 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 2 }, .ns = 1,
        .inverse = true,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:   0 -a-> 1 <-b- [2]
 * NFA:   ((q0)) -a-> q1 -b-> q2 <-- initial
 *
 * inverse=true and inverse_labels[b]=true: the two reversals cancel for b.
 * The returned traversal is 2 -b-> 1 -a-> 0.
 */
static void test_inverse_query_and_label (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 2, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 2, 1, 1, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 2 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 2 }, .ns = 1,
        .inverse_labels = { false, true, false },
        .inverse = true,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a
 * Graph:  [0] ----> 1
 *           ^      |
 *           +--b---+
 *           |
 *           +--c--> 2
 * NFA:   -->q0 -a-> q1 -b-> q2 -c-> ((q3))
 *
 * The accepted path 0 -a-> 1 -b-> 0 -c-> 2 revisits graph vertex 0.
 */
static void test_cycle_in_graph (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 },
        { 0, 2, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 2, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 0, 1, 1, 0, 2, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a
 * Graph:  [0] ----> 1
 *           ^      |
 *           +--b---+
 * NFA:   -->q0 -a-> q1 -b-> q2 -a-> ((q3))
 *
 * The accepted path traverses the same directed edge 0 -a-> 1 twice.
 * AllPaths allows repeated edges as well as repeated vertices.
 */
static void test_repeated_edge (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 0, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 0, 1, 1, 0, 0, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> 2 -a-> 3 -a-> 4 -a-> 5 -a-> 6 -a-> 7 -a-> 8
 * NFA:  -->q0 -a-> q1 -a-> q2 -a-> q3 -a-> q4 -a-> q5 -a-> q6 -a-> q7
 *                                                                           |
 *                                                                           a
 *                                                                           v
 *                                                                         ((q8))
 *
 * There is exactly one eight-edge path; all of its vertices and labels matter.
 */
static void test_long_chain (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 3 },
        { 3, 0, 4 },
        { 4, 0, 5 },
        { 5, 0, 6 },
        { 6, 0, 7 },
        { 7, 0, 8 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 3 },
        { 3, 0, 4 },
        { 4, 0, 5 },
        { 5, 0, 6 },
        { 6, 0, 7 },
        { 7, 0, 8 }
    } ;
    const ExpectedPath expected [] =
    {
        { 8, { 0, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6, 0, 7, 0, 8 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 9, .automaton_states = 9,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 8 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * a                         a
 * Graph:  [0] -a-> 1 <--+     NFA: -->((q0)) -a-> q1 <--+
 *                  +---+                         +----+
 *
 * The product graph has a reachable cycle, but q1 is not accepting and cannot
 * return to q0.  Only the zero-edge path at source 0 is a result.
 */
static void test_nonaccepting_cycle (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 0, { 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 *             a                         a
 * Graph:    +---+            NFA:      +---+
 *           v   |                     v   |
 *          [0]--+                 -->((q0))-+
 *
 * The documented default bound is 1024 edges, inclusive.
 * Expected paths: (0 -a-> 0)^k for every k=0,...,1024, exactly once each.
 * This explicit family also checks the zero-edge path, the last permitted
 * length, repeated traversal of a root and termination of the matrix phase.
 */
static void test_length_limit (void)
{
    const TestEdge graph [] = { { 0, 0, 0 } } ;
    const TestEdge automaton [] = { { 0, 0, 0 } } ;
    const TestQuery query =
    {
        .graph_vertices = 1, .automaton_states = 1,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1, .QF = { 0 }, .nqf = 1, .S = { 0 }, .ns = 1
    } ;
    LAGraph_RpqPath *paths = NULL ;
    size_t count = 0 ;
    test_run_query (&query, &paths, &count) ;
    TEST_CHECK_ (count == 1025, "got %zu paths, expected 1025", count) ;
    TEST_ASSERT (paths != NULL) ;
    bool seen [1025] = { false } ;
    for (size_t k = 0 ; k < count ; k++)
    {
        TEST_ASSERT (paths[k].length <= 1024) ;
        TEST_ASSERT (paths[k].elements != NULL) ;
        TEST_CHECK (!seen[paths[k].length]) ;
        seen[paths[k].length] = true ;
        bool matches = true ;
        for (size_t i = 0 ; i < 2 * paths[k].length + 1 ; i++)
            matches &= paths[k].elements[i] == 0 ;
        TEST_CHECK_ (matches, "incorrect path of length %zu", paths[k].length) ;
    }
    for (size_t length = 0 ; length <= 1024 ; length++)
        TEST_CHECK_ (seen[length], "missing path of length %zu", length) ;
    TEST_CHECK (LAGraph_2RpqPath_FreePaths (&paths, count,
        msg) == GrB_SUCCESS) ;
    TEST_CHECK (LAGraph_Finalize (msg) == GrB_SUCCESS) ;
}


/*
 * Graph: [0] -a-> 1 -b-> 2 -c-> 3
 *          ^      |
 *          +--b---+
 *          +-----------c-------> 3
 * NFA:  -->q0 -a-> q1 -b-> q2 -c-> ((q3))
 *
 * Simple: keep 0-a-1-b-2-c-3; reject 0-a-1-b-0-c-3, which repeats vertex 0.
 */
static void test_simple_repeated_vertex (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 },
        { 1, 1, 2 },
        { 0, 2, 3 },
        { 2, 2, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 2, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 0, 1, 1, 2, 2, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> [0]       [0] -b-> 1
 * NFA:  -->q0 -a-> q0        q0 -b-> ((q1))
 *
 * Simple: the a self-loop repeats vertex 0.  Only the direct b path remains.
 */
static void test_simple_self_loop (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 0 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 },
        { 0, 1, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 1, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> [0]
 * NFA:  -->q0 -a-> q1 -b-> ((q2))
 *
 * Simple: the NFA accepts ab, but its only graph path repeats its source.
 */
static void test_simple_closed_path (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = NULL,
        .expected_count = 0,
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1        [0] -b-> 1
 * NFA:  -->q0 -a-> ((q1))   q0 -b-> ((q1))
 *
 * Simple: both labeled one-edge paths are distinct and have no vertex repeats.
 */
static void test_simple_parallel_labels (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 1, { 0, 1, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> [1] -a-> 2
 * NFA:  -->((q0)) -a-> q0
 *
 * Simple, S={0,1}: retain both zero-edge paths and all three nonempty paths.
 * A root in the middle of a path does not block another source's path.
 */
static void test_simple_sources_and_roots (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 }
    } ;
    const ExpectedPath expected [] =
    {
        { 0, { 0 } },
        { 0, { 1 } },
        { 1, { 0, 0, 1 } },
        { 1, { 1, 0, 2 } },
        { 2, { 0, 0, 1, 0, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 1,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0, 1 }, .ns = 2,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0]               (no edges)
 * NFA:  -->((q0))          (no transitions)
 *
 * Simple: the zero-edge path is valid.
 */
static void test_simple_zero_length (void)
{
    const ExpectedPath expected [] =
    {
        { 0, { 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 1, .automaton_states = 1,
        .graph_edges = NULL, .graph_edge_count = 0,
        .automaton_edges = NULL,
        .automaton_edge_count = 0,
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllSimple
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> 2 -a-> [0]
 * NFA:  -->((q0)) -a-> q0
 *
 * Trails: the three-edge closed path is valid; a fourth edge would repeat 0-a->1.
 * Expected: the empty path and the three successive prefixes of one circuit.
 */
static void test_trails_vertex_revisit (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 }
    } ;
    const ExpectedPath expected [] =
    {
        { 0, { 0 } },
        { 1, { 0, 0, 1 } },
        { 2, { 0, 0, 1, 0, 2 } },
        { 3, { 0, 0, 1, 0, 2, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 1,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> [0] -b-> 1
 * NFA:  -->q0 -a-> q1 -a-> q2 -b-> ((q3))
 *
 * Trails: the ordered pair (0,1) occurs twice, under different labels a and b.
 * The edges are distinct, so 0-a-1-a-0-b-1 is valid.
 */
static void test_trails_different_labels (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 0 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 1, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 0, 1, 0, 0, 1, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> [0]
 * NFA:  -->q0 -a-> q1 -a-> ((q2))
 *
 * Trails: 0-a->1 and 1-a->0 are different directed edges despite equal labels.
 */
static void test_trails_opposite_directions (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> [0]
 * NFA:  -->q0 -a-> q1 -b-> q2 -a-> ((q3))
 *
 * Trails: the sole accepted walk 0-a-1-b-0-a-1 repeats the edge 0-a->1.
 * Different NFA states on its two uses do not make it a different graph edge.
 */
static void test_trails_repeated_edge (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 0, 3 }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = NULL,
        .expected_count = 0,
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> [0]
 * NFA:  -->q0 -a-> ((q1)) -a-> ((q2))
 *
 * Trails: the self-loop can be used once.  The accepted two-edge walk repeats it.
 */
static void test_trails_self_loop_once (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 1, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1, 2 }, .nqf = 2,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> [0] -a-> 2 -c-> 3
 *                   +--------------c----> 3
 * NFA:  -->q0 -a-> q1 -b-> q2 -a-> q3 -c-> ((q4))
 *
 * Trails: keep 0-a-1-b-0-a-2-c-3, whose a edges have different destinations.
 * Reject 0-a-1-b-0-a-1-c-3, which repeats the full edge (0,a,1).
 */
static void test_trails_different_targets (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 0 },
        { 0, 0, 2 },
        { 1, 2, 3 },
        { 2, 2, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 0, 3 },
        { 3, 2, 4 }
    } ;
    const ExpectedPath expected [] =
    {
        { 4, { 0, 0, 1, 1, 0, 0, 2, 2, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 5,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 4 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1        [0] -b-> 1
 * NFA:  -->q0 -a-> q1 -b-> ((q2))
 *
 * Trails, inverse_labels[b]=true: 0-a-1-b-0 is a valid closed trail.
 * The reverse traversal of b is distinct from the forward traversal of a.
 */
static void test_trails_inverse_label (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 1, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .inverse_labels = { false, true, false },
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllTrails
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> 3
 *          +--a-> 2 -a---^
 * NFA:  -->q0 -a-> q1 -a-> ((q2))
 *
 * Shortest: both two-edge branches to vertex 3 are tied and must be returned.
 */
static void test_shortest_equal_branches (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 0, 2 },
        { 1, 0, 3 },
        { 2, 0, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 0, 3 } },
        { 2, { 0, 0, 2, 0, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> 2
 * NFA:  -->q0 -a-> ((q1)) -b-> ((q2))
 *
 * Shortest: vertex 1 has minimum length 1, vertex 2 has minimum length 2.
 * The minimum is per destination, not a global minimum across results.
 */
static void test_shortest_per_destination (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 2, { 0, 0, 1, 1, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1, 2 }, .nqf = 2,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> 2 -c-> 3
 *          +---------------a----^
 * NFA:  -->q0 -a-> ((q1)) -b-> q2 -c-> ((q3))
 *
 * Shortest, QF={q3,q1}: abc reaches vertex 3 through the first accepting state,
 * then a supplies a shorter accepted path through q1.  Replace abc with a.
 * The already saved shortest path to vertex 1 must remain intact.
 */
static void test_shortest_later_final_state (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 3 },
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 2, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 },
        { 2, 2, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 1, { 0, 0, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3, 1 }, .nqf = 2,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> 4
 *        [2] --------a--> 4
 *        [3] --------a--> 4
 * NFA:  -->q0 -a-> ((q1)) -a-> q1
 *
 * Shortest, S={0,2,3}: vertex 4 has two one-edge ties from sources 2 and 3.
 * Discard the two-edge route from source 0; keep its one-edge route to vertex 1.
 */
static void test_shortest_sources (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 4 },
        { 2, 0, 4 },
        { 3, 0, 4 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 1, { 2, 0, 4 } },
        { 1, { 3, 0, 4 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 5, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0, 2, 3 }, .ns = 3,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1         [0] -b-> 1
 * NFA:  -->q0 -a-> ((q1))    q0 -b-> ((q2))
 *
 * Shortest: different accepting states supply equal-length paths to vertex 1.
 * Both label sequences must survive the shared minimum.
 */
static void test_shortest_parallel_final_states (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 0, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 1, { 0, 1, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1, 2 }, .nqf = 2,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -b-> 2
 * NFA:  -->q0 -a-> q1 -b-> ((q3))
 *           q0 -a-> q2 -b-> q3
 *
 * Shortest: two tied accepting NFA runs describe one graph path; emit it once.
 */
static void test_shortest_nondeterminism (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 0, 0, 2 },
        { 1, 1, 3 },
        { 2, 1, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 1, 1, 2 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> [0]
 * NFA:  -->((q0)) -a-> q0
 *
 * Shortest: the zero-edge path dominates all nonempty returns to vertex 0.
 * Vertex 1 still has the one-edge shortest path 0-a-1.
 */
static void test_shortest_root_and_cycle (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 0 }
    } ;
    const ExpectedPath expected [] =
    {
        { 0, { 0 } },
        { 1, { 0, 0, 1 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 1,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> [0]
 * NFA:  -->q0 -a-> q1 -a-> ((q2))
 *
 * Shortest: only aa is accepted.  Its shortest path repeats the vertex and edge.
 * Neither the zero-edge walk nor a single loop is a valid shortcut.
 */
static void test_shortest_requires_repeated_edge (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 0 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 0, 0, 0, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 1, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -b-> 1 -b-> 2 -b-> 3
 *          +---------------a----^
 * NFA:  -->q0 -b-> q1 -b-> q2 -b-> ((q3))
 *
 * Shortest: the direct graph edge a is rejected by the language.
 * The minimum accepted path is bbb, even though it is longer in the plain graph.
 */
static void test_shortest_rejected_shortcut (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 3 },
        { 0, 1, 1 },
        { 1, 1, 2 },
        { 2, 1, 3 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 1, 1 },
        { 1, 1, 2 },
        { 2, 1, 3 }
    } ;
    const ExpectedPath expected [] =
    {
        { 3, { 0, 1, 1, 1, 2, 1, 3 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 4, .automaton_states = 4,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 3 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: 0 -a-> 1 <-b- [2]
 * NFA: ((q0)) -a-> q1 -b-> q2 <-- initial
 *
 * Shortest, inverse=true, inverse_labels[b]=true, QS={q2}, QF={q0}, S={2}.
 * The accepted shortest path in query traversal order is 2-b-1-a-0.
 */
static void test_shortest_inverse_query (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 2, 1, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 1, 2 }
    } ;
    const ExpectedPath expected [] =
    {
        { 2, { 2, 1, 1, 0, 0 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 3, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 2 }, .nqs = 1,
        .QF = { 0 }, .nqf = 1,
        .S = { 2 }, .ns = 1,
        .inverse_labels = { false, true, false },
        .inverse = true,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1
 * NFA:  -->q0 -b-> ((q1))
 *
 * Shortest: no accepted path exists, so there is no minimum and no result.
 */
static void test_shortest_no_path (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 1, 1 }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 2, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = NULL,
        .expected_count = 0,
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph: [0] -a-> 1 -a-> 2 -a-> 4
 *          +--a-> 3 --------a--^
 *          +--a-> 5 --------a--^
 * NFA:  -->q0 -a-> ((q1)) -a-> q1
 *
 * Shortest: vertex 4 is first reconstructed through predecessor 2 (length 3),
 * then predecessor 3 improves its minimum to 2, and predecessor 5 supplies a tie.
 * Discard only the longer path to vertex 4, preserving other destinations.
 */
static void test_shortest_late_shorter_and_tie (void)
{
    const TestEdge graph [] =
    {
        { 0, 0, 1 },
        { 1, 0, 2 },
        { 2, 0, 4 },
        { 0, 0, 3 },
        { 3, 0, 4 },
        { 0, 0, 5 },
        { 5, 0, 4 }
    } ;
    const TestEdge automaton [] =
    {
        { 0, 0, 1 },
        { 1, 0, 1 }
    } ;
    const ExpectedPath expected [] =
    {
        { 1, { 0, 0, 1 } },
        { 2, { 0, 0, 1, 0, 2 } },
        { 1, { 0, 0, 3 } },
        { 2, { 0, 0, 3, 0, 4 } },
        { 2, { 0, 0, 5, 0, 4 } },
        { 1, { 0, 0, 5 } }
    } ;
    const TestQuery query =
    {
        .graph_vertices = 6, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected,
        .expected_count = ARRAY_COUNT (expected),
        .run = LAGraph_2RpqPath_AllShortestPaths
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:       +--a--> 1
 *          [0] +--a--> 2
 *              ...
 *              +--a--> 1100
 * NFA: -->q0 --a--> ((q1))
 *
 * Expected: 1100 distinct one-edge paths (0,a,i), i=1,...,1100.
 * The first step needs at least one temporary block per destination, exceeding
 * the former 1024-block arena limit.  Later steps must preserve all paths after
 * the temporary blocks from the first step have been freed.
 */
static void test_wide_graph (void)
{
    TestEdge graph [1100] ;
    ExpectedPath expected [1100] ;
    for (size_t k = 0 ; k < ARRAY_COUNT (graph) ; k++)
    {
        graph[k] = (TestEdge) { 0, 0, k + 1 } ;
        expected[k] = (ExpectedPath) { 1, { 0, 0, k + 1 } } ;
    }
    const TestEdge automaton [] = { { 0, 0, 1 } } ;
    const TestQuery query =
    {
        .graph_vertices = 1101, .automaton_states = 2,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 1 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected, .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

/*
 * Graph:           +--> 1  --+
 *              [0] --a--> ... a--> 66
 *                  +--> 65 --+
 * NFA: -->q0 --a--> q1 --a--> ((q2))
 *
 * The final configuration has 65 distinct predecessors, spanning more than
 * one default 64-record temporary block.  Expected: (0,a,i,a,66) for i=1,...,65.
 */
static void test_many_predecessors (void)
{
    TestEdge graph [130] ;
    const TestEdge automaton [] = { { 0, 0, 1 }, { 1, 0, 2 } } ;
    ExpectedPath expected [65] ;
    for (size_t k = 0 ; k < 65 ; k++)
    {
        graph[2 * k] = (TestEdge) { 0, 0, k + 1 } ;
        graph[2 * k + 1] = (TestEdge) { k + 1, 0, 66 } ;
        expected[k] = (ExpectedPath) { 2, { 0, 0, k + 1, 0, 66 } } ;
    }
    const TestQuery query =
    {
        .graph_vertices = 67, .automaton_states = 3,
        .graph_edges = graph, .graph_edge_count = ARRAY_COUNT (graph),
        .automaton_edges = automaton,
        .automaton_edge_count = ARRAY_COUNT (automaton),
        .QS = { 0 }, .nqs = 1,
        .QF = { 2 }, .nqf = 1,
        .S = { 0 }, .ns = 1,
        .expected = expected, .expected_count = ARRAY_COUNT (expected)
    } ;
    test_check_query (&query) ;
}

TEST_LIST =
{
    { "RpqPath_chain", test_chain },
    { "RpqPath_branching", test_branching },
    { "RpqPath_unequal_branches", test_unequal_branches },
    { "RpqPath_parallel_labels", test_parallel_labels },
    { "RpqPath_nondeterministic_runs", test_nondeterministic_runs },
    { "RpqPath_duplicate_accepting_states", test_duplicate_accepting_states },
    { "RpqPath_multiple_sources", test_multiple_sources },
    { "RpqPath_continue_through_roots", test_continue_through_roots },
    { "RpqPath_zero_length", test_zero_length },
    { "RpqPath_no_shared_label", test_no_shared_label },
    { "RpqPath_rejected_word", test_rejected_word },
    { "RpqPath_inverse_label", test_inverse_label },
    { "RpqPath_inverse_query", test_inverse_query },
    { "RpqPath_inverse_query_and_label", test_inverse_query_and_label },
    { "RpqPath_cycle_in_graph", test_cycle_in_graph },
    { "RpqPath_repeated_edge", test_repeated_edge },
    { "RpqPath_long_chain", test_long_chain },
    { "RpqPath_nonaccepting_cycle", test_nonaccepting_cycle },
    { "RpqPath_length_limit", test_length_limit },
    { "RpqPath_wide_graph", test_wide_graph },
    { "RpqPath_many_predecessors", test_many_predecessors },
    { "RpqPath_simple_repeated_vertex", test_simple_repeated_vertex },
    { "RpqPath_simple_self_loop", test_simple_self_loop },
    { "RpqPath_simple_closed_path", test_simple_closed_path },
    { "RpqPath_simple_parallel_labels", test_simple_parallel_labels },
    { "RpqPath_simple_sources_and_roots", test_simple_sources_and_roots },
    { "RpqPath_simple_zero_length", test_simple_zero_length },
    { "RpqPath_trails_vertex_revisit", test_trails_vertex_revisit },
    { "RpqPath_trails_different_labels", test_trails_different_labels },
    { "RpqPath_trails_opposite_directions", test_trails_opposite_directions },
    { "RpqPath_trails_repeated_edge", test_trails_repeated_edge },
    { "RpqPath_trails_self_loop_once", test_trails_self_loop_once },
    { "RpqPath_trails_different_targets", test_trails_different_targets },
    { "RpqPath_trails_inverse_label", test_trails_inverse_label },
    { "RpqPath_shortest_equal_branches", test_shortest_equal_branches },
    { "RpqPath_shortest_per_destination", test_shortest_per_destination },
    { "RpqPath_shortest_later_final_state", test_shortest_later_final_state },
    { "RpqPath_shortest_sources", test_shortest_sources },
    { "RpqPath_shortest_parallel_final_states", test_shortest_parallel_final_states },
    { "RpqPath_shortest_nondeterminism", test_shortest_nondeterminism },
    { "RpqPath_shortest_root_and_cycle", test_shortest_root_and_cycle },
    { "RpqPath_shortest_requires_repeated_edge", test_shortest_requires_repeated_edge },
    { "RpqPath_shortest_rejected_shortcut", test_shortest_rejected_shortcut },
    { "RpqPath_shortest_inverse_query", test_shortest_inverse_query },
    { "RpqPath_shortest_no_path", test_shortest_no_path },
    { "RpqPath_shortest_late_shorter_and_tie", test_shortest_late_shorter_and_tie },
    { NULL, NULL }
} ;


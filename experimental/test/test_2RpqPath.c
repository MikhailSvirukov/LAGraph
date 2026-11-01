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

    int info = LAGraph_2RpqPath_AllPaths (paths, count, R,
        query->inverse_labels, TEST_LABELS, query->QS, query->nqs,
        query->QF, query->nqf, G, query->S, query->ns, query->inverse, msg) ;
    TEST_ASSERT_ (info == GrB_SUCCESS, "AllPaths info=%d: %s", info, msg) ;
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
    { NULL, NULL }
} ;


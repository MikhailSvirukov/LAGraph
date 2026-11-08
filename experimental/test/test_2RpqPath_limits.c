// Black-box tests compiled with length=8 and count=4 to exercise both bounds
// without materializing tens of thousands of long cyclic paths.
#include <LAGraph_test.h>
#include <LAGraphX.h>

#define COUNT(a) (sizeof(a) / sizeof((a)[0]))
typedef struct { GrB_Index from; size_t label; GrB_Index to; } Edge;
typedef int (*Query)(LAGraph_RpqPath **, size_t *, LAGraph_Graph *, const bool *,
    size_t, const GrB_Index *, size_t, const GrB_Index *, size_t,
    LAGraph_Graph *, const GrB_Index *, size_t, bool, char *);
static char msg[LAGRAPH_MSG_LEN];

static uint64_t element(const LAGraph_RpqPath *path, size_t slot)
{
    size_t position = (slot + 1) / 2;
    const LAGraph_RpqPathNode *node = path->tail;
    while (node != NULL && node->length > position) node = node->prefix;
    TEST_ASSERT(node != NULL && node->length == position);
    return (slot & 1) ? node->label : node->vertex;
}

/** Build a borrowed-edge diagram as three owned label graphs.
 * @param[out] graphs Three graph handles, each released with LAGraph_Delete.
 * @param[in] n Number of vertices or states.
 * @param[in] edges List of zero-based edges, with labels a=0,b=1,c=2.
 * @param[in] count Number of edges.
 */
static void build(LAGraph_Graph graphs[3], GrB_Index n,
                  const Edge *edges, size_t count)
{
    for (size_t a = 0; a < 3; a++)
    {
        GrB_Matrix A = NULL;
        TEST_ASSERT(GrB_Matrix_new(&A, GrB_BOOL, n, n) == GrB_SUCCESS);
        TEST_ASSERT(GrB_set(A, GrB_ROWMAJOR, GrB_STORAGE_ORIENTATION_HINT) == GrB_SUCCESS);
        for (size_t k = 0; k < count; k++)
            if (edges[k].label == a)
                TEST_ASSERT(GrB_Matrix_setElement_BOOL(A, true,
                    edges[k].from, edges[k].to) == GrB_SUCCESS);
        TEST_ASSERT(LAGraph_New(&graphs[a], &A,
            LAGraph_ADJACENCY_DIRECTED, msg) == GrB_SUCCESS);
    }
}

/** Release both owned decompositions after their queries finish.
 * @param[in,out] G Three graph labels; handles become NULL.
 * @param[in,out] R Three NFA labels; handles become NULL.
 */
static void release(LAGraph_Graph G[3], LAGraph_Graph R[3])
{
    for (size_t a = 0; a < 3; a++)
    {
        TEST_CHECK(LAGraph_Delete(&G[a], msg) == GrB_SUCCESS);
        TEST_CHECK(LAGraph_Delete(&R[a], msg) == GrB_SUCCESS);
    }
    TEST_CHECK(LAGraph_Finalize(msg) == GrB_SUCCESS);
}

/* Graph: [0] --a--> 0 (self-loop).
 * NFA: -->((q0)) --a--> q1 --a--> q2 --a--> q3 --a--> q0.
 * With an inclusive length bound of 8, expected lengths are 0,4,8.
 * The count bound of 4 must not be reached; length 12 must be rejected.
 */
static void test_length_bound(void)
{
    const Edge graph[] = {{0,0,0}};
    const Edge nfa[] = {{0,0,1},{1,0,2},{2,0,3},{3,0,0}};
    LAGraph_Graph G[3], R[3];
    TEST_ASSERT(LAGraph_Init(msg) == GrB_SUCCESS);
    build(G,1,graph,COUNT(graph)); build(R,4,nfa,COUNT(nfa));
    const GrB_Index QS[] = {0}, QF[] = {0}, S[] = {0};
    const bool inverse[] = {false,false,false};
    LAGraph_RpqPath *paths = NULL; size_t count = 0;
    TEST_ASSERT(LAGraph_2RpqPath_AllPaths(&paths,&count,R,inverse,3,
        QS,1,QF,1,G,S,1,false,msg) == GrB_SUCCESS);
    TEST_CHECK(count == 3);
    bool seen[3] = {false,false,false};
    for (size_t k = 0; k < count; k++)
    {
        TEST_ASSERT(paths[k].length <= 8 && paths[k].length % 4 == 0);
        TEST_CHECK(!seen[paths[k].length / 4]);
        seen[paths[k].length / 4] = true;
        for (size_t i = 0; i <= 2 * paths[k].length; i++)
            TEST_CHECK(element(&paths[k], i) == 0);
    }
    TEST_CHECK(seen[0] && seen[1] && seen[2]);
    TEST_CHECK(LAGraph_2RpqPath_FreePaths(&paths,count,msg) == GrB_SUCCESS);
    release(G,R);
}

/* Graph: [0] --a--> i, i=1,...,6.
 * NFA: -->q0 --a--> ((q1)), and q0 --a--> ((q2)); QF={q1,q2,q1}.
 * Each graph path has duplicate accepting runs. For every semantics, the first
 * four DISTINCT paths end at vertices 1,2,3,4. No fifth result is admitted.
 */
static void test_count_bound(void)
{
    const Edge graph[] = {{0,0,1},{0,0,2},{0,0,3},{0,0,4},{0,0,5},{0,0,6}};
    const Edge nfa[] = {{0,0,1},{0,0,2}};
    LAGraph_Graph G[3], R[3];
    TEST_ASSERT(LAGraph_Init(msg) == GrB_SUCCESS);
    build(G,7,graph,COUNT(graph)); build(R,3,nfa,COUNT(nfa));
    const GrB_Index QS[] = {0}, QF[] = {1,2,1}, S[] = {0};
    const bool inverse[] = {false,false,false};
    Query queries[] = {LAGraph_2RpqPath_AllPaths,LAGraph_2RpqPath_AllSimple,
        LAGraph_2RpqPath_AllTrails,LAGraph_2RpqPath_AllShortestPaths};
    for (size_t mode = 0; mode < COUNT(queries); mode++)
    {
        LAGraph_RpqPath *paths = NULL; size_t count = 0;
        TEST_ASSERT(queries[mode](&paths,&count,R,inverse,3,
            QS,1,QF,3,G,S,1,false,msg) == GrB_SUCCESS);
        TEST_CHECK(count == 4);
        for (size_t k = 0; k < count; k++)
        {
            TEST_CHECK(paths[k].length == 1);
            TEST_CHECK(element(&paths[k], 0) == 0 && element(&paths[k], 1) == 0);
            TEST_CHECK(element(&paths[k], 2) == k + 1);
        }
        TEST_CHECK(LAGraph_2RpqPath_FreePaths(&paths,count,msg) == GrB_SUCCESS);
    }
    release(G,R);
}

/* Graph: [0] --a--> i --b--> 5, i=1,...,4; also 0 --c--> 5.
 * NFA: -->q0 --a--> q1 --b--> ((q2)); q0 --c--> ((q3)); QF={q2,q3}.
 * Four length-2 paths are found before the length-1 path. The cap stops the
 * traversal successfully, even for shortest: only those first four are seen.
 */
static void test_shortest_early_stop(void)
{
    const Edge graph[] = {{0,0,1},{1,1,5},{0,0,2},{2,1,5},
        {0,0,3},{3,1,5},{0,0,4},{4,1,5},{0,2,5}};
    const Edge nfa[] = {{0,0,1},{1,1,2},{0,2,3}};
    LAGraph_Graph G[3], R[3];
    TEST_ASSERT(LAGraph_Init(msg) == GrB_SUCCESS);
    build(G,6,graph,COUNT(graph)); build(R,4,nfa,COUNT(nfa));
    const GrB_Index QS[] = {0}, QF[] = {2,3}, S[] = {0};
    const bool inverse[] = {false,false,false};
    LAGraph_RpqPath *paths = NULL; size_t count = 0;
    TEST_ASSERT(LAGraph_2RpqPath_AllShortestPaths(&paths,&count,R,inverse,3,
        QS,1,QF,2,G,S,1,false,msg) == GrB_SUCCESS);
    TEST_CHECK(count == 4);
    bool seen[4] = {false,false,false,false};
    for (size_t k = 0; k < count; k++)
    {
        TEST_CHECK(paths[k].length == 2);
        TEST_CHECK(element(&paths[k], 0) == 0 && element(&paths[k], 1) == 0);
        uint64_t middle = element(&paths[k], 2);
        TEST_ASSERT(middle >= 1 && middle <= 4);
        TEST_CHECK(!seen[middle - 1]);
        seen[middle - 1] = true;
        TEST_CHECK(element(&paths[k], 3) == 1 && element(&paths[k], 4) == 5);
    }
    TEST_CHECK(seen[0] && seen[1] && seen[2] && seen[3]);
    TEST_CHECK(LAGraph_2RpqPath_FreePaths(&paths,count,msg) == GrB_SUCCESS);
    release(G,R);
}

/* A self-loop feeds both itself and an accepting edge.  Recursive propagation
 * must consume entries appended while the loop is active, pass each to the
 * accepting branch, and stop immediately at the distinct-result count cap.
 */
static void test_recursive_cycle_count_cap(void)
{
    const Edge graph[] = {{0,0,0},{0,1,1}};
    const Edge nfa[] = {{0,0,0},{0,1,1}};
    LAGraph_Graph G[3], R[3];
    TEST_ASSERT(LAGraph_Init(msg) == GrB_SUCCESS);
    build(G,2,graph,COUNT(graph)); build(R,2,nfa,COUNT(nfa));
    const GrB_Index QS[] = {0}, QF[] = {1}, S[] = {0};
    const bool inverse[] = {false,false,false};
    LAGraph_RpqPath *paths = NULL; size_t count = 0;
    TEST_ASSERT(LAGraph_2RpqPath_AllPaths(&paths,&count,R,inverse,3,
        QS,1,QF,1,G,S,1,false,msg) == GrB_SUCCESS);
    TEST_ASSERT(count == 4);
    bool seen[4] = {false,false,false,false};
    for (size_t k = 0; k < count; k++)
    {
        size_t length = paths[k].length;
        TEST_ASSERT(length >= 1 && length <= 4);
        TEST_CHECK(!seen[length - 1]); seen[length - 1] = true;
        for (size_t j = 0; j < length; j++)
        {
            TEST_CHECK(element(&paths[k],2*j) == 0);
            TEST_CHECK(element(&paths[k],2*j+1) == (j+1 == length ? 1 : 0));
        }
        TEST_CHECK(paths[k].tail->vertex == 1);
    }
    TEST_CHECK(seen[0] && seen[1] && seen[2] && seen[3]);
    TEST_CHECK(LAGraph_2RpqPath_FreePaths(&paths,count,msg) == GrB_SUCCESS);
    release(G,R);
}

TEST_LIST = {
    {"RpqPath_length_bound",test_length_bound},
    {"RpqPath_count_bound",test_count_bound},
    {"RpqPath_shortest_early_stop",test_shortest_early_stop},
    {"RpqPath_recursive_cycle_count_cap",test_recursive_cycle_count_cap},
    {NULL,NULL}
};

// SPDX-License-Identifier: BSD-2-Clause
// Public API coverage: growing P filters and saturated persistent path filters.
#include <LAGraph_test.h>
#include <LAGraphX.h>
#include "../algorithm/LG_RpqPath_bloom.h"

typedef int (*Query)(LAGraph_RpqPath **, size_t *, LAGraph_Graph *, size_t,
    const GrB_Index *, size_t, const GrB_Index *, size_t, LAGraph_Graph *,
    const GrB_Index *, size_t, char *) ;
static void run_growth (void)
{
    char msg[LAGRAPH_MSG_LEN] ;
    OK (LAGraph_Init (msg)) ;
    LAGraph_Graph graph = NULL, automaton = NULL ;
    GrB_Matrix a = NULL, n = NULL ;
    OK (GrB_Matrix_new (&a, GrB_BOOL, 131, 131)) ;
    for (GrB_Index v = 0 ; v < 130 ; v++)
    {
        OK (GrB_Matrix_setElement_BOOL (a, true, v, 130)) ;
        if (v < 129) OK (GrB_Matrix_setElement_BOOL (a, true, v, v + 1)) ;
    }
    OK (GrB_Matrix_new (&n, GrB_BOOL, 1, 1)) ;
    OK (GrB_Matrix_setElement_BOOL (n, true, 0, 0)) ;
    OK (LAGraph_New (&graph, &a, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    OK (LAGraph_New (&automaton, &n, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    GrB_Index zero = 0 ;
    Query queries[] = { LAGraph_2RpqPath_AllPaths, LAGraph_2RpqPath_AllSimple,
        LAGraph_2RpqPath_AllTrails, LAGraph_2RpqPath_AllShortestPaths } ;
    for (size_t k = 0 ; k < 4 ; k++)
    {
        LAGraph_RpqPath *paths = NULL ; size_t count = 0 ;
        OK (queries[k] (&paths, &count, &automaton, 1, &zero, 1, &zero, 1,
            &graph, &zero, 1, msg)) ;
        TEST_CHECK (count == (k == 3 ? 131 : 260)) ;
        OK (LAGraph_2RpqPath_FreePaths (&paths, count, msg)) ;
    }
    OK (LAGraph_Delete (&automaton, msg)) ; OK (LAGraph_Delete (&graph, msg)) ;
    OK (LAGraph_Finalize (msg)) ;
}

static void run_cycle (void)
{
    char msg[LAGRAPH_MSG_LEN] ; OK (LAGraph_Init (msg)) ;
    LAGraph_Graph graph = NULL, automaton = NULL ;
    GrB_Matrix a = NULL, n = NULL ;
    OK (GrB_Matrix_new (&a, GrB_BOOL, 3, 3)) ;
    OK (GrB_Matrix_setElement_BOOL (a, true, 0, 1)) ;
    OK (GrB_Matrix_setElement_BOOL (a, true, 1, 0)) ;
    OK (GrB_Matrix_setElement_BOOL (a, true, 1, 2)) ;
    OK (GrB_Matrix_new (&n, GrB_BOOL, 1, 1)) ;
    OK (GrB_Matrix_setElement_BOOL (n, true, 0, 0)) ;
    OK (LAGraph_New (&graph, &a, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    OK (LAGraph_New (&automaton, &n, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    GrB_Index zero = 0 ;
    Query queries[] = { LAGraph_2RpqPath_AllSimple, LAGraph_2RpqPath_AllTrails } ;
    for (size_t k = 0 ; k < 2 ; k++)
    {
        LAGraph_RpqPath *paths = NULL ; size_t count = 0 ;
        OK (queries[k] (&paths, &count, &automaton, 1, &zero, 1, &zero, 1,
            &graph, &zero, 1, msg)) ;
        TEST_CHECK (count == (k == 0 ? 3 : 4)) ;
        OK (LAGraph_2RpqPath_FreePaths (&paths, count, msg)) ;
    }
    OK (LAGraph_Delete (&automaton, msg)) ; OK (LAGraph_Delete (&graph, msg)) ;
    OK (LAGraph_Finalize (msg)) ;
}
static void run_persistence (void)
{
    char msg[LAGRAPH_MSG_LEN] ; OK (LAGraph_Init (msg)) ;
    LG_RpqPath_BloomShape shape ;
    OK (LG_RpqPath_BloomShapeNew (128, 4096, &shape)) ;
    TEST_ASSERT (shape.words <= 64 && shape.depth > 0) ;
    const LG_RpqPath_BloomNode *versions[101] = { NULL } ;
    uint64_t words[101][64] = { { 0 } } ;
    LG_RpqPath_BloomNodes *pool = NULL ;
    for (size_t i = 0 ; i < 100 ; i++)
    {
        uint64_t hash = LG_RpqPath_BloomKey (i, 7, i + 1) ;
        OK (LG_RpqPath_BloomExtend (&shape, &pool, versions[i], hash, &versions[i+1], msg)) ;
        memcpy (words[i+1], words[i], sizeof (words[i])) ;
        uint64_t stride = LG_RpqPath_BloomStride (hash) ;
        for (size_t k = 0 ; k < shape.hashes ; k++)
        {
            size_t bit = LG_RpqPath_BloomPosition (&shape, hash, stride, k) ;
            words[i+1][bit / 64] |= UINT64_C (1) << (bit % 64) ;
        }
    }
    const LG_RpqPath_BloomNode *branch = NULL ;
    OK (LG_RpqPath_BloomExtend (&shape, &pool, versions[20],
        LG_RpqPath_BloomKey (999, 1, 1000), &branch, msg)) ;
    for (size_t i = 0 ; i <= 100 ; i++)
    {
        for (size_t word = 0 ; word < shape.words ; word++)
            TEST_CHECK (LG_RpqPath_BloomWord (versions[i], shape.depth, word) == words[i][word]) ;
        for (size_t key = 0 ; key < i ; key++)
            TEST_CHECK (LG_RpqPath_BloomMayContain (&shape, versions[i], LG_RpqPath_BloomKey (key, 7, key + 1))) ;
    }
    TEST_CHECK (LG_RpqPath_BloomMayContain (&shape, branch, LG_RpqPath_BloomKey (999, 1, 1000))) ;
    const LG_RpqPath_BloomNode *same = NULL ;
    OK (LG_RpqPath_BloomExtend (&shape, &pool, versions[100], LG_RpqPath_BloomKey (0, 7, 1), &same, msg)) ;
    TEST_CHECK (same == versions[100]) ;
    LG_RpqPath_BloomNodesFree (&pool) ; TEST_CHECK (pool == NULL) ;
    OK (LAGraph_Finalize (msg)) ;
}
TEST_LIST = { { "bloom/immutable-word-versions", run_persistence }, { "bloom/P-growth-and-path-versions", run_growth },
    { "bloom/exact-cycle-rejection", run_cycle }, { NULL, NULL } } ;

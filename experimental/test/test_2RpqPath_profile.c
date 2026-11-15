// SPDX-License-Identifier: BSD-2-Clause
#include <LAGraph_test.h>
#include <LAGraphX.h>
static void shared_profile (void)
{
    char msg[LAGRAPH_MSG_LEN] ; OK (LAGraph_Init (msg)) ;
    FILE *stream = tmpfile () ; TEST_ASSERT (stream != NULL) ;
    GrB_Matrix a = NULL, n = NULL ; LAGraph_Graph graph = NULL, automaton = NULL ;
    OK (GrB_Matrix_new (&a, GrB_BOOL, 1, 1)) ;
    OK (GrB_Matrix_new (&n, GrB_BOOL, 1, 1)) ;
    OK (LAGraph_New (&graph, &a, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    OK (LAGraph_New (&automaton, &n, LAGraph_ADJACENCY_DIRECTED, msg)) ;
    GrB_Index zero = 0 ;
    for (size_t pass = 0 ; pass < 2 ; pass++)
    {
        OK (LAGraph_2RpqPath_SetProfile (stream, pass == 0 ? "alpha" : "beta", pass + 1, pass == 0, msg)) ;
        LAGraph_RpqPath *paths = NULL ; size_t count = 0 ;
        OK (LAGraph_2RpqPath_AllPaths (&paths, &count, &automaton, 1,
            &zero, 1, &zero, 1, &graph, &zero, 1, msg)) ;
        TEST_CHECK (count == 1) ; OK (LAGraph_2RpqPath_FreePaths (&paths, count, msg)) ;
    }
    OK (LAGraph_2RpqPath_SetProfile (NULL, NULL, 0, false, msg)) ;
    rewind (stream) ; char line[2048] ; size_t headers = 0, alpha = 0, beta = 0, ends = 0 ;
    while (fgets (line, sizeof (line), stream) != NULL)
    {
        headers += strncmp (line, "pid\tcall\t", 9) == 0 ;
        alpha += strstr (line, "\tquery\talpha\n") != NULL ;
        beta += strstr (line, "\tquery\tbeta\n") != NULL ;
        ends += strstr (line, "\tstatus\t0.000000000\n") != NULL && strstr (line, "\tquery\t0\t-1\tend\t") != NULL ;
    }
    TEST_CHECK (headers == 1 && alpha == 1 && beta == 1 && ends == 2) ;
    TEST_CHECK (fclose (stream) == 0) ;
    OK (LAGraph_Delete (&automaton, msg)) ; OK (LAGraph_Delete (&graph, msg)) ;
    OK (LAGraph_Finalize (msg)) ;
}
TEST_LIST = { { "profile/shared-explicit-stream", shared_profile }, { NULL, NULL } } ;

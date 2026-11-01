//------------------------------------------------------------------------------
// rpq_paths_demo: benchmark prepared graph/NFA Matrix Market decompositions
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause

#include "LAGraphX.h"
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

typedef int (*QueryFunction)
(
    LAGraph_RpqPath **, size_t *, LAGraph_Graph *, const bool *, size_t,
    const GrB_Index *, size_t, const GrB_Index *, size_t, LAGraph_Graph *,
    const GrB_Index *, size_t, bool, char *
) ;

typedef struct
{
    int64_t label ;
    LAGraph_Graph graph ;
}
GraphLabel ;

/** Read a square Matrix Market matrix, cast values to bool and materialize it.
 * @param[out] graph Receives an owned graph, or NULL on error.
 * @param[in] path Input filename.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GraphBLAS/LAGraph status; a file/shape error returns GrB_INVALID_VALUE.
 */
static int read_graph (LAGraph_Graph *graph, const char *path, char *msg)
{
    *graph = NULL ;
    FILE *file = fopen (path, "r") ;
    if (file == NULL)
    {
        fprintf (stderr, "%s: %s\n", path, strerror (errno)) ;
        return (GrB_INVALID_VALUE) ;
    }
    GrB_Matrix A = NULL, B = NULL ;
    int info = LAGraph_MMRead (&A, file, msg) ;
    fclose (file) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    GrB_Index rows = 0, cols = 0 ;
    info = GrB_Matrix_nrows (&rows, A) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = GrB_Matrix_ncols (&cols, A) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    if (rows != cols)
    {
        fprintf (stderr, "%s: expected a square matrix\n", path) ;
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    info = GrB_Matrix_new (&B, GrB_BOOL, rows, cols) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = GrB_set (B, GrB_ROWMAJOR, GrB_STORAGE_ORIENTATION_HINT) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = GrB_Matrix_assign (B, NULL, NULL, A,
        GrB_ALL, rows, GrB_ALL, cols, NULL) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = GrB_Matrix_wait (B, GrB_MATERIALIZE) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_New (graph, &B, LAGraph_ADJACENCY_DIRECTED, msg) ;
cleanup:
    GrB_free (&A) ;
    GrB_free (&B) ;
    return (info) ;
}

/** Read a counted list of one-based NFA states and convert them to zero-based.
 * @param[in] file Open meta.txt stream, positioned before the list's count.
 * @param[out] states Receives an owned array, including partial setup on error.
 * @param[out] count Receives the number of entries.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation error.
 */
static int read_states
(
    FILE *file, GrB_Index **states, size_t *count, char *msg
)
{
    if (fscanf (file, "%zu", count) != 1) return (GrB_INVALID_VALUE) ;
    int info = LAGraph_Malloc ((void **) states, *count, sizeof (GrB_Index), msg) ;
    if (info != GrB_SUCCESS) return (info) ;
    for (size_t k = 0 ; k < *count ; k++)
    {
        uint64_t state ;
        if (fscanf (file, "%" SCNu64, &state) != 1 || state == 0)
            return (GrB_INVALID_VALUE) ;
        (*states)[k] = state - 1 ;
    }
    return (GrB_SUCCESS) ;
}

/** Execute one query directory, printing query/time_seconds/path_count on success.
 * @param[in] directory Numbered query directory with meta.txt and label matrices.
 * @param[in] graph Loaded graph labels, borrowed; loaded once for the whole batch.
 * @param[in] graph_count Number of graph labels.
 * @param[in] ng Shared graph vertex count.
 * @param[in] query Selected public query function.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation/algorithm error.
 */
static int run_query
(
    const char *directory, const GraphLabel *graph, size_t graph_count,
    GrB_Index ng, QueryFunction query, char *msg
)
{
    char *path = NULL ;
    FILE *meta = NULL ;
    GrB_Index *QS = NULL, *QF = NULL, *S = NULL ;
    LAGraph_Graph *G = NULL, *R = NULL ;
    bool *inverse_labels = NULL ;
    LAGraph_RpqPath *paths = NULL ;
    size_t nqs = 0, nqf = 0, ns = 0, nl = 0, path_count = 0 ;
    uint64_t source = 0, target = 0 ;
    size_t path_size = strlen (directory) + 64 ;
    int info = LAGraph_Malloc ((void **) &path, path_size, 1, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    snprintf (path, path_size, "%s/meta.txt", directory) ;
    meta = fopen (path, "r") ;
    if (meta == NULL)
    {
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    if (fscanf (meta, "%" SCNu64 " %" SCNu64, &source, &target) != 2 ||
        source > ng || target > ng)
    {
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    if (target != 0)
    {
        fprintf (stderr, "%s: fixed targets are unsupported by the benchmark; "
            "the public API returns paths to all accepting endpoints\n", directory) ;
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    info = read_states (meta, &QS, &nqs, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = read_states (meta, &QF, &nqf, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    if (fscanf (meta, "%zu", &nl) != 1 || nl == 0)
    {
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    info = LAGraph_Calloc ((void **) &G, nl, sizeof (LAGraph_Graph), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &R, nl, sizeof (LAGraph_Graph), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &inverse_labels, nl, sizeof (bool), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    for (size_t a = 0 ; a < nl ; a++)
    {
        int64_t label ;
        if (fscanf (meta, "%" SCNd64, &label) != 1 || label == 0 ||
            label == INT64_MIN)
        {
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        int64_t absolute = label < 0 ? -label : label ;
        for (size_t k = 0 ; k < graph_count ; k++)
            if (graph[k].label == absolute) G[a] = graph[k].graph ;
        if (G[a] == NULL)
        {
            fprintf (stderr, "%s: missing graph matrix for label %" PRId64 "\n",
                directory, absolute) ;
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        inverse_labels[a] = label < 0 ;
        snprintf (path, path_size, "%s/%" PRId64 ".txt", directory, label) ;
        info = read_graph (&R[a], path, msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
    }
    fclose (meta) ;
    meta = NULL ;

    ns = source != 0 ? 1 : (size_t) ng ;
    info = LAGraph_Malloc ((void **) &S, ns, sizeof (GrB_Index), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    if (source != 0) S[0] = source - 1 ;
    else for (size_t k = 0 ; k < ns ; k++) S[k] = k ;

    double begin = LAGraph_WallClockTime ( ) ;
    info = query (&paths, &path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, false, msg) ;
    double seconds = LAGraph_WallClockTime ( ) - begin ;
    if (info != GrB_SUCCESS) goto cleanup ;

    const char *number = strrchr (directory, '/') ;
    printf ("%s\t%.9f\t%zu\n", number == NULL ? directory : number + 1,
        seconds, path_count) ;
    fflush (stdout) ;
cleanup:
    if (meta != NULL) fclose (meta) ;
    if (R != NULL)
        for (size_t a = 0 ; a < nl ; a++) LAGraph_Delete (&R[a], NULL) ;
    LAGraph_2RpqPath_FreePaths (&paths, path_count, NULL) ;
    LAGraph_Free ((void **) &path, NULL) ;
    LAGraph_Free ((void **) &QS, NULL) ;
    LAGraph_Free ((void **) &QF, NULL) ;
    LAGraph_Free ((void **) &S, NULL) ;
    LAGraph_Free ((void **) &G, NULL) ;
    LAGraph_Free ((void **) &R, NULL) ;
    LAGraph_Free ((void **) &inverse_labels, NULL) ;
    return (info) ;
}

// The Python launcher supplies: semantics graph_count graph_files... query_dirs...
int main (int argc, char **argv)
{
    if (argc < 5) return (EXIT_FAILURE) ;
    QueryFunction query = NULL ;
    if (!strcmp (argv[1], "all")) query = LAGraph_2RpqPath_AllPaths ;
    if (!strcmp (argv[1], "simple")) query = LAGraph_2RpqPath_AllSimple ;
    if (!strcmp (argv[1], "trails")) query = LAGraph_2RpqPath_AllTrails ;
    if (!strcmp (argv[1], "shortest")) query = LAGraph_2RpqPath_AllShortestPaths ;
    char *end = NULL ;
    long n = strtol (argv[2], &end, 10) ;
    if (query == NULL || *end != '\0' || n < 1 || n > argc - 4)
        return (EXIT_FAILURE) ;
    char msg [LAGRAPH_MSG_LEN] = "" ;
    GraphLabel *graph = NULL ;
    bool failed = false ;
    int info = LAGraph_Init (msg) ;
    if (info != GrB_SUCCESS)
    {
        fprintf (stderr, "initialization: info=%d %s\n", info, msg) ;
        return (EXIT_FAILURE) ;
    }
    info = LAGraph_Calloc ((void **) &graph, (size_t) n, sizeof (GraphLabel), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    GrB_Index ng = 0 ;
    for (long k = 0 ; k < n ; k++)
    {
        const char *file = argv[3 + k] ;
        const char *base = strrchr (file, '/') ;
        base = base == NULL ? file : base + 1 ;
        graph[k].label = strtoll (base, &end, 10) ;
        if (graph[k].label < 1 || *end != '.')
        {
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        info = read_graph (&graph[k].graph, file, msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
        GrB_Index size = 0 ;
        info = GrB_Matrix_nrows (&size, graph[k].graph->A) ;
        if (info != GrB_SUCCESS) goto cleanup ;
        if (k != 0 && size != ng)
        {
            fprintf (stderr, "graph matrices have different dimensions\n") ;
            info = GrB_DIMENSION_MISMATCH ;
            goto cleanup ;
        }
        ng = size ;
    }
    printf ("query\ttime_seconds\tpaths\n") ;
    for (int k = 3 + (int) n ; k < argc ; k++)
    {
        int query_info = run_query (argv[k], graph, (size_t) n, ng, query, msg) ;
        if (query_info != GrB_SUCCESS)
        {
            fprintf (stderr, "%s: info=%d %s\n", argv[k], query_info, msg) ;
            failed = true ;
        }
    }
cleanup:
    if (graph != NULL)
        for (long k = 0 ; k < n ; k++) LAGraph_Delete (&graph[k].graph, NULL) ;
    LAGraph_Free ((void **) &graph, NULL) ;
    if (info != GrB_SUCCESS) fprintf (stderr, "info=%d %s\n", info, msg) ;
    LAGraph_Finalize (NULL) ;
    return (failed || info != GrB_SUCCESS ? EXIT_FAILURE : EXIT_SUCCESS) ;
}

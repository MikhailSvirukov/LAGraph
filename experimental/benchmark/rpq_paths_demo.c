//------------------------------------------------------------------------------
// rpq_paths_demo: benchmark prepared graph/NFA Matrix Market decompositions
//------------------------------------------------------------------------------
// SPDX-License-Identifier: BSD-2-Clause

#include "LAGraphX.h"
#include <errno.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

typedef int (*QueryFunction)
(
    LAGraph_RpqPath **, size_t *, LAGraph_Graph *, const bool *, size_t,
    const GrB_Index *, size_t, const GrB_Index *, size_t, LAGraph_Graph *,
    const GrB_Index *, size_t, bool, char *
) ;

/** Read a square Matrix Market matrix, cast values to bool and materialize it.
 * @param[out] graph Receives an owned graph, or NULL on error.
 * @param[in] path Input filename.
 * @param[in] optional Accept a missing file as an absent label (NULL graph).
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GraphBLAS/LAGraph status; a file/shape error returns GrB_INVALID_VALUE.
 */
static int read_graph
(
    LAGraph_Graph *graph, const char *path, bool optional, char *msg
)
{
    *graph = NULL ;
    FILE *file = fopen (path, "r") ;
    if (file == NULL)
    {
        if (optional && errno == ENOENT) return (GrB_SUCCESS) ;
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
 * @param[in] file Open metadata stream, positioned before the list's count.
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

/** Read an uncounted list of one-based graph source vertices.
 * @param[in] path Sources filename; whitespace separates vertex IDs.
 * @param[out] sources Receives an owned array, including partial setup on error.
 * @param[out] count Receives the number of entries; an empty file means no sources.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation error.
 */
static int read_sources
(
    const char *path, GrB_Index **sources, size_t *count, char *msg
)
{
    FILE *file = fopen (path, "r") ;
    if (file == NULL)
    {
        fprintf (stderr, "%s: %s\n", path, strerror (errno)) ;
        return (GrB_INVALID_VALUE) ;
    }
    *count = 0 ;
    uint64_t vertex ;
    int scanned, info = GrB_SUCCESS ;
    while ((scanned = fscanf (file, "%" SCNu64, &vertex)) == 1)
    {
        if (vertex == 0) { info = GrB_INVALID_VALUE ; goto cleanup ; }
        (*count)++ ;
    }
    if (scanned != EOF || ferror (file))
    {
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    rewind (file) ;
    info = LAGraph_Malloc ((void **) sources, *count, sizeof (GrB_Index), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    for (size_t k = 0 ; k < *count ; k++)
    {
        if (fscanf (file, "%" SCNu64, &vertex) != 1 || vertex == 0)
        {
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        (*sources)[k] = vertex - 1 ;
    }
cleanup:
    fclose (file) ;
    return (info) ;
}

typedef struct
{
    const char *label ;             // borrowed canonical label name from argv
    LAGraph_Graph graph ;           // owned; loaded once for the whole batch
}
GraphLabel ;

/** Load one query, call the API and release all query resources.
 * @param[in] prefix Query directory or flat filename prefix without suffix.
 * @param[in] folders True for <number>/meta.txt, false for <number>_meta.txt.
 * @param[in] graph Borrowed graph labels, loaded once for the whole batch.
 * @param[in] graph_count Number of graph labels.
 * @param[in] ng Shared graph vertex count, used for unrestricted source sets.
 * @param[in] query Selected public query function.
 * @param[out] seconds Receives the elapsed time of the public query call.
 * @param[out] count Receives the returned path count; valid only on success.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation/algorithm error.  Fixed source
 *     and destination together are rejected: the API has no target filter.
 */
static int run_query
(
    const char *prefix, bool folders, const GraphLabel *graph,
    size_t graph_count, GrB_Index ng, QueryFunction query,
    double *seconds, size_t *count, char *msg
)
{
    FILE *meta = NULL ;
    char *path = NULL ;
    GrB_Index *QS = NULL, *QF = NULL, *S = NULL ;
    LAGraph_Graph *G = NULL, *R = NULL ;
    bool *inverse_labels = NULL ;
    LAGraph_RpqPath *paths = NULL ;
    size_t nqs = 0, nqf = 0, ns = 0, nl = graph_count, path_count = 0 ;
    uint64_t source = 0, target = 0 ;
    bool inverse = false ;
    size_t path_size = strlen (prefix) + 64 ;
    for (size_t k = 0 ; k < graph_count ; k++)
    {
        size_t needed = strlen (prefix) + strlen (graph[k].label) + 16 ;
        if (needed > path_size) path_size = needed ;
    }
    int info = LAGraph_Malloc ((void **) &path, path_size, 1, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    snprintf (path, path_size, "%s%s", prefix,
        folders ? "/meta.txt" : "_meta.txt") ;
    meta = fopen (path, "r") ;
    if (meta == NULL)
    {
        fprintf (stderr, "%s: %s\n", path, strerror (errno)) ;
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    if (folders)
    {
        if (fscanf (meta, "%" SCNu64 " %" SCNu64, &source, &target) != 2 ||
            source > ng || target > ng)
        {
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        if (source != 0 && target != 0)
        {
            if (msg != NULL) snprintf (msg, LAGRAPH_MSG_LEN,
                "fixed source and destination together are unsupported by the API") ;
            info = GrB_INVALID_VALUE ;
            goto cleanup ;
        }
        inverse = source == 0 && target != 0 ;
    }
    info = read_states (meta, &QS, &nqs, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = read_states (meta, &QF, &nqf, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    if (folders && (fscanf (meta, "%zu", &nl) != 1 || nl == 0))
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
        if (folders)
        {
            int64_t label ;
            if (fscanf (meta, "%" SCNd64, &label) != 1 || label == 0 ||
                label == INT64_MIN)
            {
                info = GrB_INVALID_VALUE ;
                goto cleanup ;
            }
            char name [32] ;
            snprintf (name, sizeof (name), "%" PRId64, label < 0 ? -label : label) ;
            for (size_t k = 0 ; k < graph_count ; k++)
                if (!strcmp (graph[k].label, name)) G[a] = graph[k].graph ;
            if (G[a] == NULL)
            {
                if (msg != NULL) snprintf (msg, LAGRAPH_MSG_LEN,
                    "missing graph matrix for label %s", name) ;
                info = GrB_INVALID_VALUE ;
                goto cleanup ;
            }
            inverse_labels[a] = label < 0 ;
            snprintf (path, path_size, "%s/%" PRId64 ".txt", prefix, label) ;
        }
        else
        {
            G[a] = graph[a].graph ;
            snprintf (path, path_size, "%s_%s.mtx", prefix, graph[a].label) ;
        }
        info = read_graph (&R[a], path, !folders, msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
    }
    fclose (meta) ;
    meta = NULL ;
    if (folders)
    {
        ns = source != 0 || inverse ? 1 : (size_t) ng ;
        info = LAGraph_Malloc ((void **) &S, ns, sizeof (GrB_Index), msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
        if (source != 0) S[0] = source - 1 ;
        else if (inverse) S[0] = target - 1 ;
        else for (size_t k = 0 ; k < ns ; k++) S[k] = k ;
    }
    else
    {
        snprintf (path, path_size, "%s_sources.txt", prefix) ;
        info = read_sources (path, &S, &ns, msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
    }

    double begin = LAGraph_WallClockTime ( ) ;
    info = query (&paths, &path_count, R, inverse_labels, nl,
        inverse ? QF : QS, inverse ? nqf : nqs,
        inverse ? QS : QF, inverse ? nqs : nqf, G, S, ns, inverse, msg) ;
    *seconds = LAGraph_WallClockTime ( ) - begin ;
    if (info != GrB_SUCCESS) goto cleanup ;
    *count = path_count ;
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

typedef struct
{
    double seconds ;                // sum of measured query times
    size_t paths ;                  // identical across measured passes
    bool failed ;                   // suppress incomplete/invalid averages
}
BenchmarkResult ;

// Python supplies: semantics warmup iterations layout graph_count
// (label graph_file)... query_prefixes...
int main (int argc, char **argv)
{
    if (argc < 9) return (EXIT_FAILURE) ;
    QueryFunction query = NULL ;
    if (!strcmp (argv[1], "all")) query = LAGraph_2RpqPath_AllPaths ;
    if (!strcmp (argv[1], "simple")) query = LAGraph_2RpqPath_AllSimple ;
    if (!strcmp (argv[1], "trails")) query = LAGraph_2RpqPath_AllTrails ;
    if (!strcmp (argv[1], "shortest")) query = LAGraph_2RpqPath_AllShortestPaths ;
    char *end = NULL ;
    errno = 0 ;
    long warmup = strtol (argv[2], &end, 10) ;
    if (errno || *end != '\0' || end == argv[2] || warmup < 0)
        return (EXIT_FAILURE) ;
    long iterations = strtol (argv[3], &end, 10) ;
    if (errno || *end != '\0' || end == argv[3] || iterations < 1)
        return (EXIT_FAILURE) ;
    bool folders = !strcmp (argv[4], "folders") ;
    if (!folders && strcmp (argv[4], "flat")) return (EXIT_FAILURE) ;
    long n = strtol (argv[5], &end, 10) ;
    if (errno || query == NULL || *end != '\0' || n < 1 || n > (argc - 7) / 2)
        return (EXIT_FAILURE) ;
    size_t first_query = 6 + 2 * n ;
    size_t query_count = argc - first_query ;
    char msg [LAGRAPH_MSG_LEN] = "" ;
    GraphLabel *graph = NULL ;
    BenchmarkResult *results = NULL ;
    bool failed = false ;
    int info = LAGraph_Init (msg) ;
    if (info != GrB_SUCCESS)
    {
        fprintf (stderr, "initialization: info=%d %s\n", info, msg) ;
        return (EXIT_FAILURE) ;
    }
    info = LAGraph_Calloc ((void **) &graph, (size_t) n, sizeof (GraphLabel), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &results, query_count,
        sizeof (BenchmarkResult), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    GrB_Index ng = 0 ;
    for (long k = 0 ; k < n ; k++)
    {
        graph[k].label = argv[6 + 2 * k] ;
        info = read_graph (&graph[k].graph, argv[7 + 2 * k], false, msg) ;
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
    // Finish every warmup batch before starting measured batches.  Keeping
    // phases separate also avoids overflowing warmup + iterations.
    for (int phase = 0 ; phase < 2 ; phase++)
    {
        long passes = phase == 0 ? warmup : iterations ;
        for (long pass = 0 ; pass < passes ; pass++)
        {
            for (size_t q = 0 ; q < query_count ; q++)
            {
                const char *prefix = argv[first_query + q] ;
                const char *number = strrchr (prefix, '/') ;
                number = number == NULL ? prefix : number + 1 ;
                double seconds = 0 ;
                size_t count = 0 ;
                msg[0] = '\0' ;
                int query_info = run_query (prefix, folders, graph, (size_t) n, ng, query,
                    &seconds, &count, msg) ;
                if (query_info != GrB_SUCCESS)
                {
                    fprintf (stderr, "%s: %s pass %ld: info=%d %s\n",
                        number, phase == 0 ? "warmup" : "measured",
                        pass + 1, query_info, msg) ;
                    failed = results[q].failed = true ;
                    continue ;
                }
                if (phase == 0) continue ;
                if (pass > 0 && results[q].paths != count)
                {
                    fprintf (stderr, "%s: path count changed between iterations\n",
                        number) ;
                    failed = results[q].failed = true ;
                }
                results[q].seconds += seconds ;
                results[q].paths = count ;
            }
        }
    }
    printf ("query\ttime_seconds\tpaths\n") ;
    for (size_t q = 0 ; q < query_count ; q++)
    {
        if (results[q].failed) continue ;
        const char *prefix = argv[first_query + q] ;
        const char *number = strrchr (prefix, '/') ;
        number = number == NULL ? prefix : number + 1 ;
        printf ("%s\t%.9f\t%zu\n", number,
            results[q].seconds / iterations, results[q].paths) ;
    }
cleanup:
    if (graph != NULL)
        for (long k = 0 ; k < n ; k++) LAGraph_Delete (&graph[k].graph, NULL) ;
    LAGraph_Free ((void **) &graph, NULL) ;
    LAGraph_Free ((void **) &results, NULL) ;
    if (info != GrB_SUCCESS) fprintf (stderr, "info=%d %s\n", info, msg) ;
    LAGraph_Finalize (NULL) ;
    return (failed || info != GrB_SUCCESS ? EXIT_FAILURE : EXIT_SUCCESS) ;
}

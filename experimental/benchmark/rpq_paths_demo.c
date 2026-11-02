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

/** Load one NFA and its sources, call the API and release all query resources.
 * @param[in] files Query number, metadata path, sources path, then nl NFA paths.
 *     A path of "-" denotes an absent NFA label.
 * @param[in] G Borrowed graph decomposition, loaded once for the whole batch.
 * @param[in] nl Number of label slots shared by G and the NFA path list.
 * @param[in] query Selected public query function.
 * @param[out] seconds Receives the elapsed time of the public query call.
 * @param[out] count Receives the returned path count; valid only on success.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation/algorithm error.
 */
static int run_query
(
    char *const *files, LAGraph_Graph *G, size_t nl,
    QueryFunction query, double *seconds, size_t *count, char *msg
)
{
    FILE *meta = NULL ;
    GrB_Index *QS = NULL, *QF = NULL, *S = NULL ;
    LAGraph_Graph *R = NULL ;
    bool *inverse_labels = NULL ;
    LAGraph_RpqPath *paths = NULL ;
    size_t nqs = 0, nqf = 0, ns = 0, path_count = 0 ;
    int info = GrB_SUCCESS ;
    meta = fopen (files[1], "r") ;
    if (meta == NULL)
    {
        fprintf (stderr, "%s: %s\n", files[1], strerror (errno)) ;
        info = GrB_INVALID_VALUE ;
        goto cleanup ;
    }
    info = read_states (meta, &QS, &nqs, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = read_states (meta, &QF, &nqf, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    fclose (meta) ;
    meta = NULL ;
    info = read_sources (files[2], &S, &ns, msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &R, nl, sizeof (LAGraph_Graph), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &inverse_labels, nl, sizeof (bool), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    for (size_t a = 0 ; a < nl ; a++)
    {
        if (!strcmp (files[3 + a], "-")) continue ;
        info = read_graph (&R[a], files[3 + a], msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
    }

    double begin = LAGraph_WallClockTime ( ) ;
    info = query (&paths, &path_count, R, inverse_labels, nl,
        QS, nqs, QF, nqf, G, S, ns, false, msg) ;
    *seconds = LAGraph_WallClockTime ( ) - begin ;
    if (info != GrB_SUCCESS) goto cleanup ;

    *count = path_count ;
cleanup:
    if (meta != NULL) fclose (meta) ;
    if (R != NULL)
        for (size_t a = 0 ; a < nl ; a++) LAGraph_Delete (&R[a], NULL) ;
    LAGraph_2RpqPath_FreePaths (&paths, path_count, NULL) ;
    LAGraph_Free ((void **) &QS, NULL) ;
    LAGraph_Free ((void **) &QF, NULL) ;
    LAGraph_Free ((void **) &S, NULL) ;
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

// The Python launcher supplies: semantics warmup iterations nl graph_files...
// followed by query
// blocks: number meta_file sources_file nfa_files... (nl entries, "-" if absent).
int main (int argc, char **argv)
{
    if (argc < 10) return (EXIT_FAILURE) ;
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
    long n = strtol (argv[4], &end, 10) ;
    if (errno || query == NULL || *end != '\0' || n < 1 || n > (argc - 8) / 2 ||
        (argc - 5 - n) % (n + 3) != 0)
        return (EXIT_FAILURE) ;
    size_t query_count = (argc - 5 - n) / (n + 3) ;
    char msg [LAGRAPH_MSG_LEN] = "" ;
    LAGraph_Graph *G = NULL ;
    BenchmarkResult *results = NULL ;
    bool failed = false ;
    int info = LAGraph_Init (msg) ;
    if (info != GrB_SUCCESS)
    {
        fprintf (stderr, "initialization: info=%d %s\n", info, msg) ;
        return (EXIT_FAILURE) ;
    }
    info = LAGraph_Calloc ((void **) &G, (size_t) n, sizeof (LAGraph_Graph), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    info = LAGraph_Calloc ((void **) &results, query_count,
        sizeof (BenchmarkResult), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    GrB_Index ng = 0 ;
    for (long k = 0 ; k < n ; k++)
    {
        info = read_graph (&G[k], argv[5 + k], msg) ;
        if (info != GrB_SUCCESS) goto cleanup ;
        GrB_Index size = 0 ;
        info = GrB_Matrix_nrows (&size, G[k]->A) ;
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
                char **files = argv + 5 + n + q * (n + 3) ;
                double seconds = 0 ;
                size_t count = 0 ;
                msg[0] = '\0' ;
                int query_info = run_query (files, G, (size_t) n, query,
                    &seconds, &count, msg) ;
                if (query_info != GrB_SUCCESS)
                {
                    fprintf (stderr, "%s: %s pass %ld: info=%d %s\n",
                        files[0], phase == 0 ? "warmup" : "measured",
                        pass + 1, query_info, msg) ;
                    failed = results[q].failed = true ;
                    continue ;
                }
                if (phase == 0) continue ;
                if (pass > 0 && results[q].paths != count)
                {
                    fprintf (stderr, "%s: path count changed between iterations\n",
                        files[0]) ;
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
        const char *number = argv[5 + n + q * (n + 3)] ;
        printf ("%s\t%.9f\t%zu\n", number,
            results[q].seconds / iterations, results[q].paths) ;
    }
cleanup:
    if (G != NULL)
        for (long k = 0 ; k < n ; k++) LAGraph_Delete (&G[k], NULL) ;
    LAGraph_Free ((void **) &G, NULL) ;
    LAGraph_Free ((void **) &results, NULL) ;
    if (info != GrB_SUCCESS) fprintf (stderr, "info=%d %s\n", info, msg) ;
    LAGraph_Finalize (NULL) ;
    return (failed || info != GrB_SUCCESS ? EXIT_FAILURE : EXIT_SUCCESS) ;
}

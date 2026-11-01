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

/** Load one NFA and its sources, call the API and print its time and path count.
 * @param[in] files Query number, metadata path, sources path, then nl NFA paths.
 *     A path of "-" denotes an absent NFA label.
 * @param[in] G Borrowed graph decomposition, loaded once for the whole batch.
 * @param[in] nl Number of label slots shared by G and the NFA path list.
 * @param[in] query Selected public query function.
 * @param[out] msg Optional LAGRAPH_MSG_LEN-byte error buffer.
 * @return GrB_SUCCESS or an input/allocation/algorithm error.
 */
static int run_query
(
    char *const *files, LAGraph_Graph *G, size_t nl,
    QueryFunction query, char *msg
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
    double seconds = LAGraph_WallClockTime ( ) - begin ;
    if (info != GrB_SUCCESS) goto cleanup ;

    printf ("%s\t%.9f\t%zu\n", files[0], seconds, path_count) ;
    fflush (stdout) ;
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

// The Python launcher supplies: semantics nl graph_files... followed by query
// blocks: number meta_file sources_file nfa_files... (nl entries, "-" if absent).
int main (int argc, char **argv)
{
    if (argc < 8) return (EXIT_FAILURE) ;
    QueryFunction query = NULL ;
    if (!strcmp (argv[1], "all")) query = LAGraph_2RpqPath_AllPaths ;
    if (!strcmp (argv[1], "simple")) query = LAGraph_2RpqPath_AllSimple ;
    if (!strcmp (argv[1], "trails")) query = LAGraph_2RpqPath_AllTrails ;
    if (!strcmp (argv[1], "shortest")) query = LAGraph_2RpqPath_AllShortestPaths ;
    char *end = NULL ;
    long n = strtol (argv[2], &end, 10) ;
    if (query == NULL || *end != '\0' || n < 1 || n > (argc - 6) / 2 ||
        (argc - 3 - n) % (n + 3) != 0)
        return (EXIT_FAILURE) ;
    char msg [LAGRAPH_MSG_LEN] = "" ;
    LAGraph_Graph *G = NULL ;
    bool failed = false ;
    int info = LAGraph_Init (msg) ;
    if (info != GrB_SUCCESS)
    {
        fprintf (stderr, "initialization: info=%d %s\n", info, msg) ;
        return (EXIT_FAILURE) ;
    }
    info = LAGraph_Calloc ((void **) &G, (size_t) n, sizeof (LAGraph_Graph), msg) ;
    if (info != GrB_SUCCESS) goto cleanup ;
    GrB_Index ng = 0 ;
    for (long k = 0 ; k < n ; k++)
    {
        info = read_graph (&G[k], argv[3 + k], msg) ;
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
    printf ("query\ttime_seconds\tpaths\n") ;
    for (int k = 3 + (int) n ; k < argc ; k += (int) n + 3)
    {
        msg[0] = '\0' ;
        int query_info = run_query (argv + k, G, (size_t) n, query, msg) ;
        if (query_info != GrB_SUCCESS)
        {
            fprintf (stderr, "%s: info=%d %s\n", argv[k], query_info, msg) ;
            failed = true ;
        }
    }
cleanup:
    if (G != NULL)
        for (long k = 0 ; k < n ; k++) LAGraph_Delete (&G[k], NULL) ;
    LAGraph_Free ((void **) &G, NULL) ;
    if (info != GrB_SUCCESS) fprintf (stderr, "info=%d %s\n", info, msg) ;
    LAGraph_Finalize (NULL) ;
    return (failed || info != GrB_SUCCESS ? EXIT_FAILURE : EXIT_SUCCESS) ;
}

// Private instrumentation for LAGraph_2RpqPath.c. No GraphBLAS callback does I/O.
// Enabled by LG_RPQ_PROFILE=/path/prefix; one exclusive file per query.
#ifndef LG_RPQ_PATH_PROFILE_H
#define LG_RPQ_PATH_PROFILE_H
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <unistd.h>

#define LG_RPQ_COUNTERS(X) \
    X(temp_allocations) X(temp_records_written) X(product_calls) X(product_records) \
    X(union_calls) X(union_input_records) X(union_duplicates) \
    X(p_allocations) X(p_allocated_bytes) X(p_added_records) X(p_duplicate_records) \
    X(p_changed_cells) X(p_new_cells) \
    X(front_checks) X(front_bloom_negative) X(front_bloom_false_positive) \
    X(front_found) X(front_blocks_searched) X(front_comparisons) \
    X(merge_checks) X(merge_bloom_negative) X(merge_bloom_false_positive) \
    X(merge_found) X(merge_blocks_searched) X(merge_comparisons)
#define LG_RPQ_ENUM(n) LG_RPQ_##n,
typedef enum { LG_RPQ_COUNTERS (LG_RPQ_ENUM) LG_RPQ_COUNTER_COUNT } LG_RpqPath_Counter ;
#undef LG_RPQ_ENUM
#define LG_RPQ_NAME(n) #n,
static const char *LG_RpqPath_CounterNames[] = { LG_RPQ_COUNTERS (LG_RPQ_NAME) } ;
#undef LG_RPQ_NAME

typedef struct
{
    FILE *file ;
    char *buffer ;
    size_t used, capacity, iteration ;
    int64_t label ;
    const char *phase, *event ;
    double start, stamp, stats_ms, io_ms, next_sample ;
    bool failed ;
    atomic_uint_fast64_t counters[LG_RPQ_COUNTER_COUNT] ;
    // Reconstruction counters are single-threaded and cumulative per query.
    uint64_t pairs, propagate_calls, active_returns, depth, max_depth ;
    uint64_t reject_length, reject_shortest, reject_semantics, accepted ;
    uint64_t memo_attempts, memo_duplicates, prefixes, prefix_max, path_blocks ;
    uint64_t publish_attempts, publish_duplicates, published, published_length_sum ;
    uint64_t published_length_max, loaded_cells, dependencies, read_blocks, read_records ;
    uint64_t activate_steps, visit_inserts, visit_erases, visited_count, visited_capacity ;
    uint64_t load_pending, load_peak, distance_pending, distance_peak, distance_relaxations ;
    uint64_t targets, samples, visited_bytes ;
    double join_ms, memo_ms, publish_ms, prepare_ms, first_answer_ms ;
    bool count_limit ;
} LG_RpqPath_Profile ;

static double LG_RpqPath_ProfileClock (LG_RpqPath_Profile *p)
{
    return p == NULL ? 0 : LAGraph_WallClockTime () ;
}
static void LG_RpqPath_ProfileAdd (LG_RpqPath_Profile *p, LG_RpqPath_Counter key, uint64_t n)
{
    if (p != NULL) atomic_fetch_add_explicit (&p->counters[key], n, memory_order_relaxed) ;
}
static void LG_RpqPath_ProfileEvent (LG_RpqPath_Profile *p, const char *event)
{
    if (p == NULL) return ;
    p->event = event ;
    p->stamp = 1000 * (LAGraph_WallClockTime () - p->start) ;
}
static void LG_RpqPath_ProfileText (LG_RpqPath_Profile *p, const char *key, const char *value)
{
    if (p == NULL || p->failed) return ;
    // Metadata must remain one TSV field, including caller-supplied run IDs.
    char clean[512] ;
    size_t k = 0 ;
    for (; value[k] != '\0' && k + 1 < sizeof (clean) ; k++)
        clean[k] = value[k] == '\t' || value[k] == '\n' || value[k] == '\r' ? ' ' : value[k] ;
    clean[k] = '\0' ;
    char row[1024] ;
    int n = snprintf (row, sizeof (row), "%s\t%zu\t%" PRId64 "\t%s\t%.6f\t%s\t%s\n",
        p->phase, p->iteration, p->label, p->event, p->stamp, key, clean) ;
    if (n < 0 || (size_t) n >= sizeof (row) || p->used > SIZE_MAX - (size_t) n)
    { p->failed = true ; return ; }
    size_t needed = p->used + (size_t) n ;
    if (needed > p->capacity)
    {
        size_t cap = needed > SIZE_MAX / 2 ? needed : 2 * needed ;
        char *grown = realloc (p->buffer, cap) ;
        if (grown == NULL) { p->failed = true ; return ; }
        p->buffer = grown ; p->capacity = cap ;
    }
    memcpy (p->buffer + p->used, row, (size_t) n) ;
    p->used = needed ;
}
static void LG_RpqPath_ProfileU (LG_RpqPath_Profile *p, const char *key, uint64_t n)
{
    if (p == NULL) return ;
    char value[32] ; snprintf (value, sizeof (value), "%" PRIu64, n) ;
    LG_RpqPath_ProfileText (p, key, value) ;
}
static void LG_RpqPath_ProfileD (LG_RpqPath_Profile *p, const char *key, double n)
{
    if (p == NULL) return ;
    char value[64] ; snprintf (value, sizeof (value), "%.9f", n) ;
    LG_RpqPath_ProfileText (p, key, value) ;
}
static void LG_RpqPath_ProfileFlush (LG_RpqPath_Profile *p)
{
    if (p == NULL) return ;
    double start = LAGraph_WallClockTime () ;
    if (p->used && fwrite (p->buffer, 1, p->used, p->file) != p->used) p->failed = true ;
    if (fflush (p->file) != 0) p->failed = true ;
    p->used = 0 ;
    p->io_ms += 1000 * (LAGraph_WallClockTime () - start) ;
}
static LG_RpqPath_Profile *LG_RpqPath_ProfileOpen (LG_RpqPath_Profile *p)
{
    const char *prefix = getenv ("LG_RPQ_PROFILE") ;
    if (prefix == NULL || *prefix == '\0') return NULL ;
    static atomic_uint_fast64_t serial = ATOMIC_VAR_INIT (0) ;
    uint64_t id = atomic_fetch_add (&serial, 1) ;
    size_t size = strlen (prefix) + 100 ;
    char *name = malloc (size) ;
    if (name == NULL) return NULL ;
    snprintf (name, size, "%s.%ld.%" PRIu64 ".tsv", prefix, (long) getpid (), id) ;
    FILE *file = fopen (name, "wx") ;
    if (file == NULL) fprintf (stderr, "RPQ profile: cannot create %s\n", name) ;
    free (name) ;
    if (file == NULL) return NULL ;
    *p = (LG_RpqPath_Profile) { .file = file, .label = -1,
        .phase = "query", .event = "begin", .first_answer_ms = -1 } ;
    for (int k = 0 ; k < LG_RPQ_COUNTER_COUNT ; k++) atomic_init (&p->counters[k], 0) ;
    p->start = LAGraph_WallClockTime () ; p->next_sample = p->start + 0.1 ;
    if (fprintf (file, "phase\titeration\tlabel\tevent\telapsed_ms\tmetric\tvalue\n") < 0)
        p->failed = true ;
    LG_RpqPath_ProfileU (p, "schema", 1) ;
    LG_RpqPath_ProfileU (p, "pid", (uint64_t) getpid ()) ;
    LG_RpqPath_ProfileU (p, "call", id) ;
    const char *run = getenv ("LG_RPQ_PROFILE_RUN_ID") ;
    LG_RpqPath_ProfileText (p, "run_id", run == NULL ? "" : run) ;
    LG_RpqPath_ProfileText (p, "matrix_method", "AUTO") ;
    return p ;
}
static void LG_RpqPath_ProfileClose (LG_RpqPath_Profile *p)
{
    if (p == NULL) return ;
    LG_RpqPath_ProfileFlush (p) ;
    if (fclose (p->file) != 0) p->failed = true ;
    if (p->failed) fprintf (stderr, "RPQ profile: incomplete log (I/O or allocation failure)\n") ;
    free (p->buffer) ;
}
// Call time and completion time are disjoint. Waiting is profiling-only.
static int LG_RpqPath_ProfileOperation (LG_RpqPath_Profile *p,
    const char *name, GrB_Matrix matrix, double start, int info)
{
    if (p == NULL) return info ;
    double end = LAGraph_WallClockTime () ;
    if (info == GrB_SUCCESS && matrix != NULL) info = GrB_Matrix_wait (matrix, GrB_MATERIALIZE) ;
    double ready = LAGraph_WallClockTime () ;
    LG_RpqPath_ProfileEvent (p, name) ;
    LG_RpqPath_ProfileD (p, "call_ms", 1000 * (end - start)) ;
    LG_RpqPath_ProfileD (p, "wait_ms", 1000 * (ready - end)) ;
    LG_RpqPath_ProfileD (p, "total_ms", 1000 * (ready - start)) ;
    LG_RpqPath_ProfileD (p, "status", info) ;
    return info ;
}
#define LG_RPQ_CALL(name, matrix, call, cleanup) do { \
    double rpq_start = LG_RpqPath_ProfileClock (profile) ; \
    info = (call) ; \
    info = LG_RpqPath_ProfileOperation (profile, name, matrix, rpq_start, info) ; \
    if (info != GrB_SUCCESS) goto cleanup ; \
} while (0)

#endif

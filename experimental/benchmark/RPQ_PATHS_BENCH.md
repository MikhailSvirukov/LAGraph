# RPQ path benchmark

Build from the LAGraph repository root (SuiteSparse:GraphBLAS 10.1+ is required;
10.5.0 is the tested version):

```bash
cmake -S . -B build-paths -DCMAKE_BUILD_TYPE=Release -DBUILD_TESTING=ON
cmake --build build-paths --target rpq_paths_demo --parallel
```

For a GraphBLAS build outside the standard search paths, add
`-DGraphBLAS_DIR=/path/to/GraphBLAS/build` to the configure command.
The executable is `build-paths/experimental/benchmark/rpq_paths_demo`; CMake builds
it together with the LAGraph libraries it uses. `main.c` is not involved.

Run the Python launcher with the original query and matrix directories:

```bash
python3 experimental/benchmark/rpq_paths_bench.py \
  wikidata-queries-mm /path/to/wikidata-mm \
  --semantics trails --warmup 1 --iterations 5 --build-dir build-paths \
  > results.tsv 2> errors.log
```

The graph directory is scanned non-recursively for positive numeric filenames
with `.txt`, `.mtx`, or `.mat` extensions, such as `1000.txt`. Auxiliary files
such as `edges.txt` and `vertices.txt` are ignored. Individual files and explicit
mappings such as `141=/path/to/matrix.txt` are also accepted. Duplicate graph
labels and directories with no matching matrices are errors.

Queries use the original format from `main.c`, without conversion:

```text
queries/
  1/
    meta.txt
    141.txt
    -62.txt
    raw.txt
```

For example, `meta.txt` contains:

```text
12 0
1 1
1 3
2 141 -62
```

The first pair is the source and destination, with one-based vertex IDs and `0`
meaning unrestricted. Next are counted lists of initial and final NFA states
(one-based). The last counted list contains signed labels. Each declared NFA
matrix is named `<signed-label>.txt`. A negative label uses the graph matrix
for its absolute label with `inverse_labels = true`. `raw.txt` is ignored.
Queries are processed in numeric order. There are no temporary converted files,
source-list files, or flat `<number>_meta.txt` inputs.

Matrices are read directly by `LAGraph_MMRead`, as in `main.c`. Vertex IDs,
matrix dimensions and entries are preserved. Storage is set to row-major for
LAGraph. No padding, resizing, relabeling or transposed-matrix cache is added.
The algorithm requires square graph matrices with matching dimensions **within
each query**; NFA label matrices must also agree within a query. Matrices unused
by a query are not passed to it. Dimension errors are returned by the algorithm.

A fixed source runs forward. A fixed destination with a free source runs
backward from that destination, swapping the initial/final NFA state sets and
setting `inverse = true`, as in `main.c`. Two free endpoints use all graph
vertices as sources. Two fixed endpoints produce an explicit error: the public
API has no target filter. Results are not filtered by the driver. With
`shortest`, minima are per endpoint in the chosen traversal direction; for a
backward query, these endpoints are the original sources.

`--semantics` accepts `all` (default), `simple`, `trails`, or `shortest`.
`--warmup N` runs N unreported full-batch passes (default 0).
`--iterations N` runs N measured full-batch passes (default 1, positive).
All warmup passes finish before measured passes begin. Each query's reported
time is the arithmetic mean of its measured calls, excluding warmup.

Graph matrices are loaded once for the entire process. Each invocation loads
its NFA and creates a fresh algorithm workspace; the query's inputs, workspace
and returned paths are released before the next invocation. File loading and
freeing the returned paths are outside the timed public API call. The
algorithm's path-length bound applies (60000 edges by default). Reconstruction
stops successfully after collecting 100000 distinct paths by default. With
`shortest`, this can miss a shorter path found later in traversal; its final
filter only compares the collected prefix, so the returned count may be lower.

Output is TSV on stdout, one row per successful query:

```text
query   time_seconds   paths
1       0.001234567    42
2       0.000456789    3
```

Errors go to stderr. A query with any failed invocation is omitted from the
table; later queries and passes still run, and the process returns nonzero.
Changing path counts between measured passes are also reported as an error.

To identify a query that crashes before the final table is printed, set
`LAGRAPH_RPQ_TRACE=1` when running the launcher. The driver writes and flushes
the query number and pass to stderr immediately before each invocation. For
example, prefix the launch command with `LAGRAPH_RPQ_TRACE=1` and use
`2> trace.log`; the last trace line identifies the active query.

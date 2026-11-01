# RPQ path benchmark

Build the driver:

```bash
cmake -S . -B build
cmake --build build --target rpq_paths_demo -j4
```

Run from the repository root, passing the queries directory and graph
decomposition files directly:

```bash
python3 experimental/benchmark/rpq_paths_bench.py \
  /path/to/queries \
  /path/to/graph/1.txt /path/to/graph/2.txt \
  --semantics trails --build-dir build
```

Graph filenames identify positive label numbers: `1.txt`, `0002.mat`, `3.mtx`.
Their contents must be square Matrix Market matrices with equal dimensions.
Numeric values are cast to Boolean adjacency values. Pass every graph label
used by the queries; no decomposition or regex conversion is performed.

`--semantics` accepts `all` (default), `simple`, `trails`, or `shortest`.
The existing algorithm's reconstruction depth and arena limits apply.

Queries use the `la-rpq/Scripts/sparql-to-fa` / `pokec-queries-to-fa` layout:

```text
queries/
  1/
    meta.txt
    1.txt
    -2.txt
  2/
    meta.txt
    ...
```

For example, `meta.txt` can contain:

```text
12 0
1 1
1 3
2 1 -2
```

The first line gives source and target vertices; `0` means unrestricted.
The benchmark supports a fixed source or all sources (`0`), with an unrestricted
target (`0`). A nonzero target is rejected with an error because the public API
has no target parameter.
The next two lists contain the count and one-based initial/final NFA states.
The last list contains the count and signed label IDs: `-2` uses graph matrix
`2.txt` backwards and NFA matrix `-2.txt`. Vertex and state IDs are one-based
in metadata and are converted to the algorithm's zero-based indices.
`raw.txt` is ignored. Numbered query directories are processed in numeric order.

The graph is loaded once. Each NFA is loaded before timing. One wall-clock
measurement surrounds the complete public algorithm call, including predecessor
matrix construction and path reconstruction. Loading matrices and freeing paths
are outside the measured interval. The reported count is the `path_count`
returned by the selected public function, without additional result processing.
The driver passes `inverse = false`; signed labels still control the direction
of individual labels through `inverse_labels`.

Output is tab-separated, one successful query per row:

```text
query   time_seconds   paths
1       0.001234567    42
2       0.000456789    3
```

Redirect stdout to save the table. Errors go to stderr, subsequent queries still
run, and the script returns a nonzero exit status if any query failed.

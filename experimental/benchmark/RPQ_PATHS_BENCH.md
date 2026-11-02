# RPQ path benchmark

Build the driver:

```bash
cmake -S . -B build
cmake --build build --target rpq_paths_demo -j4
```

Pass a queries directory and the graph decomposition files:

```bash
python3 experimental/benchmark/rpq_paths_bench.py \
  /path/to/queries /path/to/graph/a.mtx /path/to/graph/b.mtx \
  --semantics trails --warmup 1 --iterations 5 --build-dir build
```

The input format matches `data/rpq_data` and the loader in
`experimental/test/test_2Rpq.c`:

```text
queries/
  1_meta.txt
  1_sources.txt
  1_a.mtx
  2_meta.txt
  2_sources.txt
  2_a.mtx
  2_b.mtx
```

`<number>_meta.txt` contains two counted lists: initial and final NFA states.
For example, one initial state (1) and two final states (2 and 3):

```text
1 1
2 2 3
```

`<number>_sources.txt` contains whitespace-separated graph source vertices,
without a count. An empty file means an empty source set. Vertex and state IDs
are one-based in these files and converted to zero-based API indices.

`<number>_<label>.mtx` is the NFA adjacency matrix for that label. An absent file
means an absent NFA label (`NULL` in the API). Supply a graph matrix for every
label used by the queries. Graph matrix filenames define labels by their stems:
`a.mtx` corresponds to `<number>_a.mtx`. For other filenames, specify the label
explicitly, for example `a=/path/to/labels_a.mtx`.

Graph and NFA files must contain square Matrix Market matrices. Graph matrices
must share dimensions; NFA matrices must share dimensions within each query.
Numeric values are cast to Boolean adjacency values. No decomposition or regex
conversion is performed. Queries are processed in numeric order.

The graph is loaded once. Each NFA and its sources are loaded before timing.
One wall-clock measurement surrounds the complete public algorithm call,
including predecessor matrix construction and path reconstruction. Loading
inputs and freeing returned paths are outside the measured interval. The
reported count is the returned `path_count`, without additional processing.
`inverse` and all `inverse_labels` flags are false.

`--semantics` accepts `all` (default), `simple`, `trails`, or `shortest`.
The algorithm's reconstruction depth and arena limits apply.

`--warmup N` runs N complete unreported passes over the query batch (default 0).
`--iterations N` runs N measured complete passes (default 1, must be positive).
All warmup passes finish before measurements start. For example, with queries
1 and 2, `--warmup 1 --iterations 2` runs warmup [1, 2], measured [1, 2],
measured [1, 2]. Each output row reports the arithmetic mean of that query's
measured times and its path count. Warmup timings are discarded.

All passes share one process, one GraphBLAS initialization and the loaded graph.
Each query invocation reloads its NFA and sources, creates a fresh algorithm
workspace, and releases the workspace, query inputs and returned paths before
the next invocation. There is no reuse of predecessor matrices or reconstruction
state. If any invocation fails, its query row is omitted and the exit status is
nonzero; other queries and passes still run. Changing path counts between
measured passes is also reported as an error.

For the repository examples, queries 1–4 use `a.mtx` and `b.mtx`, while queries
5–6 use a different graph (`labels_a.mtx` and `labels_b.mtx`). Put the desired
query files in a separate directory for each graph. For example:

```bash
mkdir -p /tmp/rpq-queries-1-4
cp data/rpq_data/[1-4]_*.mtx data/rpq_data/[1-4]_meta.txt \
  data/rpq_data/[1-4]_sources.txt /tmp/rpq-queries-1-4/
python3 experimental/benchmark/rpq_paths_bench.py \
  /tmp/rpq-queries-1-4 data/rpq_data/a.mtx data/rpq_data/b.mtx \
  --semantics trails --build-dir build
```

For queries 5–6, use graph arguments
`a=data/rpq_data/labels_a.mtx b=data/rpq_data/labels_b.mtx`.

Output is tab-separated, one successful query per row:

```text
query   time_seconds   paths
1       0.001234567    42
2       0.000456789    3
```

Redirect stdout to save the table. Input discovery errors stop the launcher.
Driver errors go to stderr, subsequent queries still run, and the script returns
a nonzero exit status if any query failed.

#!/usr/bin/env python3
"""Run predecessor-based RPQ benchmarks on prepared Matrix Market inputs."""

import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("queries", type=Path,
                        help="directory of numbered query folders containing meta.txt")
    parser.add_argument("matrices", nargs="+",
                        help="matrix directory, individual <label>.txt/.mtx files, or <label>=<path>")
    parser.add_argument("--semantics", choices=("all", "simple", "trails", "shortest"),
                        default="all")
    parser.add_argument("--warmup", type=int, default=0,
                        help="unreported passes over the full batch (default: 0)")
    parser.add_argument("--iterations", type=int, default=1,
                        help="measured passes over the full batch (default: 1)")
    parser.add_argument("--build-dir", type=Path,
                        default=Path(__file__).resolve().parents[2] / "build",
                        help="LAGraph CMake build directory (default: build)")
    args = parser.parse_args()
    if args.warmup < 0 or args.iterations < 1:
        parser.error("--warmup must be nonnegative and --iterations must be positive")
    driver = args.build_dir / "experimental/benchmark/rpq_paths_demo"
    if not driver.is_file():
        parser.error(f"missing {driver}; build the rpq_paths_demo CMake target first")
    if not args.queries.is_dir():
        parser.error(f"not a queries directory: {args.queries}")
    queries = sorted((p for p in args.queries.iterdir()
                      if p.is_dir() and p.name.isdecimal() and (p / "meta.txt").is_file()),
                     key=lambda p: int(p.name))
    if not queries:
        parser.error("no numbered query folders containing meta.txt")
    inputs = []
    for value in args.matrices:
        path = Path(value)
        if path.is_dir():
            files = sorted((p for p in path.iterdir()
                            if p.is_file() and p.stem.isdecimal() and int(p.stem) > 0
                            and p.suffix.lower() in (".txt", ".mtx", ".mat")),
                           key=lambda p: (int(p.stem), p.name))
            if not files:
                parser.error(f"no numeric matrix files (.txt/.mtx/.mat) in directory: {path}")
            inputs.extend(str(p) for p in files)
        else:
            inputs.append(value)
    matrices = {}
    for value in inputs:
        label, separator, filename = value.partition("=")
        path = Path(filename if separator else value)
        if not separator:
            label = path.stem
        if not label or "/" in label or "\\" in label or not path.is_file():
            parser.error(f"expected a matrix directory, <label>.txt/.mtx, or <label>=<existing-file>: {value}")
        if label in matrices:
            parser.error(f"duplicate graph label: {label}")
        if not label.isdecimal() or int(label) < 1 or int(label) > 2**63 - 1:
            parser.error(f"expected a positive integer graph label: {label}")
        label = str(int(label))
        if label in matrices:
            parser.error(f"duplicate graph label: {label}")
        matrices[label] = path
    command = [str(driver.resolve()), args.semantics, str(args.warmup),
               str(args.iterations), str(len(matrices))]
    for label, path in matrices.items():
        command.extend([label, str(path.resolve())])
    command.extend(str(directory.resolve()) for directory in queries)
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())

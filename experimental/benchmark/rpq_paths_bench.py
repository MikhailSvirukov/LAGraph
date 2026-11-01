#!/usr/bin/env python3
"""Run predecessor-based RPQ benchmarks on prepared Matrix Market inputs."""

import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("queries", type=Path, help="directory of numbered query directories")
    parser.add_argument("matrices", nargs="+", type=Path,
                        help="graph decomposition files: <positive-label>.txt/.mtx/.mat")
    parser.add_argument("--semantics", choices=("all", "simple", "trails", "shortest"),
                        default="all")
    parser.add_argument("--build-dir", type=Path,
                        default=Path(__file__).resolve().parents[2] / "build",
                        help="LAGraph CMake build directory (default: build)")
    args = parser.parse_args()
    driver = args.build_dir / "experimental/benchmark/rpq_paths_demo"
    if not driver.is_file():
        parser.error(f"missing {driver}; build the rpq_paths_demo CMake target first")
    if not args.queries.is_dir():
        parser.error(f"not a queries directory: {args.queries}")
    queries = sorted((p for p in args.queries.iterdir()
                      if p.is_dir() and p.name.isdecimal() and (p / "meta.txt").is_file()),
                     key=lambda p: int(p.name))
    if not queries:
        parser.error("no numbered query directories containing meta.txt")
    labels = set()
    for path in args.matrices:
        if not path.is_file() or not path.stem.isdecimal() or int(path.stem) < 1:
            parser.error(f"expected a graph matrix named <positive-label>.<extension>: {path}")
        label = int(path.stem)
        if label in labels:
            parser.error(f"duplicate graph label: {label}")
        labels.add(label)
    command = [str(driver.resolve()), args.semantics, str(len(args.matrices)),
               *(str(p.resolve()) for p in args.matrices),
               *(str(p.resolve()) for p in queries)]
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())

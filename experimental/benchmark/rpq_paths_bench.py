#!/usr/bin/env python3
"""Run predecessor-based RPQ benchmarks on prepared Matrix Market inputs."""

import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("queries", type=Path,
                        help="numbered query folders with meta.txt, or flat <number>_meta.txt files")
    parser.add_argument("matrices", nargs="+",
                        help="graph matrices: <label>.txt/.mtx or <label>=<path>")
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
    layout = "folders" if queries else "flat"
    if layout == "flat":
        queries = sorted((p for p in args.queries.glob("*_meta.txt")
                          if p.is_file() and p.name[:-9].isdecimal()),
                         key=lambda p: int(p.name[:-9]))
    if not queries:
        parser.error("no numbered query folders or <number>_meta.txt files")
    matrices = {}
    for value in args.matrices:
        label, separator, filename = value.partition("=")
        path = Path(filename if separator else value)
        if not separator:
            label = path.stem
        if not label or "/" in label or "\\" in label or not path.is_file():
            parser.error(f"expected <label>.mtx or <label>=<existing-file>: {value}")
        if label in matrices:
            parser.error(f"duplicate graph label: {label}")
        if layout == "folders":
            if not label.isdecimal() or int(label) < 1 or int(label) > 2**63 - 1:
                parser.error(f"folder format requires positive integer graph labels: {label}")
            label = str(int(label))
            if label in matrices:
                parser.error(f"duplicate graph label: {label}")
        matrices[label] = path
    command = [str(driver.resolve()), args.semantics, str(args.warmup),
               str(args.iterations), layout, str(len(matrices))]
    for label, path in matrices.items():
        command.extend([label, str(path.resolve())])
    for meta in queries:
        if layout == "folders":
            command.append(str(meta.resolve()))
            continue
        number = meta.name[:-9]
        sources = meta.with_name(f"{number}_sources.txt")
        if not sources.is_file():
            parser.error(f"missing sources file: {sources}")
        nfa = {p.name[len(number) + 1:-4]: p
               for p in args.queries.glob(f"{number}_*.mtx") if p.is_file()}
        if not nfa:
            parser.error(f"no NFA matrices for query {number}")
        if missing := nfa.keys() - matrices.keys():
            parser.error(f"query {number}: missing graph labels: {', '.join(sorted(missing))}")
        command.append(str(meta.with_name(number).resolve()))
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())

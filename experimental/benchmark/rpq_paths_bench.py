#!/usr/bin/env python3
"""Run predecessor-based RPQ benchmarks on prepared Matrix Market inputs."""

import argparse
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("queries", type=Path,
                        help="directory containing <number>_meta.txt and <number>_sources.txt")
    parser.add_argument("matrices", nargs="+",
                        help="graph matrices: <label>.mtx or <label>=<path>")
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
    queries = sorted((p for p in args.queries.glob("*_meta.txt")
                      if p.is_file() and p.name[:-9].isdecimal()),
                     key=lambda p: int(p.name[:-9]))
    if not queries:
        parser.error("no <number>_meta.txt query files")
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
        matrices[label] = path
    command = [str(driver.resolve()), args.semantics, str(len(matrices)),
               *(str(p.resolve()) for p in matrices.values())]
    for meta in queries:
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
        command.extend([number, str(meta.resolve()), str(sources.resolve()),
                        *(str(nfa[label].resolve()) if label in nfa else "-"
                          for label in matrices)])
    return subprocess.run(command, check=False).returncode


if __name__ == "__main__":
    sys.exit(main())

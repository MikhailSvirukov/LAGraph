#!/usr/bin/env python3
"""Aggregate LG_RPQ_PROFILE TSV files; standard library only, no plots."""
import argparse
import csv
import glob
import sys
from collections import defaultdict
from decimal import Decimal, InvalidOperation
from pathlib import Path


def read(path):
    with open(path, newline='') as stream:
        reader = csv.DictReader(stream, delimiter='\t')
        if reader.fieldnames is None:
            print(f'{path}: empty profile (interrupted before header flush)', file=sys.stderr)
            return
        required = {'phase', 'iteration', 'label', 'event', 'elapsed_ms', 'metric', 'value'}
        if set(reader.fieldnames or []) != required:
            raise ValueError(f'{path}: unexpected profile header')
        for row in reader:
            if None in row or any(row[k] is None for k in required):
                print(f'{path}: ignoring incomplete final record', file=sys.stderr)
                continue
            yield row


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', nargs='+', help='profile files or glob patterns')
    parser.add_argument('--by', choices=['query', 'iteration', 'label', 'sample'], default='query')
    parser.add_argument('--all', action='store_true', help='include every metric; numeric columns have .sum/.max/.last')
    parser.add_argument('--columns', help='comma-separated output column glob patterns (implies --all)')
    args = parser.parse_args()
    paths = sorted({p for pattern in args.files for p in glob.glob(pattern)})
    if not paths:
        parser.error('no input files matched')
    output = []
    for path in paths:
        groups = defaultdict(dict)
        metadata = {'file': str(Path(path))}
        complete = False
        for row in read(path):
            phase, event, metric = row['phase'], row['event'], row['metric']
            if phase == 'query' and event == 'begin':
                metadata[metric] = row['value']
            if phase == 'query' and event == 'end' and metric == 'status':
                complete = True
            if args.by == 'query':
                group = ()
            elif args.by == 'iteration':
                if phase != 'traverse' or row['iteration'] == '0':
                    continue
                group = (row['iteration'],)
            elif args.by == 'label':
                if phase != 'traverse' or row['label'] == '-1':
                    continue
                group = (row['iteration'], row['label'])
            else:
                if phase != 'reconstruct' or event not in ('sample', 'final'):
                    continue
                group = (row['iteration'],)
            key = f'{phase}.{event}.{metric}'
            values = groups[group]
            try:
                number = Decimal(row['value'])
            except InvalidOperation:
                values[key + '.last'] = row['value']
            else:
                values[key + '.sum'] = values.get(key + '.sum', Decimal(0)) + number
                values[key + '.max'] = max(values.get(key + '.max', number), number)
                values[key + '.last'] = number
            values['elapsed_ms'] = row['elapsed_ms']
        if not groups and args.by == 'query':
            groups[()] = {}
        for group, values in groups.items():
            result = dict(metadata, complete=int(complete), **values)
            if group:
                result['sample' if args.by == 'sample' else 'iteration'] = group[0]
                if len(group) == 2:
                    result['label'] = group[1]
            output.append(result)
    # Compact query view: sums of per-iteration work and final cumulative state.
    compact = [
        'file', 'run_id', 'pid', 'call', 'semantics', 'complete',
        'query.end.status.last', 'query.end.paths.last', 'query.end.total_ms.last',
        'query.end.snapshot_ms.last', 'query.end.io_ms.last',
        'traverse.end.iterations.last', 'traverse.end.total_ms.last',
        'traverse.mxm1.total_ms.sum', 'traverse.mxm2.total_ms.sum',
        'traverse.front_union.total_ms.sum', 'traverse.front_select.total_ms.sum',
        'traverse.P_merge.total_ms.sum', 'traverse.iteration_end.cleanup_ms.sum',
        'traverse.begin.frontier_nvals.max', 'traverse.mxm1.H_records.max',
        'traverse.products_done.C_records.max', 'traverse.P_merge.P_records.last',
        'traverse.P_merge.P_owned_bytes.last', 'traverse.products_done.pool_bytes.max',
        'traverse.iteration_end.p_added_records.sum', 'traverse.iteration_end.p_duplicate_records.sum',
        'reconstruct.end.total_ms.last', 'reconstruct.final.pairs.last',
        'reconstruct.final.prefixes.last', 'reconstruct.final.memo_duplicates.last',
        'reconstruct.final.reject_semantics.last', 'reconstruct.final.max_depth.last',
        'reconstruct.final.memo_bytes.last', 'reconstruct.final.node_bytes.last',
        'reconstruct.final.first_answer_ms.last', 'reconstruct.final.count_limit.last',
    ]
    columns = sorted({key for row in output for key in row}) if args.all or args.columns or args.by != 'query' else compact
    if args.columns:
        from fnmatch import fnmatchcase
        patterns = args.columns.split(',')
        columns = [key for key in columns if any(fnmatchcase(key, pattern) for pattern in patterns)]
    writer = csv.DictWriter(sys.stdout, fieldnames=columns, delimiter='\t', extrasaction='ignore', lineterminator='\n')
    writer.writeheader()
    writer.writerows(output)


if __name__ == '__main__':
    main()

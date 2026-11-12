"""Run with python3 -m unittest discover -s experimental/benchmark -p test_rpq_profile.py."""
import csv
import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('rpq_profile.py')


class AggregationTest(unittest.TestCase):
    def aggregate(self, rows, *options):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'profile.tsv'
            path.write_text('phase\titeration\tlabel\tevent\telapsed_ms\tmetric\tvalue\n' + rows)
            result = subprocess.run([sys.executable, str(SCRIPT), str(path), *options],
                                    check=True, text=True, capture_output=True)
            return list(csv.DictReader(io.StringIO(result.stdout), delimiter='\t')), result.stderr

    def test_empty_crash_file(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'empty.tsv'
            path.touch()
            result = subprocess.run([sys.executable, str(SCRIPT), str(path)],
                                    check=True, text=True, capture_output=True)
            rows = list(csv.DictReader(io.StringIO(result.stdout), delimiter='\t'))
            self.assertEqual(rows[0]['complete'], '0')
            self.assertIn('empty profile', result.stderr)

    def test_time_sums_and_cumulative_count(self):
        rows, _ = self.aggregate(
            'traverse\t1\t0\tmxm1\t1\ttotal_ms\t1.25\n'
            'traverse\t2\t0\tmxm1\t2\ttotal_ms\t2.75\n'
            'reconstruct\t1\t-1\tsample\t3\tpairs\t7\n'
            'reconstruct\t2\t-1\tfinal\t4\tpairs\t12\n'
            'query\t0\t-1\tend\t5\tstatus\t0\n')
        self.assertEqual(rows[0]['traverse.mxm1.total_ms.sum'], '4.00')
        self.assertEqual(rows[0]['reconstruct.final.pairs.last'], '12')
        self.assertEqual(rows[0]['complete'], '1')

    def test_exact_large_integer_and_iteration_groups(self):
        rows, _ = self.aggregate(
            'traverse\t1\t0\tmxm2\t1\tC_records\t9007199254740993\n'
            'traverse\t2\t0\tmxm2\t2\tC_records\t2\n', '--by', 'iteration')
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0]['traverse.mxm2.C_records.last'], '9007199254740993')
        self.assertEqual(rows[0]['complete'], '0')

    def test_partial_record_and_selected_columns(self):
        rows, stderr = self.aggregate(
            'query\t0\t-1\tend\t1\tpaths\t3\ntraverse\t1\t',
            '--columns', 'complete,query.end.paths.last')
        self.assertEqual(rows, [{'complete': '0', 'query.end.paths.last': '3'}])
        self.assertIn('incomplete final record', stderr)


if __name__ == '__main__':
    unittest.main()

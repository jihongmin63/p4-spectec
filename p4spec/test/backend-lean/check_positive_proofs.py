"""Exercise the positive proof runner against real generated Lean semantics."""
import argparse
import json
from pathlib import Path
import subprocess
import signal
import sys
import tempfile
import time
import unittest

sys.dont_write_bytecode = True
import prove_positive_cases as runner

parser = argparse.ArgumentParser()
parser.add_argument('--exe', required=True)
args, tests = parser.parse_known_args()
EXE = str(Path(args.exe).resolve())
HERE = Path(__file__).resolve().parent


class PositiveProofs(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.spec = self.root / 'spec.watsup'
        self.spec.write_text((HERE / 'case-obligation.watsup').read_text())
        self.manifest = self.root / 'cases.tsv'
        self.output = self.root / 'run'
        self.report = self.root / 'report.md'

    def run_proofs(self, rows, *flags):
        self.manifest.write_text(''.join(rows))
        result = subprocess.run([
            sys.executable, str(HERE / 'prove_positive_cases.py'), '--exe', EXE,
            '--spec', str(self.spec), '--manifest', str(self.manifest),
            '--output', str(self.output), '--report', str(self.report),
            '--limit', '0', '--fuel', '32', *flags], capture_output=True, text=True)
        self.assertTrue((self.output / 'results.json').exists(), result.stdout + result.stderr)
        return result, json.loads((self.output / 'results.json').read_text())

    def test_smallest_first_and_only_kernel_proof_counts(self):
        result, report = self.run_proofs([
            f'accept\t{HERE / "case-semicolon.p4"}\t{HERE / "case-oracle.lean"}\n',
            f'reject\t{HERE / "case-empty.p4"}\n',
            f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n'])
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual([r['case_id'] for r in report['cases']], [2, 0])
        self.assertEqual([r['status'] for r in report['cases']], ['proved', 'unmatch'])
        self.assertEqual(report['proved'], 1)
        self.assertIn('propext', report['cases'][0]['axioms'])
        self.assertTrue(self.report.is_file())
        self.assertEqual(result.stdout.splitlines()[0], 'case\tseconds\tsuccess')
        self.assertEqual(len(result.stdout.splitlines()), 4)
        lines = self.report.read_text().splitlines()
        self.assertEqual(lines[2:4], ['| Case | Seconds | Success |', '|---|---:|---|'])
        self.assertEqual(len(lines), 7)
        self.assertIn('| case_2 |', lines[4])
        self.assertTrue(lines[4].endswith('| PASS |'))
        self.assertTrue(lines[5].endswith('| FAIL |'))
        self.assertTrue(lines[6].endswith('| FAIL |'))
        # A second invocation cannot silently overwrite the evidence.
        again = subprocess.run([sys.executable, str(HERE / 'prove_positive_cases.py'),
            '--exe', EXE, '--output', str(self.output), '--report', str(self.report)],
            capture_output=True, text=True)
        self.assertNotEqual(again.returncode, 0)
        self.assertEqual(json.loads((self.output / 'results.json').read_text()), report)

    def test_fuel_exhaustion_is_not_a_proof(self):
        for flags in ([], ['--kernel-only']):
            with self.subTest(flags=flags):
                self.output = self.root / ('kernel' if flags else 'native')
                self.report = self.output.with_suffix('.md')
                result, report = self.run_proofs([
                    f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n'],
                    '--fuel', '1', *flags)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(report['cases'][0]['status'], 'outOfFuel')
                self.assertEqual(report['proved'], 0)

    def test_success_with_wrong_oracle_is_not_a_proof(self):
        self.spec.write_text(self.spec.read_text().replace('p4programIR = OK', 'p4programIR = OK | BAD'))
        oracle = self.root / 'wrong.lean'
        oracle.write_text('p4programIR.BAD\n')
        for flags in ([], ['--kernel-only']):
            with self.subTest(flags=flags):
                self.output = self.root / ('kernel' if flags else 'native')
                self.report = self.output.with_suffix('.md')
                result, report = self.run_proofs([
                    f'accept\t{HERE / "case-empty.p4"}\t{oracle}\n'], *flags)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(report['cases'][0]['status'], 'proof-error')
                self.assertEqual(report['proved'], 0)

    def test_external_choice_is_explicitly_unsupported(self):
        self.spec.write_text(self.spec.read_text().split('rule Program_ok/empty:')[0]
                            .replace('relation Program_ok:', 'extern relation Program_ok:'))
        for flags in ([], ['--kernel-only']):
            with self.subTest(flags=flags):
                self.output = self.root / ('kernel' if flags else 'native')
                self.report = self.output.with_suffix('.md')
                result, report = self.run_proofs([
                    f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n'], *flags)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(report['cases'][0]['status'], 'unsupportedChoice')

    def test_case_ids_never_rewrite_oracle_string_literals(self):
        self.spec.write_text(self.spec.read_text().replace('p4programIR = OK',
                            'p4programIR = text').replace(': OK', ': "case_0"'))
        oracle = self.root / 'literal.lean'
        oracle.write_text('"case_0"\n')
        result, report = self.run_proofs([
            f'reject\t{HERE / "case-semicolon.p4"}\n',
            f'accept\t{HERE / "case-empty.p4"}\t{oracle}\n'])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(report['cases'][0]['status'], 'proved')

    def test_timeout_stops_descendant_processes(self):
        marker = self.root / 'orphan'
        child = f'import time; from pathlib import Path; time.sleep(0.3); Path({str(marker)!r}).touch()'
        parent = f'import subprocess, sys, time; subprocess.Popen([sys.executable, "-c", {child!r}]); time.sleep(5)'
        phase, _, _ = runner.run_phase([sys.executable, '-c', parent], self.root,
                                      'timeout', 0.1)
        self.assertIsNone(phase['returncode'])
        time.sleep(0.5)
        self.assertFalse(marker.exists(), 'timed-out descendant continued running')

    def test_kernel_mode_proves_beyond_native_constructor_limit(self):
        self.spec.write_text(self.spec.read_text() + ''.join(
            f'\ndec $padding{i}() : nat\ndef $padding{i}() = 0\n' for i in range(260)))
        result, report = self.run_proofs([
            f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n'],
            '--kernel-only')
        self.assertEqual(result.returncode, 0, json.dumps(report, indent=2))
        self.assertEqual(report['cases'][0]['status'], 'proved')

    def test_each_case_gets_its_own_deadline_after_shared_setup(self):
        result, report = self.run_proofs([
            f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n',
            f'accept\t{HERE / "case-semicolon.p4"}\t{HERE / "case-oracle.lean"}\n'],
            '--case-timeout', '0.01')
        self.assertEqual(result.returncode, 1)
        self.assertEqual(report['status'], 'complete')
        self.assertEqual(report['proved'], 0)
        self.assertEqual([c['status'] for c in report['cases']], ['timeout', 'timeout'])
        self.assertTrue(all(c['seconds'] >= 0.01 for c in report['cases']))
        self.assertTrue((self.output / 'Semantics.olean').is_file())

    def test_case_deadline_stops_descendant_processes(self):
        marker = self.root / 'orphan'
        child = f'import time; from pathlib import Path; time.sleep(0.3); Path({str(marker)!r}).touch()'
        parent = f'import subprocess, sys, time; subprocess.Popen([sys.executable, "-c", {child!r}]); time.sleep(5)'
        previous = signal.signal(signal.SIGALRM, runner.expire_case)
        try:
            signal.setitimer(signal.ITIMER_REAL, 0.1)
            with self.assertRaises(runner.CaseTimeout):
                runner.run_phase([sys.executable, '-c', parent], self.root, 'deadline', 5)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, previous)
        time.sleep(0.5)
        self.assertFalse(marker.exists(), 'descendant survived the case deadline')

    def test_skip_proved_from_retries_only_unproved_cases(self):
        rows = [f'accept\t{HERE / "case-semicolon.p4"}\t{HERE / "case-oracle.lean"}\n',
                f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n']
        result, first = self.run_proofs(rows)
        self.assertEqual([(r['case_id'], r['status']) for r in first['cases']],
                         [(1, 'proved'), (0, 'unmatch')])
        previous = self.output
        self.output, self.report = self.root / 'retry', self.root / 'retry.md'
        result, retry = self.run_proofs(rows, '--skip-proved-from', str(previous))
        self.assertEqual(result.returncode, 1)
        self.assertEqual([r['case_id'] for r in retry['cases']], [0])
        self.assertEqual(retry['skipped_proved']['count'], 1)
        self.assertEqual(retry['total_positive'], 2)

    def test_shared_semantics_reuse_checks_source_and_compiled_hashes(self):
        rows = [f'accept\t{HERE / "case-empty.p4"}\t{HERE / "case-oracle.lean"}\n']
        result, first = self.run_proofs(rows)
        self.assertEqual(result.returncode, 0)
        cache = self.output
        self.output, self.report = self.root / 'reused', self.root / 'reused.md'
        result, reused = self.run_proofs(rows, '--semantics-from', str(cache))
        self.assertEqual(result.returncode, 0, json.dumps(reused))
        self.assertEqual(reused['proved'], 1)
        self.assertEqual(reused['semantics_olean_sha256'], first['semantics_olean_sha256'])
        self.assertFalse((self.output / 'Semantics.json').exists())
        # A changed spec cannot silently import a cache for the old relation.
        self.spec.write_text(self.spec.read_text().replace(': OK', ': OK\n  -- if 0 = 1'))
        self.output, self.report = self.root / 'changed', self.root / 'changed.md'
        result, changed = self.run_proofs(rows, '--semantics-from', str(cache))
        self.assertEqual(result.returncode, 1)
        self.assertEqual(changed['status'], 'failed')
        self.assertIn('semantics source', changed['error'])
        self.spec.write_text((HERE / 'case-obligation.watsup').read_text())
        (cache / 'Semantics.olean').write_bytes(b'invalid compiled cache')
        self.output, self.report = self.root / 'corrupt', self.root / 'corrupt.md'
        result, corrupt = self.run_proofs(rows, '--semantics-from', str(cache))
        self.assertEqual(result.returncode, 1)
        self.assertIn('compiled semantics', corrupt['error'])


if __name__ == '__main__':
    unittest.main(argv=[sys.argv[0], *tests])

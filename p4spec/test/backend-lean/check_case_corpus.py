"""Exercise corpus export through the CLI and check the generated Lean contract."""
import argparse
import csv
import gzip
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

parser = argparse.ArgumentParser()
parser.add_argument('--exe', required=True)
args, tests = parser.parse_known_args()
EXE = str(Path(args.exe).resolve())
FIXTURES = Path(__file__).resolve().parent


class CaseCorpus(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.spec = self.root / 'spec.watsup'
        self.spec.write_text((FIXTURES / 'case-obligation.watsup').read_text())
        self.manifest = self.root / 'cases.tsv'
        self.directory = self.root / 'export'
        self.manifest.write_text(
            f'accept\t{FIXTURES / "case-empty.p4"}\t{FIXTURES / "case-oracle.lean"}\n'
            f'reject\t{FIXTURES / "case-semicolon.p4"}\n'
            f'abort-reject\t{FIXTURES / "case-semicolon.p4"}\n')

    def export(self, *flags):
        return subprocess.run([EXE, '--emit-cases', str(self.directory),
                               '--manifest', str(self.manifest), *flags, str(self.spec)],
                              capture_output=True, text=True)

    def rows(self):
        with (self.directory / 'index.tsv').open() as stream:
            return list(csv.DictReader(stream, delimiter='\t'))

    def lean(self, proof):
        semantics = self.directory / 'semantics'
        cases = self.directory / 'cases'
        env = os.environ | {'LEAN_PATH': os.pathsep.join([str(semantics), str(cases)])}
        modules = [semantics / 'SpecTecCore.lean', semantics / 'SpecTecSupport.lean']
        modules += sorted(semantics.glob('SpecTecDecl*.lean'))
        modules += [semantics / 'SpecTecAll.lean']
        for row in self.rows():
            modules += [cases / row['data_module'], cases / row['goal_module']]
        for source in modules:
            result = subprocess.run(['lean', '-o', str(source.with_suffix('.olean')), str(source)],
                                    env=env, cwd=source.parent, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, source.name + '\n' + result.stdout + result.stderr)
        client = self.root / 'Client.lean'
        client.write_text(proof)
        result = subprocess.run(['lean', str(client)], env=env, cwd=client.parent, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_export_preserves_acceptance_uniqueness_and_negative_contracts(self):
        result = self.export()
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = self.rows()
        self.assertEqual([r['case_id'] for r in rows], ['0', '1', '2'])
        self.assertEqual([r['expectation'] for r in rows], ['accept', 'reject', 'abort-reject'])
        self.assertEqual(rows[2]['goal_kind'], 'rejection-conjecture')
        index = (self.directory / 'index.md').read_text()
        self.assertIn('Case0000.lean', index)
        self.assertIn('Case0002.lean', index)
        self.assertIn('conjecture', index)
        self.lean('''import Case0000
import Case0001
import Case0002
namespace SpecTec
open SpecTecExecution
example : case_0 := by
  constructor
  · exact ⟨0, .call (.orElse_success (.bind_success (.guard_true (by rfl)) (.pure _)))⟩
  · intro output ⟨final, h⟩
    obtain ⟨_, known⟩ : ∃ a : Eval Body (.call ⟨p4programIR,
      Call.Program_ok case_0_input⟩) 0 (.success (.of case_0_expected)) 0,
      Functional Body a :=
      ⟨_, .call (.orElse_success (.bind_success (.guard_true (h := by rfl)) (.pure _)))⟩
    simpa only [Outcome.success.injEq, Value.of.injEq, heq_eq_eq, true_and]
      using ((eval_deterministic known h).1).symm
example : case_1 := by
  rintro ⟨output, final, h⟩
  obtain ⟨_, failure⟩ : ∃ a : Eval Body (.call ⟨p4programIR,
    Call.Program_ok case_1_input⟩) 0 .unmatch 0, Functional Body a :=
    ⟨_, .call (.orElse_unmatch (.bind_unmatch (.guard_false (h := by decide))) .unmatch)⟩
  cases (eval_deterministic failure h).1
example (h : case_0) : Program_ok case_0_input case_0_expected := h.1
example (h : case_0) : ∀ output, Program_ok case_0_input output →
    output = case_0_expected := h.2
example (h : case_2) : ¬ ∃ output, Program_ok case_2_input output := h
end SpecTec
''')

    def test_range_preserves_global_ids_across_comments(self):
        self.manifest.write_text('# first\n\n' + self.manifest.read_text())
        result = self.export('--case-range', '1', '2')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual([r['case_id'] for r in self.rows()], ['1', '2'])
        self.assertFalse((self.directory / 'cases' / 'Case0000.lean').exists())
        self.lean('import Case0001\nimport Case0002\n#check SpecTec.case_1\n#check SpecTec.case_2\n')

    def test_fresh_gzip_oracle_keeps_exact_names(self):
        self.spec.write_text('''syntax p4program = _EMPTY | p4program ';'
syntax p4programIR = text
var id : text
builtin dec $fresh_typeId() : text
relation Program_ok: |- p4program : p4programIR hint(input %0)
rule Program_ok/fail: |- _EMPTY : "unreachable"
  -- if id = $fresh_typeId()
  -- if id = "not-fresh"
rule Program_ok/fallback: |- _EMPTY : $fresh_typeId()
  -- otherwise
''')
        oracle = self.root / 'oracle.lean.gz'
        with gzip.open(oracle, 'wt') as stream:
            # The failed first clause already consumed FRESH__0.
            stream.write('"FRESH__1"\n')
        self.manifest.write_text(f'accept\t{FIXTURES / "case-empty.p4"}\t{oracle}\n')
        result = self.export()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean('''import Case0000
namespace SpecTec
example : case_0_expected = "FRESH__1" := rfl
example : Program_ok case_0_input case_0_expected := by
  refine ⟨2, ?_⟩
  apply SpecTecExecution.Eval.call
  apply SpecTecExecution.Eval.orElse_unmatch
  · apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true; rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact .call .freshId
      · apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false; decide
  · apply SpecTecExecution.Eval.orElse_success
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true; rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact .call .freshId
      · exact .pure _
end SpecTec
''')

    def test_imports_preserve_external_type_context(self):
        self.spec.write_text('extern syntax json\nvar j : json\n' +
                             self.spec.read_text() + '''
relation Echo: json ~> json hint(input %0)
rule Echo: j ~> j
''')
        result = self.export('--case-range', '0', '1')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean('''import Case0000
#check @SpecTec.case_0
example : SpecTec.json := .mk
example (x y : SpecTec.json) : x = y := by cases x; cases y; rfl
''')

    def test_existing_destination_is_preserved(self):
        self.directory.mkdir()
        sentinel = self.directory / 'keep.txt'
        sentinel.write_text('user data')
        result = self.export()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(sentinel.read_text(), 'user data')
        self.assertEqual(list(self.directory.iterdir()), [sentinel])

    def test_late_parse_failure_does_not_publish_partial_corpus(self):
        invalid = self.root / 'invalid.p4'
        invalid.write_text('not a P4 program !')
        self.manifest.write_text(self.manifest.read_text() + f'reject\t{invalid}\n')
        result = self.export()
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(self.directory.exists())

    def test_empty_or_corrupt_oracle_is_an_error(self):
        for data in (b'', b'not gzip data'):
            with self.subTest(data=data):
                oracle = self.root / 'bad.lean.gz'
                oracle.write_bytes(data)
                self.manifest.write_text(f'accept\t{FIXTURES / "case-empty.p4"}\t{oracle}\n')
                result = self.export()
                self.assertNotEqual(result.returncode, 0)
                self.assertFalse(self.directory.exists())

    def test_malformed_manifest_reports_line_and_keeps_output_absent(self):
        for row in ('accept\tinput.p4', 'reject\tinput.p4\textra', 'unknown\tinput.p4'):
            with self.subTest(row=row):
                self.manifest.write_text('# heading\n' + row + '\n')
                result = self.export()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn('cases.tsv:2:', result.stderr)
                self.assertFalse(self.directory.exists())

    def verify(self, env=None):
        return subprocess.run([sys.executable, str(FIXTURES / 'verify_case_corpus.py'),
                               '--directory', str(self.directory), '--jobs', '2'],
                              env=env, capture_output=True, text=True)

    def assert_failed_report(self):
        report = json.loads((self.directory / 'checks.json').read_text())
        self.assertFalse(report['all_declarations_checked'])
        self.assertEqual(report['propositions_proved'], 0)
        self.assertIn('All declarations checked: False.',
                      (self.directory / 'checks.md').read_text())

    def test_verifier_does_not_import_deleted_source_from_stale_cache(self):
        self.assertEqual(self.export().returncode, 0)
        self.lean('import Case0000\n#check SpecTec.case_0\n')
        self.assertEqual(self.verify().returncode, 0)
        semantics = self.directory / 'semantics'
        self.assertTrue((semantics / 'SpecTecDecl0000.olean').exists())
        (semantics / 'SpecTecDecl0000.lean').unlink()
        checked = self.verify()
        self.assertNotEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assert_failed_report()

    def test_verifier_invalidates_success_report_when_case_source_is_missing(self):
        self.assertEqual(self.export().returncode, 0)
        self.assertEqual(self.verify().returncode, 0)
        (self.directory / 'cases' / 'Case0000.lean').unlink()
        checked = self.verify()
        self.assertNotEqual(checked.returncode, 0)
        self.assert_failed_report()

    def test_verifier_records_failure_when_lean_cannot_launch(self):
        self.assertEqual(self.export().returncode, 0)
        self.assertEqual(self.verify().returncode, 0)
        checked = self.verify(env=os.environ | {'PATH': ''})
        self.assertNotEqual(checked.returncode, 0)
        self.assert_failed_report()

    def test_verifier_checks_declarations_without_claiming_proofs(self):
        result = self.export()
        self.assertEqual(result.returncode, 0, result.stderr)
        checked = self.verify()
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        report = json.loads((self.directory / 'checks.json').read_text())
        self.assertTrue(report['all_declarations_checked'])
        self.assertEqual(report['propositions_proved'], 0)
        self.assertEqual([r['case_id'] for r in report['cases']], [0, 1, 2])
        self.assertEqual([r['status'] for r in report['cases']], ['checked'] * 3)
        self.assertEqual(report['cases'][2]['goal_kind'], 'rejection-conjecture')

    def test_verifier_checks_large_oracle_declaration(self):
        self.spec.write_text('''syntax p4program = _EMPTY | p4program ';'
syntax p4programIR = nat*
var n : nat
var m : nat
dec $zeros(nat) : nat*
def $zeros(0) = eps
def $zeros(n) = 0 :: $zeros(m)
  -- if $(n > 0)
  -- if m = $(n - 1)
relation Program_ok: |- p4program : p4programIR hint(input %0)
rule Program_ok: |- _EMPTY : $zeros(20000)
''')
        oracle = self.root / 'large.lean'
        oracle.write_text('[' + ','.join(['0'] * 20000) + ']\n')
        self.manifest.write_text(f'accept\t{FIXTURES / "case-empty.p4"}\t{oracle}\n')
        exported = self.export()
        self.assertEqual(exported.returncode, 0, exported.stderr)
        checked = self.verify()
        report = json.loads((self.directory / 'checks.json').read_text())
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr + str(report))
        self.assertTrue(report['all_declarations_checked'])
        self.assertEqual(report['propositions_proved'], 0)

    def test_verifier_reports_ill_typed_oracle_as_failure(self):
        oracle = self.root / 'wrong.lean'
        oracle.write_text('42\n')
        self.manifest.write_text(f'accept\t{FIXTURES / "case-empty.p4"}\t{oracle}\n')
        self.assertEqual(self.export().returncode, 0)
        checked = self.verify()
        self.assertNotEqual(checked.returncode, 0)
        report = json.loads((self.directory / 'checks.json').read_text())
        self.assertFalse(report['all_declarations_checked'])
        self.assertEqual(report['cases'][0]['status'], 'data-error')
        self.assertFalse(report['cases'][0]['goal_checked'])

    def test_verifier_rejects_index_paths_outside_case_directory(self):
        self.assertEqual(self.export().returncode, 0)
        index = self.directory / 'index.tsv'
        index.write_text(index.read_text().replace('Case0000Data.lean', '../outside.lean'))
        checked = self.verify()
        self.assertNotEqual(checked.returncode, 0)
        self.assertIn('data_module', checked.stderr)


if __name__ == '__main__':
    unittest.main(argv=['check_case_corpus', *tests], verbosity=2)

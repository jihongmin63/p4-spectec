"""Check the default ordered API, compatibility mode and independent pruning."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

parser = argparse.ArgumentParser()
parser.add_argument('--exe', required=True)
parser.add_argument('--oracle-exe')
args = parser.parse_args()
EXE = str(Path(args.exe).resolve())
ORACLE_EXE = str(Path(args.oracle_exe).resolve()) if args.oracle_exe else None
FIXTURES = Path(__file__).resolve().parent

class OrderedRelations(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)

    def translate(self, text, *flags):
        source = self.root / 'input.watsup'
        source.write_text(text)
        return subprocess.run([EXE, *flags, str(source)], capture_output=True, text=True)

    def lean(self, text):
        source = self.root / 'Proof.lean'
        source.write_text(text)
        result = subprocess.run(['lean', str(source)], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def modules(self, text, *flags):
        directory = self.root / 'modules'
        result = self.translate(text, '--emit-modules', str(directory), '--module-split-bytes', '1000', *flags)
        self.assertEqual(result.returncode, 0, result.stderr)
        files = ['SpecTecCore.lean', 'SpecTecSupport.lean']
        files += [p.name for p in sorted(directory.glob('SpecTecDecl*.lean'))]
        files += ['SpecTecAll.lean', 'SpecTecProofs.lean', 'SpecTecCases.lean']
        env = os.environ | {'LEAN_PATH': str(directory)}
        for name in files:
            source = directory / name
            result = subprocess.run(['lean', '-o', str(source.with_suffix('.olean')), str(source)],
                                    env=env, cwd=directory, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, name + '\n' + result.stdout + result.stderr)
        self.assertEqual((directory / 'SpecTecCore.lean').read_text().count('inductive Eval'), 1)
        return directory

    def test_choice_default_and_operational_proofs(self):
        result = self.translate((FIXTURES / 'ordered-choice.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.count('inductive Eval'), 1)
        self.assertNotIn('runFuel', result.stdout)
        self.assertNotIn('inductive Choose', result.stdout)
        self.assertNotIn('noncomputable', result.stdout)
        self.lean(result.stdout + (FIXTURES / 'ordered-choice-proof.lean').read_text())

    def test_noncomputable_is_limited_to_runtime_constructor_dependencies(self):
        source = 'var n : nat\nvar m : nat\n' + ''.join(
            f'extern relation E{i:03d}: nat ~> nat hint(input %0)\n'
            for i in range(250)) + '''
extern dec $empty : nat
dec $use_empty() : nat
def $use_empty() = $empty()
relation Lower: nat ~> nat hint(input %0)
rule Lower: n ~> m
  -- E243: n ~> m
relation Upper: nat ~> nat hint(input %0)
rule Upper/first: n ~> m
  -- E244: n ~> m
rule Upper/default: n ~> 0
  -- otherwise
'''
        result = self.translate(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        annotations = [line.split(' :=')[0] for line in result.stdout.splitlines()
                       if line.startswith('noncomputable def ')]
        self.assertEqual(len(annotations), 3, annotations)
        self.assertTrue(annotations[0].startswith('noncomputable def «Upper:clause:0» '))
        self.assertTrue(annotations[1].startswith('noncomputable def Upper_clauses '))
        self.assertTrue(annotations[2].startswith('noncomputable def Body '))
        self.lean(result.stdout + '''
namespace SpecTec
example : Upper 7 9 :=
  ⟨0, .call (.orElse_success (.bind_success
    (.call (.choose 9 (.allowed 7 9))) (.pure 9)))⟩
end SpecTec
''')

    def test_noncomputable_handles_large_data_constructors(self):
        source = 'syntax value = ' + ' | '.join(f'C{i} nat' for i in range(245)) + ''' | EMPTY
var n : nat
dec $match_high(value) : nat
def $match_high(C244 n) = n
dec $get_low() : value
def $get_low() = C243 0
dec $get_high() : value
def $get_high() = C244 0
dec $get_empty() : value
def $get_empty() = EMPTY
'''
        result = self.translate(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        annotations = [line for line in result.stdout.splitlines()
                       if line.startswith('noncomputable def ')]
        self.assertEqual(len(annotations), 3, annotations)
        self.assertTrue(annotations[0].startswith('noncomputable def «$get_high:clause:0» '))
        self.assertTrue(annotations[1].startswith('noncomputable def «$get_high_clauses» '))
        self.assertTrue(annotations[2].startswith('noncomputable def Body '))
        self.lean(result.stdout + '''
namespace SpecTec
example : «$get_high» (.C244 0) := ⟨0, .call (.orElse_success (.pure _))⟩
end SpecTec
''')

    def test_fresh_shared_supply_and_public_api(self):
        result = self.translate((FIXTURES / 'ordered-fresh.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + (FIXTURES / 'ordered-fresh-proof.lean').read_text())

    def test_fresh_modules_share_supply(self):
        directory = self.modules((FIXTURES / 'ordered-fresh.watsup').read_text())
        proof = directory / 'FreshClient.lean'
        proof.write_text('import SpecTecAll\n' + (FIXTURES / 'ordered-fresh-proof.lean').read_text())
        result = subprocess.run(['lean', str(proof)], env=os.environ | {'LEAN_PATH': str(directory)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_fresh_rejects_invalid_signature_and_declarative_mode(self):
        for declaration in ['builtin dec $fresh_typeId() : nat',
                            'builtin dec $fresh_typeId(nat) : text',
                            'builtin dec $fresh_typeId<X>() : text']:
            with self.subTest(declaration=declaration):
                result = self.translate(declaration)
                self.assertEqual(result.returncode, 1, result.stderr)
                self.assertIn('fresh_typeId', result.stderr)
                self.assertEqual(result.stdout, '')
        result = self.translate('builtin dec $fresh_typeId() : text',
                                '--relation-semantics', 'declarative')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn('fresh_typeId', result.stderr)

    def test_ordinary_function_named_fresh_is_not_effectful_builtin(self):
        result = self.translate('dec $fresh_typeId() : text\ndef $fresh_typeId() = "ordinary"\n')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + '''\nnamespace SpecTec
example : «$fresh_typeId» "ordinary" := ⟨0, .call (.orElse_success (.pure _))⟩
end SpecTec\n''')

    def test_fresh_builtin_callback_remains_explicitly_unsupported(self):
        result = self.translate('''builtin dec $fresh_typeId() : text
dec $use(def $f() : text) : text
def $use(def $f) = $f()
dec $bad() : text
def $bad() = $use(def $fresh_typeId)
''')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn('function argument $fresh_typeId', result.stderr)

    def test_existing_expression_and_type_fixtures(self):
        for name in ['tuple', 'update', 'slice', 'set', 'table', 'notation',
                     'decidable-eq', 'decidable-eq-shadow', 'print', 'extern-model', 'extern-syntax-only']:
            with self.subTest(name=name):
                result = self.translate((FIXTURES / (name + '.watsup')).read_text())
                self.assertEqual(result.returncode, 0, result.stderr)
                self.lean(result.stdout)

    def test_module_order_and_shared_runtime(self):
        directory = self.modules((FIXTURES / 'ordered-choice.watsup').read_text())
        proof = directory / 'Client.lean'
        proof.write_text('import SpecTecAll\n' + (FIXTURES / 'ordered-choice-proof.lean').read_text())
        result = subprocess.run(['lean', str(proof)], env=os.environ | {'LEAN_PATH': str(directory)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def check_singleton_externs(self, *flags):
        result = self.translate((FIXTURES / 'extern-singletons.watsup').read_text(), *flags)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn('SpecTecExternTypes', result.stdout)
        self.lean(result.stdout + (FIXTURES / 'extern-singletons-proof.lean').read_text())
        invalid = self.root / 'DistinctTypes.lean'
        invalid.write_text(result.stdout + '\nexample : SpecTec.objectState := SpecTec.archState.mk\n')
        checked = subprocess.run(['lean', str(invalid)], capture_output=True, text=True)
        self.assertNotEqual(checked.returncode, 0)
        self.assertIn('type mismatch', (checked.stdout + checked.stderr).lower())

    def check_singleton_modules(self, *flags):
        directory = self.modules((FIXTURES / 'extern-singletons.watsup').read_text(), *flags)
        proof = directory / 'SingletonClient.lean'
        proof.write_text('import SpecTecAll\n' + (FIXTURES / 'extern-singletons-proof.lean').read_text())
        checked = subprocess.run(['lean', str(proof)], env=os.environ | {'LEAN_PATH': str(directory)},
                                 capture_output=True, text=True)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

    def test_singleton_external_types(self):
        self.check_singleton_externs()

    def test_modules_singleton_external_types(self):
        self.check_singleton_modules()

    def test_extern_admits_every_output_without_execution_model(self):
        result = self.translate((FIXTURES / 'ordered-extern.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue('inductive «$init_archState»' in result.stdout,
                        'extern must expose a direct inductive relation')
        self.assertTrue('SpecTecExternExecution' not in result.stdout,
                        'extern must not require an execution model')
        self.assertTrue('validArchState' not in result.stdout and 'validObjectState' not in result.stdout,
                        'ordered extern types must not require unused validity fields')
        self.lean(result.stdout + (FIXTURES / 'ordered-extern-proof.lean').read_text())

    def test_modules_preserve_unconditional_extern(self):
        directory = self.modules((FIXTURES / 'ordered-extern.watsup').read_text())
        proof = directory / 'Client.lean'
        proof.write_text('import SpecTecAll\n' + (FIXTURES / 'ordered-extern-proof.lean').read_text())
        result = subprocess.run(['lean', str(proof)], env=os.environ | {'LEAN_PATH': str(directory)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_extern_multiple_zero_and_polymorphic_outputs(self):
        source = '''extern relation Any: nat ~> nat ':' nat ~> bool hint(input %0 %2)
extern relation AnyPredicate: |- nat hint(input %0)
extern dec $arbitrary<X>(X) : X
var n : nat
var m : nat
var b : bool
relation ViaAny: nat ~> nat ':' bool hint(input %0)
rule ViaAny/call: n ~> m ':' b -- Any: n ~> m ':' n ~> b
relation ViaPredicate: |- nat hint(input %0)
rule ViaPredicate/call: |- n -- AnyPredicate: |- n
dec $via_arbitrary(nat) : nat
def $via_arbitrary(n) = $arbitrary<nat>(n)
'''
        result = self.translate(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + '''
namespace SpecTec
example : Any 1 99 2 true := .allowed 1 99 2 true
example : AnyPredicate 10 := .allowed 10
example : «$arbitrary» (7 : Nat) 8 := .allowed 7 8
example : ViaAny 1 99 true := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.choose (99, true) (.allowed 1 99 1 true))) (.pure (99, true))))
example : ViaPredicate 10 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.choose () (.allowed 10))) (.pure ())))
example : «$via_arbitrary» 7 8 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.choose 8 (.allowed 7 8))) (.pure 8)))
end SpecTec
''')

    def test_pruned_callee_cannot_open_otherwise(self):
        text = '''var n : nat
builtin dec $fresh_typeId() : nat
dec $bad(nat) : nat
def $bad(n) = $fresh_typeId()
def $bad(n) = 99 -- otherwise
dec $caller(nat) : nat
def $caller(n) = $bad(n)
def $caller(n) = 100 -- otherwise
relation Copy: nat ~> nat hint(input %0)
rule Copy/copy: n ~> n
'''
        result = self.translate(text, '--keep-going')
        self.assertEqual(result.returncode, 1)
        self.assertIn('fresh_typeId', result.stderr)
        self.assertNotIn('def «$bad»', result.stdout)
        self.assertNotIn('def «$caller»', result.stdout)
        self.lean(result.stdout + '\nnamespace SpecTec\nexample : Copy 7 7 := ⟨0, .call (.orElse_success (.pure 7))⟩\nend SpecTec\n')

    def test_ordered_case_propositions_and_failure_proof(self):
        flags = ('--case', str(FIXTURES / 'case-empty.p4'), str(FIXTURES / 'case-oracle.lean'),
                 '--reject-case', str(FIXTURES / 'case-semicolon.p4'))
        directory = self.modules((FIXTURES / 'case-obligation.watsup').read_text(), *flags)
        proof = directory / 'Client.lean'
        proof.write_text('''import SpecTecCases
namespace SpecTec
open SpecTecExecution
example : case_0 := by
  have success : Program_ok case_0_input case_0_expected :=
    ⟨0, .call (.orElse_success (.bind_success (.guard_true rfl) (.pure _)))⟩
  refine ⟨success, ?_⟩
  rintro output ⟨final, h⟩
  obtain ⟨_, known⟩ : ∃ a : Eval Body
      (.call ⟨p4programIR, Call.Program_ok case_0_input⟩) 0
      (.success (.of case_0_expected)) 0, Functional Body a :=
    ⟨_, .call (.orElse_success (.bind_success (.guard_true (h := rfl)) (.pure _)))⟩
  simpa [Value.of.injEq] using ((eval_deterministic known h).1).symm
example : case_1 := by
  obtain ⟨_, failure⟩ : ∃ a : Eval Body
      (.call ⟨p4programIR, Call.Program_ok case_1_input⟩) 0 .unmatch 0,
      Functional Body a :=
    ⟨_, .call (.orElse_unmatch (.bind_unmatch (.guard_false (h := by decide))) .unmatch)⟩
  rintro ⟨output, final, h⟩
  cases (eval_deterministic failure h).1
end SpecTec
''')
        result = subprocess.run(['lean', str(proof)], env=os.environ | {'LEAN_PATH': str(directory)},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_case_propositions_use_unconditional_extern(self):
        source = ((FIXTURES / 'extern-model.watsup').read_text() +
                  '\nvar nm : nameIR\nvar result : value\n' +
                  (FIXTURES / 'case-obligation.watsup').read_text().rstrip() +
                  '\n  -- ExternFunctionCall_eval_lctk: TC |- (NAME "test") `(eps`) ~> result\n')
        flags = ('--case', str(FIXTURES / 'case-empty.p4'), str(FIXTURES / 'case-oracle.lean'))
        result = self.translate(source, *flags)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue('SpecTecP4ExternModel' not in result.stdout,
                        'ordered extern must not require a P4 validity model')
        self.assertTrue('SpecTecExternExecution' not in result.stdout,
                        'ordered extern must not require an execution model')
        self.lean(result.stdout)
        self.modules(source, *flags)

    def test_pruned_dependency_removes_whole_definition(self):
        text = '''var n : nat
builtin dec $fresh_typeId() : nat
dec $bad(nat) : nat
def $bad(n) = $fresh_typeId()
dec $caller(nat*) : nat
def $caller(n*) = $bad(0)
  -- (if $(n > 0))*
relation Copy: nat ~> nat hint(input %0)
rule Copy/copy: n ~> n
'''
        result = self.translate(text, '--keep-going')
        self.assertEqual(result.returncode, 1)
        self.assertIn('depends on untranslated declaration $fresh_typeId', result.stderr)
        self.assertIn('transitive dependency via removed declaration $bad', result.stderr)
        self.assertNotIn('execution call', result.stderr)
        self.assertNotIn('$caller', result.stdout, 'iteration helpers must not outlive their caller')
        self.lean(result.stdout + '\nnamespace SpecTec\nexample : Copy 7 7 := ⟨0, .call (.orElse_success (.pure 7))⟩\nend SpecTec\n')

    def test_downcast_to_variant_with_compound_type_argument(self):
        result = self.translate('''var n : nat
var ns : nat*
syntax wrap<X> = _CONT X
syntax stop = STOP
syntax listResult = wrap<nat*> | stop
relation Produce: nat ~> listResult
  hint(input %0)
rule Produce/zero: 0 ~> _CONT ([1, 2])
rule Produce/other: n ~> STOP
  -- otherwise
relation Consume: nat ~> nat*
  hint(input %0)
rule Consume/cont: n ~> ns
  -- Produce: n ~> _CONT ns
rule Consume/stop: n ~> eps
  -- otherwise
''')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + '''
namespace SpecTec
open SpecTecExecution
syntax "prove_downcast" : tactic
macro_rules
  | `(tactic| prove_downcast) => `(tactic|
      first
        | refine ⟨0, ?_⟩; prove_downcast
        | exact Eval.pure _
        | exact Eval.unmatch
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_downcast
        | apply Eval.orElse_success; prove_downcast
        | apply Eval.orElse_unmatch; prove_downcast; prove_downcast
        | apply Eval.bind_success; prove_downcast; prove_downcast
        | apply Eval.bind_unmatch; prove_downcast)
example : Consume 0 [1, 2] := by prove_downcast
example : Consume 1 [] := by prove_downcast
end SpecTec
''')

    def test_structural_downcasts(self):
        result = self.translate((FIXTURES / 'ordered-downcast.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + (FIXTURES / 'ordered-downcast-proof.lean').read_text())

    def test_empty_supported_call_set(self):
        result = self.translate('builtin dec $fresh_typeId() : nat\n', '--keep-going')
        self.assertEqual(result.returncode, 1)
        self.lean(result.stdout)

    def test_recursive_negative_calls_remain_rejected(self):
        result = self.translate('''relation NegativeLoop: |- nat hint(input %0)
rule NegativeLoop/negative: |- 0
  -- NegativeLoop:/ |- 0
''')
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn('IfNotHoldPr', result.stderr)
        self.assertEqual(result.stdout, '')

    def test_operation_errors_and_utf8_limit_cannot_open_fallback(self):
        result = self.translate((FIXTURES / 'ordered-errors.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + (FIXTURES / 'ordered-errors-proof.lean').read_text())

    def test_table_without_applicable_row_aborts(self):
        result = self.translate((FIXTURES / 'ordered-table.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('.abort "table $is_red did not return a value"', result.stdout)
        self.lean(result.stdout + (FIXTURES / 'ordered-table-proof.lean').read_text())

    def test_declarative_compatibility_and_otherwise_diagnostic(self):
        result = self.translate((FIXTURES / 'ordered-choice.watsup').read_text(), '--relation-semantics', 'declarative')
        self.assertEqual(result.returncode, 1)
        self.assertIn('otherwise of relation Choose', result.stderr)
        result = self.translate('var n : nat\nrelation Copy: nat ~> nat hint(input %0)\nrule Copy/copy: n ~> n\n',
                                '--relation-semantics', 'declarative')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('inductive Copy', result.stdout)
        self.lean(result.stdout + '\nnamespace SpecTec\nexample : Copy 7 7 := Copy.copy 7\nend SpecTec\n')

    def test_higher_order_result_type_is_enforced(self):
        result = self.translate((FIXTURES / 'ordered-functions.watsup').read_text())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.lean(result.stdout + (FIXTURES / 'ordered-functions-proof.lean').read_text())
        source = self.root / 'Bad.lean'
        source.write_text(result.stdout + '\nnamespace SpecTec\ndef bad := Call.«$apply» (fun n => Call.EqualPair n n) 0\nend SpecTec\n')
        result = subprocess.run(['lean', str(source)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('type mismatch', result.stdout.lower())

if __name__ == '__main__':
    unittest.main(argv=['check_ordered_relations'], verbosity=2)

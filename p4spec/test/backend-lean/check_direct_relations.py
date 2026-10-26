"""Exercise the CLI's supported subset and the generated inductive API."""

import argparse
import os
import pathlib
import subprocess
import tempfile
import unittest


parser = argparse.ArgumentParser()
parser.add_argument("--exe", required=True)
parser.add_argument("tests", nargs="*")
args = parser.parse_args()
EXE = str(pathlib.Path(args.exe).resolve())

PURE = """
var n : nat
relation Even: |- nat
  hint(input %0)
rule Even/zero:
  |- 0
rule Even/step:
  |- $(n + 2)
  -- Even: |- n

relation Left: |- nat
  hint(input %0)
relation Right: |- nat
  hint(input %0)
rule Left/zero:
  |- 0
rule Left/next:
  |- $(n + 1)
  -- Right: |- n
rule Right/next:
  |- $(n + 1)
  -- Left: |- n

relation Zero: |- nat
  hint(input %0)
rule Zero/zero:
  |- 0
relation Nonzero: |- nat
  hint(input %0)
rule Nonzero/negative:
  |- n
  -- Zero:/ |- n

relation Copy: nat ~> nat
  hint(input %0)
rule Copy/copy:
  n ~> n
dec $identity(nat) : nat
def $identity(n) = n
"""

PROOF = """
namespace SpecTec
example : Copy 7 7 := Copy.copy 7
example : ¬ Copy 7 8 := by intro h; cases h
example (n : Nat) : «$identity» n n := by constructor
example : Even 4 := Even.step 2 (Even.step 0 Even.zero)
example (n : Nat) (h : Even n) : n % 2 = 0 := by
  induction h with
  | zero => rfl
  | step n _ ih => simpa [Nat.add_mod] using ih
example : Left 2 := Left.next 1 (Right.next 0 Left.zero)
example : Nonzero 1 := Nonzero.negative 1 (by intro h; cases h)
end SpecTec
"""


class DirectRelations(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)

    def translate(self, source, *flags):
        path = self.root / "input.watsup"
        path.write_text(source)
        return subprocess.run(
            [EXE, "--relation-semantics", "declarative", *flags, str(path)], text=True, capture_output=True, check=False
        )

    def check_lean(self, source, proof):
        path = self.root / "output.lean"
        path.write_text(source + "\n" + proof)
        result = subprocess.run(["lean", str(path)], text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def check_modules(self, directory, proof, entry="SpecTecAll"):
        env = dict(os.environ)
        env["LEAN_PATH"] = str(directory) + os.pathsep + env.get("LEAN_PATH", "")
        pending = {path.stem: path for path in directory.glob("*.lean")}
        compiled = set()
        while pending:
            ready = [
                name for name, path in pending.items()
                if all(line.split()[1] not in pending
                       for line in path.read_text().splitlines()
                       if line.startswith("import "))
            ]
            self.assertTrue(ready, "generated modules contain circular imports")
            for name in ready:
                path = pending.pop(name)
                result = subprocess.run(
                    ["lean", "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=directory, env=env, text=True, capture_output=True
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                compiled.add(name)
        self.assertIn("SpecTecAll", compiled)
        path = directory / "Verify.lean"
        path.write_text("import " + entry + "\n" + proof)
        result = subprocess.run(["lean", str(path)], cwd=directory, env=env,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_modules_preserve_signatures_and_mutual_induction(self):
        directory = self.root / "generated"
        result = self.translate(PURE, "--emit-modules", str(directory),
                                "--module-split-bytes", "512")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "")
        self.check_modules(directory, PROOF)

    def test_modules_preserve_extern_context_across_imports(self):
        fixtures = pathlib.Path(__file__).parent
        directory = self.root / "generated"
        result = self.translate((fixtures / "extern-model.watsup").read_text(),
                                "--emit-modules", str(directory),
                                "--module-split-bytes", "512")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.check_modules(directory, (fixtures / "extern-direct-proof.lean").read_text())

    def test_module_output_does_not_overwrite_existing_files(self):
        directory = self.root / "generated"
        directory.mkdir()
        sentinel = directory / "existing.txt"
        sentinel.write_text("user data")
        result = self.translate(PURE, "--emit-modules", str(directory))
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertEqual(sentinel.read_text(), "user data")
        self.assertEqual(list(directory.iterdir()), [sentinel])

    def test_modules_preserve_case_obligations(self):
        fixtures = pathlib.Path(__file__).parent.resolve()
        directory = self.root / "generated"
        result = self.translate((fixtures / "case-obligation.watsup").read_text(),
                                "--emit-modules", str(directory),
                                "--case", str(fixtures / "case-empty.p4"),
                                str(fixtures / "case-oracle.lean"),
                                "--reject-case", str(fixtures / "case-semicolon.p4"))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.check_modules(directory, """
namespace SpecTec
example : case_0 := by
  constructor
  · constructor
  · intro output h; cases h; rfl
example : case_1 := by
  intro h; obtain ⟨output, h⟩ := h; cases h
end SpecTec
""", entry="SpecTecCases")

    def test_cases_preserve_external_type_context(self):
        fixtures = pathlib.Path(__file__).parent.resolve()
        source = "extern syntax json\nvar j : json\n" + (
            fixtures / "case-obligation.watsup").read_text().rstrip() + "\n  -- if j = j\n"
        result = self.translate(source, "--case", str(fixtures / "case-empty.p4"),
                                str(fixtures / "case-oracle.lean"))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.check_lean(result.stdout, "")

    def test_cases_preserve_p4_extern_model_context(self):
        fixtures = pathlib.Path(__file__).parent.resolve()
        source = (fixtures / "extern-model.watsup").read_text() + (
            "\nvar nm : nameIR\nvar result : value\n") + (
            fixtures / "case-obligation.watsup").read_text().rstrip() + """
  -- ExternFunctionCall_eval_lctk: TC |- nm `(eps`) ~> result
"""
        for modular in (False, True):
            with self.subTest(modular=modular):
                directory = self.root / "generated"
                flags = ("--emit-modules", str(directory)) if modular else ()
                result = self.translate(source, *flags, "--case",
                                        str(fixtures / "case-empty.p4"),
                                        str(fixtures / "case-oracle.lean"))
                self.assertEqual(result.returncode, 0, result.stderr)
                if modular:
                    self.check_modules(directory, "", entry="SpecTecCases")
                else:
                    self.check_lean(result.stdout, "")

    def test_incomplete_p4_extern_environment_is_rejected_and_pruned(self):
        source = PURE + """
syntax typingContext = TC
syntax nameIR = NAME text
syntax value = NUM nat
extern relation ExternFunctionCall_eval_lctk:
  typingContext |- nameIR `( nameIR* `) ~> value
  hint(input %0 %1 %2)
"""
        strict = self.translate(source)
        self.assertEqual(strict.returncode, 1, strict.stderr)
        self.assertIn("extern model", strict.stderr)
        self.assertIn("input.watsup:", strict.stderr)
        self.assertEqual(strict.stdout, "")
        partial = self.translate(source, "--keep-going")
        self.assertEqual(partial.returncode, 1, partial.stderr)
        self.assertIn("ExternFunctionCall_eval_lctk", partial.stderr)
        self.assertNotIn("SpecTecP4ExternModel", partial.stdout)
        self.check_lean(partial.stdout, PROOF)

    def test_ordinary_relation_name_does_not_inject_p4_extern_model(self):
        result = self.translate("""
relation ExternFunctionCall_eval_lctk: |- nat
  hint(input %0)
rule ExternFunctionCall_eval_lctk/zero:
  |- 0
""")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertNotIn("SpecTecP4ExternModel", result.stdout)
        self.check_lean(result.stdout, """
example : SpecTec.ExternFunctionCall_eval_lctk 0 :=
  SpecTec.ExternFunctionCall_eval_lctk.zero
""")

    def test_invalid_p4_extern_model_shapes_and_signatures_are_rejected(self):
        fixtures = pathlib.Path(__file__).parent
        source = (fixtures / "extern-model.watsup").read_text()
        variants = [
            source.replace("extern syntax archState", "syntax archState = nat"),
            source.replace("RETURN value? | EXIT | REJECT", "RETURN value? | REJECT"),
            source.replace("typingContext |- nameIR `( nameIR* `)",
                           "typingContext |- nameIR `( value* `)"),
        ]
        for index, variant in enumerate(variants):
            with self.subTest(index=index):
                strict = self.translate(variant)
                self.assertEqual(strict.returncode, 1, strict.stderr)
                self.assertIn("input.watsup:", strict.stderr)
                self.assertEqual(strict.stdout, "")
                partial = self.translate(variant, "--keep-going")
                self.assertEqual(partial.returncode, 1, partial.stderr)
                self.check_lean(partial.stdout, "")

    def test_keep_going_modules_contain_only_supported_relations(self):
        directory = self.root / "generated"
        result = self.translate(PURE + """
dec $fallback(nat) : nat
def $fallback(n) = n
  -- otherwise
""", "--keep-going", "--emit-modules", str(directory))
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("otherwise", result.stderr)
        self.check_modules(directory, PROOF)

    def test_original_signatures_and_inductive_elimination(self):
        result = self.translate(PURE)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.check_lean(result.stdout, PROOF)

    def test_otherwise_function_is_rejected_at_source(self):
        result = self.translate("""
var n : nat
dec $fallback(nat) : nat
def $fallback(0) = 1
def $fallback(n) = n
  -- otherwise
""")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("otherwise", result.stderr)
        self.assertIn("input.watsup:", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_otherwise_relation_is_rejected_at_source(self):
        result = self.translate("""
var n : nat
relation Choose: |- nat
  hint(input %0)
rule Choose/zero:
  |- 0
rule Choose/fallback:
  |- n
  -- otherwise
""")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("otherwise", result.stderr)
        self.assertIn("input.watsup:", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_fresh_allocation_is_explicitly_unsupported(self):
        result = self.translate("""
syntax typeId = text
builtin dec $fresh_typeId() : typeId
dec $allocate() : typeId
def $allocate() = $fresh_typeId()
""")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("fresh_typeId", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_keep_going_prunes_unsupported_definitions_and_callers(self):
        result = self.translate(PURE + """
syntax typeId = text
builtin dec $fresh_typeId() : typeId
dec $allocate() : typeId
def $allocate() = $fresh_typeId()
dec $fallback(nat) : nat
def $fallback(n) = n
  -- otherwise
dec $dependent(nat) : nat
def $dependent(n) = $fallback(n)
""", "--keep-going")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("otherwise", result.stderr)
        self.assertIn("fresh_typeId", result.stderr)
        self.assertIn("$dependent", result.stderr)
        self.check_lean(result.stdout, PROOF)

    def test_recursive_negative_premises_are_rejected(self):
        result = self.translate("""
relation NegativeLoop: |- nat
  hint(input %0)
rule NegativeLoop/negative:
  |- 0
  -- NegativeLoop:/ |- 0
""")
        self.assertEqual(result.returncode, 1, result.stderr)
        self.assertIn("IfNotHoldPr", result.stderr)
        self.assertEqual(result.stdout, "")


unittest.main(argv=["check_direct_relations", *args.tests], verbosity=2)

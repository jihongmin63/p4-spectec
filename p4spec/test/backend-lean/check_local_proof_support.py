#!/usr/bin/env python3
"""Check SCC-local proof tactics and typed evaluator certificates."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def run(command, *, cwd=None, env=None, succeeds=True):
    result = subprocess.run(
        command, cwd=cwd, env=env, capture_output=True, text=True, timeout=120
    )
    output = result.stdout + result.stderr
    if succeeds:
        assert result.returncode == 0, output
        assert "sorryAx" not in output, output
    else:
        assert result.returncode != 0, "invalid certificate was accepted\n" + output
        lowered = output.lower()
        assert "unknown identifier" not in lowered, (
            "negative certificate test referenced a missing declaration\n" + output
        )
        assert "unknownidentifier" not in lowered, (
            "negative certificate test referenced a missing declaration\n" + output
        )
    return output


def translate(exe: Path, source: Path) -> str:
    return run([str(exe.resolve()), str(source)])


def check_lean(root: Path, env, name: str, generated: str, proof: str,
               *, succeeds=True):
    target = root / f"{name}.lean"
    target.write_text("import SpecTecProof\n" + generated + "\n" + proof)
    return run(["lean", "-j", "2", str(target)], env=env, succeeds=succeeds)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--support", type=Path, required=True)
    parser.add_argument("--relation", type=Path, required=True)
    parser.add_argument("--local-proof", type=Path, required=True)
    parser.add_argument("--ordered", type=Path, required=True)
    parser.add_argument("--search", type=Path, required=True)
    args = parser.parse_args()

    relation = translate(args.exe, args.relation)
    ordered = translate(args.exe, args.ordered)
    search = translate(args.exe, args.search)
    assert "namespace «Decl_ok:Semantics»" in relation
    assert "inductive Atom" not in relation.split("namespace SpecTec\n", 1)[1].split(
        "namespace «", 1
    )[0]
    for theorem in (
        "Evaluation.abort_sound", "Evaluation.unsupported_sound",
        "Evaluation.timeout_fuel", "Evaluation.undetermined_sound"
    ):
        assert f"theorem {theorem}" in ordered

    certificate_proof = r'''
namespace SpecTec
open SpecTecProof

private instance certificateBoundary :
    SpecTecEval.Boundary value String String where
  aborts := fun _ error => error = "fatal"
  unsupported := fun _ feature => feature = "missing"

theorem gate_success_certificate
    (proof : Gate.eval 1 .ZERO (.success ())) : Gate .ZERO := by
  spec_check_certificate proof using
    (SpecTecEval.Evaluator.success_sound (evaluator := Gate.evaluator))

theorem gate_abort_certificate
    (proof : Gate.eval 1 .ZERO (.abort "fatal")) :
    SpecTecEval.Boundary.aborts (Input := Gate.EvalInput)
      (Error := String) (Feature := String) .ZERO "fatal" := by
  spec_check_certificate proof using SpecTecEval.Evaluation.abort_sound

theorem gate_unsupported_certificate
    (proof : Gate.eval 1 .ZERO (.unsupported "missing")) :
    SpecTecEval.Boundary.unsupported (Input := Gate.EvalInput)
      (Error := String) (Feature := String) .ZERO "missing" := by
  spec_check_certificate proof using SpecTecEval.Evaluation.unsupported_sound

theorem gate_timeout_certificate {fuel : Nat}
    (proof : Gate.eval fuel .ZERO (.timeout)) : fuel = 0 := by
  spec_check_certificate proof using SpecTecEval.Evaluation.timeout_fuel

theorem negative_undetermined_certificate {fuel : Nat}
    (proof : NegativeLoop.eval fuel .ZERO (.undetermined)) :
    NegativeLoop.evalUndetermined .ZERO := by
  spec_check_certificate proof using SpecTecEval.Evaluation.undetermined_sound

#print axioms gate_success_certificate
#print axioms gate_abort_certificate
#print axioms gate_unsupported_certificate
#print axioms gate_timeout_certificate
#print axioms negative_undetermined_certificate
end SpecTec
'''

    ordered += """
namespace SpecTec
private abbrev «$ordered:regular:eval:rule:0:plan» :=
  («$ordered:regular».evalRules[0]'(by decide))
private abbrev «$ordered:regular:eval:rule:1:plan» :=
  («$ordered:regular».evalRules[1]'(by decide))
end SpecTec
"""
    wrong_rule = r'''
namespace SpecTec
open SpecTecProof
example
    (proof : «$ordered:regular:eval:rule:1:plan».Fails (.WRAP .ZERO)) :
    «$ordered:regular:eval:rule:0:plan».Fails (.WRAP .ZERO) := by
  spec_check_certificate proof using id
end SpecTec
'''
    wrong_position = r'''
namespace SpecTec
example : SpecTecEval.RuleFailure
    («$ordered:regular:eval:rule:1:plan».premises ⟨.ZERO, ()⟩)
    «$ordered:regular:eval:rule:1:plan».recoverable := by
  apply SpecTecEval.RuleFailure.at 1 (Gate.evalSelected .ONE ())
  rfl
end SpecTec
'''
    abort_as_failure = r'''
namespace SpecTec
open SpecTecProof
private instance badBoundary :
    SpecTecEval.Boundary value String String where
  aborts := fun _ _ => True
  unsupported := fun _ _ => False
example (proof : Gate.eval 1 .ZERO (.abort "fatal")) :
    ∀ output, ¬ Gate.evalSucceeds .ZERO output := by
  spec_check_certificate proof using
    (SpecTecEval.Evaluator.ruleFailure_sound (evaluator := Gate.evaluator))
end SpecTec
'''
    one_output_failure = r'''
namespace SpecTec
example (onlyZero : ¬ Candidate.evalSelected 7 0) :
    SpecTecEval.OutputSearchFailure Nat (Candidate.evalSelected 7) := by
  refine ⟨?_⟩
  intro output
  exact onlyZero
end SpecTec
'''

    with tempfile.TemporaryDirectory(prefix="p4-local-proof-") as directory:
        root = Path(directory)
        support = root / "SpecTecProof.lean"
        support.write_text(args.support.read_text())
        run([
            "lean", "-j", "2", "-o", str(root / "SpecTecProof.olean"),
            str(support)
        ], cwd=root)
        env = dict(os.environ, LEAN_PATH=str(root))

        check_lean(
            root, env, "LocalInversion", relation, args.local_proof.read_text()
        )
        check_lean(root, env, "Certificates", ordered, certificate_proof)
        check_lean(root, env, "WrongRule", ordered, wrong_rule, succeeds=False)
        check_lean(
            root, env, "WrongPosition", ordered, wrong_position, succeeds=False
        )
        check_lean(
            root, env, "AbortAsFailure", ordered, abort_as_failure,
            succeeds=False
        )
        check_lean(
            root, env, "OneOutputFailure", search, one_output_failure,
            succeeds=False
        )

    print("local proof support: inversion, induction, and certificates checked")


if __name__ == "__main__":
    main()

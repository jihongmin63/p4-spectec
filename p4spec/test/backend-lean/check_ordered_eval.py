#!/usr/bin/env python3
"""Check ordered evaluator outcomes, prefix flow, and output-search failure."""

import argparse
from pathlib import Path
import subprocess
import tempfile


def translate(exe: Path, source: Path) -> str:
    result = subprocess.run(
        [str(exe.resolve()), str(source)], capture_output=True, text=True
    )
    assert result.returncode == 0, result.stdout + result.stderr
    return result.stdout


def check_lean(source: str, proof: Path, target: Path, *, succeeds: bool) -> str:
    target.write_text(source + "\n" + proof.read_text())
    result = subprocess.run(
        ["lean", "-j", "2", str(target)], capture_output=True, text=True
    )
    if succeeds:
        assert result.returncode == 0, result.stdout + result.stderr
    else:
        assert result.returncode != 0, "mutation unexpectedly type-checked"
    return result.stdout + result.stderr


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--ordered", type=Path, required=True)
    parser.add_argument("--ordered-proof", type=Path, required=True)
    parser.add_argument("--search", type=Path, required=True)
    parser.add_argument("--search-proof", type=Path, required=True)
    args = parser.parse_args()

    ordered = translate(args.exe, args.ordered)
    search = translate(args.exe, args.search)
    for generated in (ordered, search):
        assert "namespace SpecTecEval" in generated
        assert "inductive Outcome" in generated
        assert generated.count("structure EvalRulePlan") == 1
        assert generated.count("def EvalRulePlan.Succeeds") == 1
        assert generated.count("def EvalRulePlan.Fails") == 1
        assert generated.count("inductive Selected") == 1
        assert generated.count("inductive AllFailed") == 1
        assert "structure OutputSearchFailure" in generated
        assert "def MayContinue" in generated
        assert "mayContinue : position ∈ recoverable" in generated
        assert "OrderedFailures" not in generated
        for legacy in (":premises»", ":recoverable»", ":succeeds»", ":failed»", ":sound»"):
            assert legacy not in generated, f"legacy rule-flow declaration remains: {legacy}"
    assert "def «$ordered:regular:eval:rule:0:plan»" in ordered
    assert "def «$ordered:regular:eval:rule:1:plan»" in ordered
    assert "def «$ordered:regular:eval:rule:2:plan»" in ordered
    assert "def Candidate.evalRules" in search
    assert "SpecTecEval.Selected .nondeterministic (Candidate.evalRules)" in search
    assert len(ordered.encode()) < 87_000, "reified ordered fixture grew past its measured budget"
    assert "abbrev «$ordered».eval" in ordered
    assert "theorem «$ordered».success_sound" not in ordered
    assert "theorem «$ordered».ruleFailure_sound" not in ordered
    assert "theorem «$ordered».timeout" not in ordered
    assert "theorem «$ordered».abort_sound" not in ordered
    assert "theorem «$ordered».unsupported_sound" not in ordered
    assert "theorem «$ordered».timeout_sound" not in ordered
    assert "theorem «$ordered».undetermined_sound" not in ordered
    assert ":eval:rule:0:prefix:" not in ordered
    assert ":eval:rule:1:prefix:" not in ordered
    assert ":eval:rule:2:prefix:" not in ordered
    assert "abbrev «$ordered:regular».evalSelected" in ordered
    assert "def «$ordered:enabled».evaluator" not in ordered
    assert "SpecTecEval.Selected .ordered («$ordered:regular».evalRules)" in ordered
    assert "«$ordered:regular».evalSelected «arg:0» «arg:1»" in ordered
    assert "«$generic_option:eval:rule:0:plan» (X_T := X_T)" in ordered
    assert "(shadow : SpecTec.shadow) («eval:0» : (_root_.List SpecTec.shadow))" in ordered
    assert "abbrev Search.eval" in search
    assert "theorem Search.ruleFailure_sound" not in search
    assert "Candidate.evalSelected n candidate" in search
    candidate_selection = search.split("abbrev Candidate.evalSelected", 1)[1].split(
        "theorem Candidate.selected_sound", 1
    )[0]
    assert "SpecTecEval.Selected .nondeterministic (Candidate.evalRules)" in candidate_selection
    assert " ∨" not in candidate_selection

    common_plan_proof = r'''
namespace SpecTecEvalPlanTest
open SpecTecEval

private def emptyPlan : EvalRulePlan Nat Nat (fun input output => input = output) where
  Witness := Nat
  input := fun witness => witness
  output := fun witness => witness
  premises := fun _ => []
  recoverable := []
  publicSound := by
    intro witness _
    rfl

example : emptyPlan.Succeeds 3 3 := by
  change ∃ witness : Nat, 3 = witness ∧ 3 = witness ∧ Prefix []
  exact ⟨3, rfl, rfl, trivial⟩

private def dependentPlan : EvalRulePlan Unit Nat (fun _ _ => True) where
  Witness := Sigma fun size : Nat => Fin (size + 1)
  input := fun _ => ()
  output := fun witness => witness.2.val
  premises := fun witness => [witness.2.val < witness.1 + 1]
  recoverable := [0]
  publicSound := by
    intro _ _
    trivial

example : dependentPlan.Succeeds () 0 := by
  change ∃ witness : Sigma fun size : Nat => Fin (size + 1),
    () = () ∧ 0 = witness.2.val ∧ Prefix [witness.2.val < witness.1 + 1]
  exact ⟨⟨0, 0⟩, rfl, rfl, ⟨by decide, trivial⟩⟩

private def zeroPlan : EvalRulePlan Nat Nat (fun _ _ => True) where
  Witness := Unit
  input := fun _ => 0
  output := fun _ => 0
  premises := fun _ => []
  recoverable := []
  publicSound := by intros; trivial

private def onePlan : EvalRulePlan Nat Nat (fun _ _ => True) where
  Witness := Unit
  input := fun _ => 1
  output := fun _ => 1
  premises := fun _ => []
  recoverable := []
  publicSound := by intros; trivial

private def zeroOnePlan : EvalRulePlan Nat Nat (fun _ _ => True) where
  Witness := Unit
  input := fun _ => 0
  output := fun _ => 1
  premises := fun _ => []
  recoverable := []
  publicSound := by intros; trivial

private theorem zeroFailsAtOne : zeroPlan.Fails 1 := by
  simp [EvalRulePlan.Fails, zeroPlan]

private theorem zeroSucceedsAtZero : zeroPlan.Succeeds 0 0 := by
  exact ⟨(), by simp [zeroPlan], by simp [zeroPlan], trivial⟩

private theorem oneSucceedsAtOne : onePlan.Succeeds 1 1 := by
  exact ⟨(), by simp [onePlan], by simp [onePlan], trivial⟩

private theorem zeroOneSucceedsAtOne : zeroOnePlan.Succeeds 0 1 := by
  exact ⟨(), by simp [zeroOnePlan], by simp [zeroOnePlan], trivial⟩

private theorem zeroFailsAtTwo : zeroPlan.Fails 2 := by
  simp [EvalRulePlan.Fails, zeroPlan]

private theorem oneFailsAtTwo : onePlan.Fails 2 := by
  simp [EvalRulePlan.Fails, onePlan]

example : Selected .ordered [zeroPlan, onePlan] 1 1 := by
  exact .laterOrdered zeroFailsAtOne (.here oneSucceedsAtOne)

example : Selected .nondeterministic [zeroPlan, zeroOnePlan] 0 0 := by
  exact .here zeroSucceedsAtZero

example : Selected .nondeterministic [zeroPlan, zeroOnePlan] 0 1 := by
  exact .laterNondeterministic (.here zeroOneSucceedsAtOne)

example : AllFailed [zeroPlan, onePlan] 2 := by
  exact AllFailed.cons zeroFailsAtTwo
    (AllFailed.cons oneFailsAtTwo (AllFailed.nil 2))

example (proof : Selected .ordered [zeroPlan, onePlan] 1 1) : True :=
  proof.sound

end SpecTecEvalPlanTest
'''

    with tempfile.TemporaryDirectory(prefix="p4-ordered-eval-") as directory:
        root = Path(directory)
        empty_source = root / "empty.watsup"
        empty_source.write_text("dec $sink<T>() : T\n")
        empty = translate(args.exe, empty_source)
        empty_proof = root / "EmptyProof.lean"
        empty_proof.write_text("")
        check_lean(empty, empty_proof, root / "Empty.lean", succeeds=True)
        common = root / "CommonPlanProof.lean"
        common.write_text(common_plan_proof)
        check_lean(ordered, common, root / "CommonPlan.lean", succeeds=True)
        check_lean(ordered, args.ordered_proof, root / "Ordered.lean", succeeds=True)
        check_lean(search, args.search_proof, root / "Search.lean", succeeds=True)
        mutated = ordered.replace(
            "| .recoverableFailure => True\n  | _ => False",
            "| .recoverableFailure | .abort _ => True\n  | _ => False",
            1,
        )
        assert mutated != ordered, "continuation gate mutation did not apply"
        check_lean(mutated, args.ordered_proof, root / "Mutated.lean", succeeds=False)
        one_candidate = search.replace(
            "noSuccess : ∀ output, ¬ succeeds output",
            "noSuccess : ∃ output, ¬ succeeds output",
            1,
        )
        assert one_candidate != search, "output-search mutation did not apply"
        check_lean(
            one_candidate,
            args.search_proof,
            root / "OneCandidate.lean",
            succeeds=False,
        )

    print("ordered evaluator: outcomes, prefix flow, and universal search checked")


if __name__ == "__main__":
    main()

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
        assert "structure OutputSearchFailure" in generated
        assert "def MayContinue" in generated
        assert "mayContinue : position ∈ recoverable" in generated
        assert "OrderedFailures" not in generated
    assert "abbrev «$ordered».eval" in ordered
    assert "theorem «$ordered».success_sound" in ordered
    assert "«$ordered:regular:eval:rule:1:prefix:1»" in ordered
    assert "def «$ordered:regular».evalSelected" in ordered
    assert "SpecTecEval.Prefix ([«$ordered:regular:eval:rule:0:failed» input]" in ordered
    assert "«$ordered:regular».evalSelected «arg:0» «arg:1»" in ordered
    assert "abbrev Search.eval" in search
    assert "theorem Search.ruleFailure_sound" in search
    assert "Candidate.evalSelected n candidate" in search
    candidate_selection = search.split("def Candidate.evalSelected", 1)[1].split(
        "theorem Candidate.selected_sound", 1
    )[0]
    assert "SpecTecEval.Prefix" not in candidate_selection
    assert "«Candidate:eval:rule:0:succeeds» input output ∨" in candidate_selection
    assert "«Candidate:eval:rule:1:succeeds» input output" in candidate_selection

    with tempfile.TemporaryDirectory(prefix="p4-ordered-eval-") as directory:
        root = Path(directory)
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

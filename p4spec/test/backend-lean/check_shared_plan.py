#!/usr/bin/env python3
"""Compile the shared typed-plan laws and check their axiom dependencies."""
import argparse
import re
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    args = parser.parse_args()
    generated = subprocess.run(
        [str(args.exe.resolve()), str(args.source)], capture_output=True, text=True,
        check=True).stdout
    boundary = generated.index("end SpecTecPlan") + len("end SpecTecPlan")
    core = generated[:boundary]
    # Each rule body belongs to the typed telescope, including its premises.
    assert not re.search(r"^(?:def|abbrev) .*:eval:rule:", generated[boundary:], re.M), \
        "separate per-rule evaluator declarations remain"
    assert "publicSound :=" not in generated[boundary:]
    assert "premises :=" not in generated[boundary:]
    with tempfile.TemporaryDirectory(prefix="p4-shared-plan-") as directory:
        target = Path(directory) / "SharedPlan.lean"
        target.write_text(core + "\n" + args.proof.read_text())
        checked = subprocess.run(["lean", "-j", "2", str(target)],
                                 capture_output=True, text=True)
        output = checked.stdout + checked.stderr
        assert checked.returncode == 0, output
        assert "sorryAx" not in output, output
        for name in ("Plan.premises_iff", "Plan.eval_premises_sound",
                     "Alternative.toEvalRule", "ProgramOf.holds_cases"):
            assert f"'SpecTecPlan.{name}' depends on axioms: [propext]" in output
    print("shared plan: membership, ordered premises, evaluator soundness and typed inversion checked")


if __name__ == "__main__":
    main()

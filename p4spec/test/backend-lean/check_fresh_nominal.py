#!/usr/bin/env python3
"""Check default nominal fresh identities, rollback, and observation audit."""

import argparse
from pathlib import Path
import subprocess
import tempfile


def run(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, capture_output=True, text=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--unsafe", type=Path, required=True)
    parser.add_argument("--alpha", type=Path, required=True)
    args = parser.parse_args()
    exe = str(args.exe.resolve())

    translated = run([exe, str(args.source)])
    assert translated.returncode == 0, translated.stdout + translated.stderr
    generated = translated.stdout
    assert "-- SpecTec Lean mode: relation-local" in generated
    assert "namespace SpecTecFresh" in generated
    assert "structure FreshId" in generated
    assert "inductive FreshName" in generated
    assert "structure Supply" in generated
    assert "def «$nominal_pair».freshSites" in generated
    assert "SpecTecFresh.AllocatedAt" in generated
    assert "fresh:counter" not in generated
    assert "$fresh_typeId:state" not in generated
    assert '"FRESH__" ++' not in generated

    with tempfile.TemporaryDirectory(prefix="p4-fresh-nominal-") as directory:
        root = Path(directory)
        target = root / "FreshNominal.lean"
        target.write_text(generated + "\n" + args.proof.read_text())
        checked = run(["lean", "-j", "2", str(target)])
        assert checked.returncode == 0, checked.stdout + checked.stderr

        alpha = run([exe, str(args.alpha)])
        assert alpha.returncode == 0, alpha.stdout + alpha.stderr
        assert "def FreshNominalAlphaIR" in alpha.stdout
        assert "theorem FreshNominalAlphaIR.refl" in alpha.stdout
        alpha_target = root / "FreshNominalAlpha.lean"
        alpha_target.write_text(alpha.stdout)
        alpha_checked = run(["lean", "-j", "2", str(alpha_target)])
        assert alpha_checked.returncode == 0, alpha_checked.stdout + alpha_checked.stderr

    rejected = run([exe, str(args.unsafe)])
    assert rejected.returncode == 1, rejected.stdout + rejected.stderr
    assert "fresh compatibility:" in rejected.stderr, rejected.stderr
    assert "string concatenation" in rejected.stderr, rejected.stderr
    assert "--fresh-exact-counter" in rejected.stderr, rejected.stderr

    exact = run([exe, "--fresh-exact-counter", str(args.unsafe)])
    assert exact.returncode == 0, exact.stdout + exact.stderr
    assert "-- SpecTec Lean mode: legacy-fresh-exact-counter" in exact.stdout
    assert "$fresh_typeId:state" in exact.stdout
    assert '"FRESH__"' in exact.stdout

    print("fresh nominal: identities, rollback, alpha consistency, and audit checked")


if __name__ == "__main__":
    main()

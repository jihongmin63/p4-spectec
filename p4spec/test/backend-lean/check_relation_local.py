#!/usr/bin/env python3
"""Check that the default Lean semantics is relation/SCC local."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--legacy-proof", type=Path, required=True)
    args = parser.parse_args()

    generated = subprocess.run(
        [str(args.exe.resolve()), str(args.source)],
        capture_output=True,
        text=True,
    )
    assert generated.returncode == 0, generated.stdout + generated.stderr
    lean = generated.stdout

    scopes = []
    root_semantics = []
    for line in lean.splitlines():
        if line.startswith("namespace "):
            scopes.append(line.removeprefix("namespace ").strip())
        elif line == "end" or line.startswith("end "):
            if scopes:
                scopes.pop()
        elif re.match(r"^(?:inductive|abbrev) (?:Atom|InProgram)\b", line):
            if scopes == ["SpecTec"]:
                root_semantics.append(line)
    assert not root_semantics, \
        f"default output still exposes program-wide semantics: {root_semantics}"
    assert "namespace «Decl_ok:Semantics»" in lean
    assert "namespace «CycleA:Semantics»" in lean
    assert "namespace «$invoke:Semantics»" in lean
    assert "def Decl_ok" in lean
    assert "def Decl_ok.fails" in lean
    assert "def CycleA.undetermined" in lean
    assert "def Nat_ok.undetermined" not in lean
    assert ('relations := ["CycleA", "CycleB"], dependencies := [], '
            'recursive := true, negativeCycle := true') in lean
    decl_component = lean.split("namespace «Decl_ok:Semantics»", 1)[1].split(
        "end «Decl_ok:Semantics»", 1
    )[0]
    assert "SpecTecExternTypes" not in decl_component, \
        "an unused extern type polluted the Decl_ok component"
    assert "abbrev json" in lean, "the extern type interface disappeared"

    with tempfile.TemporaryDirectory(prefix="p4-relation-local-") as directory:
        directory = Path(directory)
        target = directory / "RelationLocal.lean"
        target.write_text(lean + "\n" + args.proof.read_text())
        checked = subprocess.run(
            ["lean", "-j", "2", str(target)], capture_output=True, text=True
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr

        legacy_command = [
            str(args.exe.resolve()), "--fresh-exact-counter", str(args.source)
        ]
        legacy = subprocess.run(legacy_command, capture_output=True, text=True)
        repeated = subprocess.run(legacy_command, capture_output=True, text=True)
        assert legacy.returncode == 0, legacy.stdout + legacy.stderr
        assert repeated.returncode == 0, repeated.stdout + repeated.stderr
        assert legacy.stdout == repeated.stdout, "legacy exact mode is not reproducible"
        assert re.search(r"^inductive Atom\b", legacy.stdout, re.MULTILINE)
        assert re.search(r"^inductive InProgram\b", legacy.stdout, re.MULTILINE)
        legacy_target = directory / "RelationLocalLegacy.lean"
        legacy_target.write_text(
            legacy.stdout + "\n" + args.legacy_proof.read_text()
        )
        legacy_checked = subprocess.run(
            ["lean", "-j", "2", str(legacy_target)], capture_output=True, text=True
        )
        assert legacy_checked.returncode == 0, \
            legacy_checked.stdout + legacy_checked.stderr

    print("relation local: SCC-local and explicit legacy judgements checked")


if __name__ == "__main__":
    main()

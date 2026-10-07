#!/usr/bin/env python3
"""Check hidden nominal supply, protected inputs, and concat provenance."""

import argparse
import hashlib
from pathlib import Path
import subprocess
import tempfile


def run(command):
    return subprocess.run(command, capture_output=True, text=True, timeout=180)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", required=True, type=Path)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--proof", required=True, type=Path)
    args = parser.parse_args()

    translated = run([str(args.exe.resolve()), str(args.source)])
    assert translated.returncode == 0, translated.stdout + translated.stderr
    generated = translated.stdout
    assert "SpecTecFresh.Allocates" in generated
    assert "SpecTecFresh.Derives" in generated
    assert "Program_ok:supply" in generated
    for relation in ("Program_ok", "Context_ok", "ExternalContext_ok"):
        collector = "FreshProtectedRelation_" + hashlib.md5(
            relation.encode()
        ).hexdigest()
        assert f"def {collector}" in generated
        assert f"Supply.root (_root_.SpecTec.{collector}" in generated
    assert "fresh:counter" not in generated
    assert "AllocatedAt" not in generated.split("namespace «Program_ok:Semantics»", 1)[1]

    with tempfile.TemporaryDirectory(prefix="p4-fresh-supply-") as directory:
        target = Path(directory) / "FreshSupply.lean"
        target.write_text(generated + "\n" + args.proof.read_text())
        checked = run(["lean", "-j", "2", str(target)])
        assert checked.returncode == 0, checked.stdout + checked.stderr

    print("fresh supply: dynamic paths, protected inputs, and concat provenance checked")


if __name__ == "__main__":
    main()

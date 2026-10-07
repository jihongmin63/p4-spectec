#!/usr/bin/env python3
"""Prove branch-local fresh rollback and shared successful allocation state."""

import argparse
from pathlib import Path
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--fixtures", type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    executable = str(args.exe.resolve())
    source = args.fixtures / "fresh-rollback.watsup"
    translated = subprocess.run(
        [executable, "--fresh-rollback", str(source)],
        capture_output=True, text=True,
    )
    assert translated.returncode == 0, translated.stdout + translated.stderr
    with tempfile.TemporaryDirectory(prefix="p4-fresh-rollback-") as directory:
        target = Path(directory) / "fresh-rollback.lean"
        target.write_text(
            translated.stdout + "\n"
            + (args.fixtures / "fresh-rollback-proof.lean").read_text()
        )
        proof = subprocess.run(
            ["lean", "-j", "2", str(target)],
            capture_output=True, text=True, timeout=120,
        )
        assert proof.returncode == 0, proof.stdout + proof.stderr
        assert "sorry" not in proof.stdout, proof.stdout

        higher_order = Path(directory) / "higher-order.watsup"
        higher_order.write_text("""
syntax typeId = text
builtin dec $fresh_typeId() : typeId
dec $once() : typeId
def $once() = $fresh_typeId()
dec $apply(def $step() : typeId) : typeId
def $apply(def $step) = $step()
dec $higher_order() : typeId
def $higher_order() = $apply(def $once)
""")
        rejected = subprocess.run(
            [executable, "--fresh-rollback", str(higher_order)],
            capture_output=True, text=True,
        )
        assert rejected.returncode == 1, rejected.stdout + rejected.stderr
        assert "stateful function argument $once" in rejected.stderr, rejected.stderr
    print("fresh rollback: failed alternatives reset; successful calls share state")


if __name__ == "__main__":
    main()

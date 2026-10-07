#!/usr/bin/env python3
"""Check generated fresh-name alpha comparison and its constructive proofs."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def run(command, *, cwd=None):
    result = subprocess.run(command, capture_output=True, text=True, cwd=cwd, timeout=120)
    output = result.stdout + result.stderr
    if result.returncode:
        raise AssertionError(output)
    if "sorryAx" in output:
        raise AssertionError("proof used sorryAx\n" + output)
    return output


def check_axioms(output):
    allowed = {"propext", "Quot.sound", "Classical.choice"}
    declarations = 0
    for line in output.splitlines():
        if "does not depend on any axioms" in line:
            declarations += 1
        if "depends on axioms:" in line:
            declarations += 1
            found = re.search(r"\[([^]]*)\]", line)
            if not found:
                raise AssertionError("unreadable axiom report: " + line)
            axioms = {item.strip() for item in found.group(1).split(",") if item.strip()}
            if axioms - allowed:
                raise AssertionError("nonstandard proof axiom: " + line)
    if not declarations:
        raise AssertionError("Lean did not print proof axiom reports")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--fixtures", type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    exe = str(args.exe.resolve())
    fixtures = args.fixtures.resolve()
    with tempfile.TemporaryDirectory(prefix="p4-fresh-alpha-") as directory:
        root = Path(directory)
        for name in ["fresh-alpha", "fresh-alpha-extern", "fresh-alpha-text", "fresh-alpha-alias", "fresh-alpha-shadow"]:
            generated = run([exe, "--fresh-rollback", str(fixtures / (name + ".watsup"))])
            if "FreshAlphaIR" not in generated:
                raise AssertionError("alpha API was not generated")
            if "FreshRename_unreachableAlpha" in generated:
                raise AssertionError("alpha renderer traversed unreachable IR types")
            if re.search(r"\b(?:axiom|sorry|partial|opaque)\b", generated[generated.index("def FreshNameSwap"):]):
                raise AssertionError("alpha support contains a nonconstructive declaration")
            target = root / (name + ".lean")
            target.write_text(generated + "\n" + (fixtures / (name + "-proof.lean")).read_text())
            output = run(["lean", "-j", "2", str(target)], cwd=root)
            check_axioms(output)
            print(name + ": proved swap, identity, and preserved data")
        exact = run([exe, str(fixtures / "fresh-alpha.watsup")])
        if "FreshAlphaIR" in exact:
            raise AssertionError("default exact output unexpectedly contains alpha support")
        unrelated = root / "unrelated.watsup"
        unrelated.write_text("syntax unrelated = VALUE text\n")
        generated = run([exe, "--fresh-rollback", str(unrelated)])
        if "FreshNameSwap" in generated or "FreshAlphaIR" in generated:
            raise AssertionError("alpha support was generated without p4programIR")
        unsupported = fixtures / "fresh-alpha-unsupported.watsup"
        for flags in [[], ["--keep-going"]]:
            result = subprocess.run(
                [exe, "--fresh-rollback", *flags, str(unsupported)],
                capture_output=True, text=True, timeout=120,
            )
            if result.returncode != 1 or "fresh abstraction:" not in result.stderr:
                raise AssertionError("unsupported alpha shape did not produce a diagnostic\n" + result.stderr)
            if "Fatal error" in result.stderr or result.stdout:
                raise AssertionError("unsupported alpha shape emitted an exception or partial source")
        print("alpha support scope and unsupported diagnostics: verified")


if __name__ == "__main__":
    main()

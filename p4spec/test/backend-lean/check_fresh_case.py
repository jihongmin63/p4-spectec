#!/usr/bin/env python3
"""Check oracle provenance and both halves of fresh-abstract case obligations."""

import argparse
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    args = parser.parse_args()
    exe = str(args.exe.resolve())
    fixtures = Path(__file__).resolve().parent
    source = fixtures / "fresh-case.watsup"
    empty = fixtures / "case-empty.p4"

    def run(*arguments):
        return subprocess.run([exe, *map(str, arguments)], text=True,
                              capture_output=True, timeout=60)

    oracle = run("--dump-output", empty, source)
    assert oracle.returncode == 0, oracle.stderr
    assert oracle.stdout.strip() == '(@p4programIR.RESULT "FRESH__1" "FRESH__1" "FRESH__99")'

    with tempfile.TemporaryDirectory(prefix="p4-fresh-case-") as directory:
        directory = Path(directory)
        expected = directory / "expected.lean"
        expected.write_text(oracle.stdout)
        for mode in ((), ("--fresh-rollback",)):
            translated = run(*mode, "--case", empty, expected,
                             "--case", empty, expected, source)
            assert translated.returncode == 0, translated.stderr
            code = translated.stdout
            for index in range(2):
                assert f'def case_{index}_fresh_names : List String := ["FRESH__0", "FRESH__1"]' in code
                assert f'def case_{index}_protected_names : List String := ["FRESH__99"]' in code
                assert f'(∃ output : p4programIR, Program_ok case_{index}_input output ∧' in code
                assert code.count(f'FreshAlphaIR case_{index}_fresh_names case_{index}_protected_names case_{index}_expected output') == 2

        exact = run("--fresh-exact-counter", "--obligations-only",
                    "--case", empty, expected, source)
        assert exact.returncode == 0, exact.stderr
        assert "_fresh_names" not in exact.stdout
        assert "FreshAlphaIR" not in exact.stdout
        proof = directory / "cases.lean"
        proof.write_text(code + "\n" + (fixtures / "fresh-case-proof.lean").read_text())
        lean = subprocess.run(["lean", "-j", "2", str(proof)], text=True,
                              capture_output=True, timeout=120)
        assert lean.returncode == 0, lean.stdout + lean.stderr
        assert "sorry" not in lean.stdout, lean.stdout

        # An ordinary literal can have exactly an allocated name's spelling.
        # Its different runtime identity must pin that spelling nevertheless.
        collision = directory / "collision.watsup"
        collision.write_text(source.read_text().replace('"FRESH__99"', '"FRESH__0"'))
        collision_oracle = run("--dump-output", empty, collision)
        assert collision_oracle.returncode == 0, collision_oracle.stderr
        expected.write_text(collision_oracle.stdout)
        collision_cases = run("--fresh-rollback", "--obligations-only",
                              "--case", empty, expected, collision)
        assert collision_cases.returncode == 0, collision_cases.stderr
        assert 'case_0_protected_names : List String := ["FRESH__0"]' in collision_cases.stdout

        expected.write_text(oracle.stdout.replace('"FRESH__99"', '"changed"'))
        invalid = run("--fresh-rollback", "--obligations-only",
                      "--case", empty, expected, source)
        assert invalid.returncode == 1, invalid.stdout + invalid.stderr
        assert "expected output differs from" in invalid.stderr, invalid.stderr
    print("fresh cases: oracle allocations, ordinary text, repeat references and quotient uniqueness checked")


if __name__ == "__main__":
    main()

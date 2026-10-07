#!/usr/bin/env python3
"""Check that batch evaluation resets stateful P4 builtins between programs."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--spec", type=Path, required=True)
    parser.add_argument("--include", type=Path, required=True)
    parser.add_argument("--first", type=Path, required=True)
    parser.add_argument("--middle", type=Path, required=True)
    args = parser.parse_args()
    first = Path(os.path.abspath(args.first))
    middle = Path(os.path.abspath(args.middle))
    common = ["-I", str(args.include.resolve()), str(args.spec.resolve())]
    with tempfile.TemporaryDirectory(prefix="p4-fresh-") as directory:
        paths = Path(directory) / "paths.list"
        paths.write_text(f"{first}\n{middle}\n{first}\n")
        batch = subprocess.run(
            [str(args.exe.resolve()), "--batch-cases", str(paths), *common],
            capture_output=True, text=True, check=True,
        )
    rows = [line.split("\t", 2) for line in batch.stdout.splitlines()]
    if len(rows) != 3 or any(len(row) != 3 or row[0] != "accept" for row in rows):
        raise ValueError("the batch did not accept all three programs")
    if rows[0][2] != rows[2][2] or "FRESH__0" not in rows[0][2]:
        raise ValueError("fresh_typeId output depends on earlier programs")
    single = subprocess.run(
        [str(args.exe.resolve()), "--dump-output", str(first), *common],
        capture_output=True, text=True, check=True,
    )
    if single.stdout != rows[0][2] + "\n":
        raise ValueError("batch and standalone IR answers differ")
    print("fresh reset verified")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Compare fixed Lean type-checking answers with the SpecTec SL interpreter."""

import argparse
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--spec", type=Path, required=True)
    parser.add_argument("--include", type=Path, required=True)
    args = parser.parse_args()

    accepted = rejected = 0
    for line_number, line in enumerate(args.manifest.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) not in (2, 3) or fields[0] not in ("accept", "reject"):
            parser.error(f"{args.manifest}:{line_number}: invalid entry")
        status, source_name = fields[:2]
        if (status == "accept") != (len(fields) == 3):
            parser.error(f"{args.manifest}:{line_number}: expected output required only for accept")
        source = (args.manifest.parent / source_name).resolve()
        command = [
            str(args.exe.resolve()),
            "--dump-output" if status == "accept" else "--check-rejection",
            str(source),
            "-I", str(args.include.resolve()),
            str(args.spec.resolve()),
        ]
        result = subprocess.run(command, capture_output=True)
        if status == "accept":
            expected = (args.manifest.parent / fields[2]).read_bytes()
            if result.returncode != 0 or result.stdout != expected:
                print(f"oracle mismatch: {source}", file=sys.stderr)
                if result.returncode != 0:
                    print(result.stderr.decode(errors="replace")[:1000], file=sys.stderr)
                return 1
            accepted += 1
        elif result.returncode == 0 and result.stdout == b"rejected\n":
            rejected += 1
        else:
            print(f"invalid rejection: {source}", file=sys.stderr)
            print(result.stderr.decode(errors="replace")[:1000], file=sys.stderr)
            return 1
    print(f"exact outputs verified: {accepted}; rejections verified: {rejected}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Re-evaluate fixed Lean answers and rejection claims with the SpecTec SL interpreter."""

import argparse
from collections import Counter
import gzip
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def source_path(base: Path, name: str) -> Path:
    return Path(os.path.abspath(base / name))


def read_manifest(path: Path):
    entries = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) not in (2, 3) or fields[0] not in (
            "accept", "reject", "abort-reject"
        ):
            raise ValueError(f"{path}:{number}: invalid entry")
        status, name = fields[:2]
        if (status == "accept") != (len(fields) == 3):
            raise ValueError(f"{path}:{number}: expected output required only for accept")
        source = source_path(path.parent, name)
        oracle = path.parent / fields[2] if status == "accept" else None
        if source in entries:
            raise ValueError(f"{path}:{number}: duplicate source {source}")
        entries[source] = (status, oracle)
    return entries


def read_audit(path: Path, root: Path):
    lines = path.read_text().splitlines()
    if not lines or lines[0] != (
        "logged_expected\tlogged_result\tactual\tsource\toracle\tsuite\tdetail"
    ):
        raise ValueError(f"{path}: invalid header")
    entries = []
    for number, line in enumerate(lines[1:], 2):
        fields = line.split("\t", 6)
        if len(fields) != 7:
            raise ValueError(f"{path}:{number}: invalid entry")
        _, _, actual, name, oracle_name, _, detail = fields
        if detail == "-":
            detail = ""
        source = source_path(root, name)
        oracle = path.parent / oracle_name if oracle_name else None
        entries.append((actual, source, oracle, detail))
    return entries


def expected_bytes(path: Path) -> bytes:
    if path.suffix == ".gz":
        with gzip.open(path, "rb") as compressed:
            return compressed.read()
    return path.read_bytes()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--audit", type=Path, help="verify every case, including parser failures")
    parser.add_argument("--reverse", action="store_true", help="evaluate cases in reverse order")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[3])
    parser.add_argument("--spec", type=Path, required=True)
    parser.add_argument("--include", type=Path, required=True)
    args = parser.parse_args()

    try:
        manifest = read_manifest(args.manifest)
        if args.audit:
            entries = read_audit(args.audit, args.root.resolve())
            eligible = {
                source: ("abort-reject" if status == "abort" else status, oracle)
                for status, source, oracle, _ in entries
                if status in ("accept", "reject", "abort")
            }
            if eligible != manifest:
                raise ValueError("proof manifest does not match parseable audit entries")
        else:
            entries = [("abort" if status == "abort-reject" else status,
                        source, oracle, "")
                       for source, (status, oracle) in manifest.items()]
        if args.reverse:
            entries.reverse()

        with tempfile.TemporaryDirectory(prefix="p4-typecheck-") as directory:
            temporary = Path(directory)
            input_path = temporary / "cases.list"
            result_path = temporary / "results.tsv"
            error_path = temporary / "errors.log"
            input_path.write_text("".join(str(source) + "\n" for _, source, _, _ in entries))
            command = [
                str(args.exe.resolve()), "--batch-cases", str(input_path),
                "-I", str(args.include.resolve()), str(args.spec.resolve()),
            ]
            with result_path.open("wb") as output, error_path.open("wb") as errors:
                result = subprocess.run(command, stdout=output, stderr=errors)
            if result.returncode != 0:
                raise ValueError(
                    f"batch interpreter failed: {error_path.read_text(errors='replace')[:1000]}"
                )
            counts = Counter()
            with result_path.open() as results:
                for expected_status, source, oracle, detail in entries:
                    line = results.readline()
                    fields = line.rstrip("\n").split("\t", 2)
                    if len(fields) != 3:
                        raise ValueError(f"missing or invalid result for {source}")
                    status, reported_source, reported_detail = fields
                    if status != expected_status or reported_source != str(source):
                        raise ValueError(
                            f"status mismatch for {source}: expected {expected_status}, got {status}"
                        )
                    if status == "accept":
                        if oracle is None or expected_bytes(oracle) != (reported_detail + "\n").encode():
                            raise ValueError(f"exact IR output mismatch for {source}")
                    elif args.audit and status in (
                        "syntax", "abort", "bad-arity", "translation-error", "crash"
                    ):
                        if reported_detail != detail:
                            raise ValueError(f"diagnostic mismatch for {source}")
                    counts[status] += 1
                if results.readline():
                    raise ValueError("batch interpreter returned extra cases")
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1

    message = f"exact outputs verified: {counts['accept']}; rejections verified: {counts['reject']}"
    if args.audit:
        message += f"; syntax: {counts['syntax']}; abort: {counts['abort']}"
    print(message)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

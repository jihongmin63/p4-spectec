#!/usr/bin/env python3
"""Freeze a complete --batch-cases scan as compressed Lean output answers."""

import argparse
from collections import Counter
import gzip
import os
from pathlib import Path

import discover_typecheck as discovery


HERE = Path(__file__).resolve().parent
ROOT = discovery.DEFAULT_ROOT


def records():
    found = {}
    for suite, expected in discovery.SUITES:
        found.update(discovery.read_suite(ROOT, suite, expected))
    return found


def rows(path: Path):
    with path.open() as scan:
        for number, line in enumerate(scan, 1):
            fields = line.rstrip("\n").split("\t", 2)
            if len(fields) != 3:
                raise ValueError(f"{path}:{number}: expected status, source, and detail")
            actual, name, detail = fields
            yield number, actual, Path(os.path.abspath(name)), detail


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan", type=Path, required=True, help="output of --batch-cases")
    args = parser.parse_args()
    found = records()

    # Reject incomplete or duplicated scans before changing the corpus.
    seen = set()
    for number, _, source, _ in rows(args.scan):
        if source not in found or source in seen:
            raise ValueError(f"{args.scan}:{number}: unexpected or repeated source {source}")
        seen.add(source)
    if seen != set(found):
        raise ValueError(f"scan is missing {len(set(found) - seen)} sources")

    manifest_lines = [
        "# Deterministic SpecTec Program_ok outcomes and one aborting negative proof target.",
        "# See typecheck-audit.tsv for original expectations and 39 parser failures.",
    ]
    audit_lines = ["logged_expected\tlogged_result\tactual\tsource\toracle\tsuite\tdetail"]
    counts = Counter()
    oracle_root = HERE / "oracles" / "full"
    for _, actual, source, detail in rows(args.scan):
        expected, logged, suite = found[source]
        source_rel = source.relative_to(ROOT)
        manifest_source = os.path.relpath(source, HERE)
        oracle = ""
        if actual == "accept":
            oracle_path = oracle_root / source_rel.parent / (source_rel.name + ".lean.gz")
            oracle_path.parent.mkdir(parents=True, exist_ok=True)
            with oracle_path.open("wb") as output:
                with gzip.GzipFile(fileobj=output, mode="wb", filename="",
                                   compresslevel=6, mtime=0) as compressed:
                    compressed.write((detail + "\n").encode())
            oracle = os.path.relpath(oracle_path, HERE)
            manifest_lines.append(f"accept\t{manifest_source}\t{oracle}")
            detail = ""
        elif actual == "reject":
            manifest_lines.append(f"reject\t{manifest_source}")
        elif actual == "abort" and expected == "reject":
            manifest_lines.append(f"abort-reject\t{manifest_source}")
        elif actual not in ("syntax", "abort", "bad-arity", "translation-error", "crash"):
            raise ValueError(f"unexpected result for {source}: {actual}")
        counts[actual] += 1
        audit_lines.append(
            f"{expected}\t{logged}\t{actual}\t{source_rel}\t{oracle}\t{suite}\t{detail or '-'}"
        )

    (HERE / "typecheck-cases.tsv").write_text("\n".join(manifest_lines) + "\n")
    (HERE / "typecheck-audit.tsv").write_text("\n".join(audit_lines) + "\n")
    print(
        f"cases: {sum(counts.values())}; obligations: "
        f"{counts['accept'] + counts['reject'] + counts['abort']}; "
        f"exact outputs: {counts['accept']}; rejections: {counts['reject']}; "
        f"syntax: {counts['syntax']}; abort: {counts['abort']}"
    )


if __name__ == "__main__":
    main()

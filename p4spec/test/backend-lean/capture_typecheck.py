#!/usr/bin/env python3
"""Freeze a complete --batch-cases scan as compressed Lean output answers."""

import argparse
from collections import Counter
import gzip
import os
from pathlib import Path
import subprocess
import tempfile

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


def scan(args, sources) -> None:
    """Split the sorted sources over parallel --batch-cases runs and merge them in order.

    Each program starts with reset builtins and caches, so the split cannot change outputs."""
    chunks = [sources[i::args.jobs] for i in range(args.jobs)]
    with tempfile.TemporaryDirectory(prefix="p4-capture-") as directory:
        temporary = Path(directory)
        processes = []
        for index, chunk in enumerate(chunks):
            paths = temporary / f"{index}.list"
            paths.write_text("".join(f"{source}\n" for source in chunk))
            command = [str(args.exe.resolve()), "--interpreter", args.interpreter,
                       "--batch-cases", str(paths), "-I", str(args.include.resolve()),
                       str(args.spec.resolve())]
            with (temporary / f"{index}.tsv").open("wb") as output, \
                    (temporary / f"{index}.err").open("wb") as errors:
                processes.append(subprocess.Popen(command, stdout=output, stderr=errors))
        lines = {}
        for index, process in enumerate(processes):
            if process.wait() != 0:
                error = (temporary / f"{index}.err").read_text(errors="replace")
                raise ValueError(f"batch interpreter failed: {error[:1000]}")
            for line in (temporary / f"{index}.tsv").read_text().splitlines(keepends=True):
                lines[Path(os.path.abspath(line.split("\t", 2)[1]))] = line
    missing = [source for source in sources if source not in lines]
    if missing:
        raise ValueError(f"batch interpreter returned no result for {missing[0]}")
    args.scan.parent.mkdir(parents=True, exist_ok=True)
    args.scan.write_text("".join(lines[source] for source in sources))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scan", type=Path, required=True,
                        help="output of --batch-cases; with --exe, where to write a new scan")
    parser.add_argument("--exe", type=Path, help="run the scan with this lean-skeleton executable")
    parser.add_argument("--interpreter", choices=("sl", "al"), default="sl",
                        help="SpecTec interpreter for --exe (default: sl)")
    parser.add_argument("--jobs", type=int, default=8, help="parallel --batch-cases processes for --exe")
    parser.add_argument("--spec", type=Path, default=ROOT / "spec")
    parser.add_argument("--include", type=Path, default=ROOT / "p4c" / "p4include")
    parser.add_argument("--oracles", type=Path, default=HERE / "oracles" / "full",
                        help="directory for compressed answers")
    parser.add_argument("--manifest", type=Path, default=HERE / "typecheck-cases.tsv")
    parser.add_argument("--audit", type=Path, default=HERE / "typecheck-audit.tsv")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    found = records()
    if args.exe:
        scan(args, sorted(found))

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
        f"# See {args.audit.name} for original expectations and 39 parser failures.",
    ]
    if args.interpreter != "sl":
        manifest_lines.append(f"# Answers from the {args.interpreter.upper()} interpreter.")
    base = args.manifest.resolve().parent
    audit_lines = ["logged_expected\tlogged_result\tactual\tsource\toracle\tsuite\tdetail"]
    counts = Counter()
    oracle_root = args.oracles.resolve()
    for _, actual, source, detail in rows(args.scan):
        expected, logged, suite = found[source]
        source_rel = source.relative_to(ROOT)
        manifest_source = os.path.relpath(source, base)
        oracle = ""
        if actual == "accept":
            oracle_path = oracle_root / source_rel.parent / (source_rel.name + ".lean.gz")
            oracle_path.parent.mkdir(parents=True, exist_ok=True)
            with oracle_path.open("wb") as output:
                with gzip.GzipFile(fileobj=output, mode="wb", filename="",
                                   compresslevel=6, mtime=0) as compressed:
                    compressed.write((detail + "\n").encode())
            oracle = os.path.relpath(oracle_path, args.audit.resolve().parent)
            manifest_lines.append(f"accept\t{manifest_source}\t{os.path.relpath(oracle_path, base)}")
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

    args.manifest.write_text("\n".join(manifest_lines) + "\n")
    args.audit.write_text("\n".join(audit_lines) + "\n")
    print(
        f"cases: {sum(counts.values())}; obligations: "
        f"{counts['accept'] + counts['reject'] + counts['abort']}; "
        f"exact outputs: {counts['accept']}; rejections: {counts['reject']}; "
        f"syntax: {counts['syntax']}; abort: {counts['abort']}"
    )


if __name__ == "__main__":
    main()

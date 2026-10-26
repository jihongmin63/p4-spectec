#!/usr/bin/env python3
"""Inventory repository P4 static-semantics cases recorded by the SL suites."""

import argparse
from collections import Counter
import os
from pathlib import Path


DEFAULT_ROOT = Path(__file__).resolve().parents[3]
SUITES = (
    ("p4spec/test/run/run_pos_sl.expected", "accept"),
    ("p4spec/test/run/run_neg_sl.expected", "reject"),
    ("p4spec/test/run/run_regression_pos_sl.expected", "accept"),
    ("p4spec/test/run/run_regression_neg_sl.expected", "reject"),
    ("p4spec/test/micro/micro_run_pos_sl.expected", "accept"),
    ("p4spec/test/micro/micro_run_neg_sl.expected", "reject"),
)
BOOT_SUITES = (
    ("p4spec/test/boot/boot_2_pos_sl.expected", "accept"),
    ("p4spec/test/boot/boot_2_neg_sl.expected", "reject"),
)
PREFIXES = {
    "Run success: ": "pass",
    "Error on run: ": "fail",
    "Excluding file: ": "excluded",
}


def read_suite(root: Path, name: str, expectation: str):
    log = root / name
    records = {}
    for number, line in enumerate(log.read_text().splitlines(), 1):
        for prefix, outcome in PREFIXES.items():
            if not line.startswith(prefix):
                continue
            source_name = line[len(prefix):]
            if prefix == "Error on run: ":
                for suffix in (" (unknown)", " (should fail)"):
                    if source_name.endswith(suffix):
                        source_name = source_name[:-len(suffix)]
            source = Path(os.path.abspath(log.parent / source_name))
            if not source.is_file():
                raise ValueError(f"{log}:{number}: missing P4 source {source}")
            if source in records:
                raise ValueError(f"{log}:{number}: duplicate P4 source {source}")
            if outcome != "excluded" and outcome != (
                "pass" if expectation == "accept" else "fail"
            ):
                raise ValueError(f"{log}:{number}: unexpected outcome {outcome}")
            records[source] = (expectation, outcome, name)
            break
    if not records:
        raise ValueError(f"{log}: no case outcomes")
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    output = parser.add_mutually_exclusive_group()
    output.add_argument("--list", action="store_true", help="print all discovered cases as TSV")
    output.add_argument("--paths", action="store_true", help="print absolute P4 paths for --batch-cases")
    parser.add_argument("--root", type=Path, default=DEFAULT_ROOT, help="repository root")
    parser.add_argument(
        "--manifest", type=Path, default=Path(__file__).with_name("typecheck-cases.tsv"),
        help="check that the proof corpus is drawn from these suites",
    )
    args = parser.parse_args()
    root = args.root.resolve()

    cases = {}
    for name, expectation in SUITES:
        for source, record in read_suite(root, name, expectation).items():
            if source in cases:
                raise ValueError(f"duplicate across suites: {source}")
            cases[source] = record

    # The boot logs cover the same p4c files and provide another recorded
    # Program_ok-status check. Failure logs alone are not proof of rejection.
    for name, expectation in BOOT_SUITES:
        for source, (_, outcome, _) in read_suite(root, name, expectation).items():
            if source not in cases or cases[source][:2] != (expectation, outcome):
                raise ValueError(f"run/boot status disagreement: {source}")

    selected = set()
    for number, line in enumerate(args.manifest.read_text().splitlines(), 1):
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) not in (2, 3):
            raise ValueError(f"{args.manifest}:{number}: invalid manifest entry")
        status, source_name = fields[:2]
        source = Path(os.path.abspath(args.manifest.parent / source_name))
        if source not in cases:
            raise ValueError(f"{args.manifest}:{number}: source absent from SL suite: {source}")
        recorded, outcome, _ = cases[source]
        if outcome != "excluded" and status != recorded and not (
            status == "abort-reject" and recorded == "reject"
        ):
            raise ValueError(f"{args.manifest}:{number}: unexpected status for {source}")
        if source in selected:
            raise ValueError(f"{args.manifest}:{number}: duplicate source {source}")
        selected.add(source)

    counts = Counter((expectation, outcome) for expectation, outcome, _ in cases.values())
    boot_unknown = sum(
        line.startswith("Error on run: ") and line.endswith(" (unknown)")
        for name, _ in BOOT_SUITES
        for line in (root / name).read_text().splitlines()
    )
    if args.paths:
        for source in sorted(cases):
            print(source)
    elif args.list:
        print("expected\tlog_result\tsource\tsuite")
        for source, (expectation, outcome, suite) in sorted(cases.items()):
            print(f"{expectation}\t{outcome}\t{source.relative_to(root)}\t{suite}")
    else:
        print(
            f"SL cases: {len(cases)}; expected accept: {counts['accept', 'pass']}; "
            f"expected reject: {counts['reject', 'fail']}; "
            f"excluded: {counts['accept', 'excluded'] + counts['reject', 'excluded']}; "
            f"boot unknown errors: {boot_unknown}; proof corpus selected: {len(selected)}"
        )


if __name__ == "__main__":
    main()

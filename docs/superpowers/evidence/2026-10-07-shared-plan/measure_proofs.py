#!/usr/bin/env python3
"""Compile the unchanged case goals and available proofs; count their cost separately.

Run after the complete generated module build. The output directory must be new.
The source directory contains the case/audit files beside this script. Optional
SpecTecProof support is copied from the implementation, without modifying it.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated", type=Path, required=True)
    parser.add_argument("--support", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--cpus", default="4,5")
    parser.add_argument("--modules", nargs="+", default=[
        "SpecTecProof", "RandomCases", "AxiomAudit", "Case0454", "Case0487", "CaseAxioms"])
    args = parser.parse_args()
    cpus = [int(value) for value in args.cpus.split(",")]
    if not cpus or not set(cpus) <= os.sched_getaffinity(0):
        parser.error("--cpus must select available CPUs")
    root = args.output.resolve()
    root.mkdir(parents=True, exist_ok=False)
    for module in args.modules:
        source = args.support if module == "SpecTecProof" else Path(__file__).with_name(module + ".lean")
        (root / (module + ".lean")).write_bytes(source.read_bytes())
    compiler = str(Path(args.lean).resolve())
    result = dict(compiler=compiler, cpus=cpus, lean_jobs=2,
                  generated=str(args.generated.resolve()), records=[])
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(args.generated.resolve()), str(root)]))
    for module in args.modules:
        source = root / (module + ".lean")
        output = source.with_suffix(".olean")
        started = time.monotonic()
        with source.with_suffix(".log").open("w") as stream:
            child = subprocess.Popen(
                [compiler, "-j", "2", "-o", str(output), str(source)],
                cwd=root, env=env, stdout=stream, stderr=stream,
                preexec_fn=lambda: os.sched_setaffinity(0, cpus))
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
        record = dict(module=module, exit=child.returncode,
                      wall_s=time.monotonic() - started,
                      user_s=usage.ru_utime, system_s=usage.ru_stime,
                      peak_rss_kib=usage.ru_maxrss,
                      source_bytes=source.stat().st_size,
                      source_lines=len(source.read_text().splitlines()),
                      source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                      olean_bytes=output.stat().st_size if child.returncode == 0 else None)
        result["records"].append(record)
        (root / "proof-measurements.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(record), flush=True)
        if child.returncode:
            return child.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

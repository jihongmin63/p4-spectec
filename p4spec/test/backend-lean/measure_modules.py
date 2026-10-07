#!/usr/bin/env python3
"""Measure every emitted Lean module in dependency order, without a build cache.

Clean runs reject existing oleans. Incremental runs use source/import mtimes;
use the same sources, Lean toolchain, CPU set and flags as the preceding run.
The report records reuse separately from compilation. RSS is the maximum of
the individual serial Lean processes, not their sum or the Python driver RSS.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--mode", choices=("clean", "incremental"), default="clean")
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--cpus", default="0,1")
    parser.add_argument("--lean", required=True,
                        help="installed compiler binary; bypass updating toolchain shims")
    args = parser.parse_args()
    root = args.directory.resolve()
    cpus = [int(value) for value in args.cpus.split(",")]
    if not cpus or not set(cpus) <= os.sched_getaffinity(0):
        parser.error("--cpus must select available CPUs")
    sources = {p.stem: p for p in root.glob("*.lean")}
    if not sources:
        parser.error("directory contains no Lean modules")
    if args.mode == "clean" and list(root.glob("*.olean")):
        parser.error("clean measurement requires no generated oleans")
    deps = {
        name: [dep for dep in re.findall(r"^import (\w+)", p.read_text(), re.M)
               if dep in sources]
        for name, p in sources.items()
    }
    order, active, visited = [], set(), set()

    def visit(name):
        if name in active:
            raise ValueError("import cycle: " + name)
        if name in visited:
            return
        active.add(name)
        for dep in deps[name]:
            visit(dep)
        active.remove(name)
        visited.add(name)
        order.append(name)

    for name in sorted(sources):
        visit(name)
    toolchain = subprocess.run([args.lean, "--version"], check=True,
                               capture_output=True, text=True).stdout.strip()
    manifest = {name: hashlib.sha256(p.read_bytes()).hexdigest()
                for name, p in sorted(sources.items())}
    env = dict(os.environ, LEAN_PATH=str(root))
    records = []
    started = time.monotonic()
    result = dict(mode=args.mode, toolchain=toolchain, cpus=cpus, lean_jobs=2,
                  compiler=str(Path(args.lean).resolve()),
                  total_modules=len(sources), source_sha256=manifest, records=records)

    def save():
        result.update(wall_s=time.monotonic() - started,
                      completed_modules=len(records),
                      fresh_modules=sum(not r["reused"] for r in records),
                      reused_modules=sum(r["reused"] for r in records))
        args.report.write_text(json.dumps(result, indent=2) + "\n")

    for name in order:
        source = sources[name]
        output = source.with_suffix(".olean")
        prerequisites = [source] + [sources[d].with_suffix(".olean") for d in deps[name]]
        reused = (args.mode == "incremental" and output.exists()
                  and all(p.exists() and output.stat().st_mtime_ns > p.stat().st_mtime_ns
                          for p in prerequisites))
        if reused:
            records.append(dict(module=name, reused=True, olean_bytes=output.stat().st_size))
            continue
        started_module = time.monotonic()
        log = source.with_suffix(".build.log")
        with log.open("w") as stream:
            child = subprocess.Popen(
                [args.lean, "-j", "2", "-o", str(output), str(source)],
                cwd=root, env=env, stdout=stream, stderr=stream,
                preexec_fn=lambda: os.sched_setaffinity(0, cpus))
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
        record = dict(module=name, reused=False, exit=child.returncode,
                      wall_s=time.monotonic() - started_module,
                      user_s=usage.ru_utime, system_s=usage.ru_stime,
                      peak_rss_kib=usage.ru_maxrss,
                      source_bytes=source.stat().st_size,
                      source_lines=len(source.read_text().splitlines()),
                      olean_bytes=output.stat().st_size if child.returncode == 0 else None)
        records.append(record)
        save()
        print(name, child.returncode, round(record["wall_s"], 3), usage.ru_maxrss, flush=True)
        if child.returncode:
            print(log.read_text()[-5000:], flush=True)
            return child.returncode
    result.update(
        generated_bytes=sum(p.stat().st_size for p in sources.values()),
        generated_lines=sum(len(p.read_text().splitlines()) for p in sources.values()),
        olean_bytes=sum(p.with_suffix(".olean").stat().st_size for p in sources.values()),
        user_s=sum(r.get("user_s", 0) for r in records),
        system_s=sum(r.get("system_s", 0) for r in records),
        peak_rss_kib=max((r.get("peak_rss_kib", 0) for r in records), default=0))
    save()
    print("DONE", args.report, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

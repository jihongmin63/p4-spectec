#!/usr/bin/env python3
"""Compare all emitted sources, public relation signatures and evaluator coverage.

This checks source/API coverage, not semantic equivalence or Lean compilation.
Run measure_modules.py separately and inspect the shared plan proof tests.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re


def inspect(root):
    files = sorted(root.glob("*.lean"))
    assert files, f"no Lean sources in {root}"
    text = "\n".join(p.read_text() for p in files)
    assert not re.search(r"\b(sorry|admit|sorryAx)\b", text)
    assert not re.search(r"^\s*axiom\b", text, re.M)
    names = set(re.findall(r"^def (\S+)\.fails\b", text, re.M))
    definitions = dict(re.findall(r"^def (\S+)([^\n]*)", text, re.M))
    signatures = {name: definitions[name].split(":=", 1)[0].strip() for name in names}
    evaluators = set(re.findall(r"^def (\S+)\.evalSucceeds\b", text, re.M))
    inversion = set(re.findall(r"^theorem (\S+)\.ruleCases\b", text, re.M))
    groups = defaultdict(lambda: dict(modules=0, lines=0, bytes=0))
    for p in files:
        group = ("core_support" if p.stem in ("SpecTecCore", "SpecTecSupport") else
                 "inversion" if p.stem.startswith("SpecTecInversion") else
                 "evaluator_files" if p.stem.startswith("SpecTecEval") else
                 "scc_files" if p.stem.startswith(("SpecTecScc", "SpecTecPart")) else
                 "entrypoints")
        groups[group]["modules"] += 1
        groups[group]["lines"] += len(p.read_text().splitlines())
        groups[group]["bytes"] += p.stat().st_size
    report = dict(groups=dict(groups), modules=len(files),
                  lines=sum(p["lines"] for p in groups.values()),
                  bytes=sum(p["bytes"] for p in groups.values()),
                  relations=len(names), evaluators=len(evaluators), inversions=len(inversion),
                  source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    return report, signatures, evaluators, inversion, text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    before = inspect(args.baseline)
    after = inspect(args.candidate)
    for i, label in enumerate(("signatures", "evaluators", "inversions"), start=1):
        assert before[i] == after[i], f"public {label} changed"
    assert not re.search(r"^(?:def|abbrev) .*:eval:rule:", after[4], re.M)
    assert "RuleCasesShape" not in after[4]
    result = dict(baseline=before[0], candidate=after[0], public_api_equal=True,
                  proof_holes=False, axiom_declarations=False,
                  separate_rule_evaluators=False)
    args.report.write_text(json.dumps(result, indent=2) + "\n")
    for name in ("baseline", "candidate"):
        print(name, {k: v for k, v in result[name].items()
                     if k not in ("groups", "source_sha256")})
    print("public signatures and coverage match; no proof holes or new axioms")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Type-check actual P4 extern rules without the unrelated full WFS program."""

import argparse
import re
import subprocess
import sys


NAMES = (
    "ExternFunctionCall_eval_lctk",
    "«$init_objectState»",
    "«$init_archState»",
    "ExternFunctionCall_eval",
    "ExternMethodCall_eval",
)


def extract(pattern: str, source: str) -> str:
    found = re.search(pattern, source, re.M | re.S)
    if found is None:
        raise RuntimeError(f"missing generated extern section: {pattern}")
    return found.group()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", required=True)
    parser.add_argument("--spec", required=True)
    args = parser.parse_args()
    result = subprocess.run(
        [args.exe, "--keep-going", args.spec], capture_output=True, text=True,
        check=False,
    )
    source = result.stdout
    assert source, result.stderr
    prefix, atom_tail = source.split("inductive Atom : Type 1 where\n", 1)
    atom_body, program_tail = atom_tail.split(
        "\n\ninductive InProgram : SpecTecWFS.Rule Atom → Prop where\n", 1
    )
    program_body = program_tail.split("\n\n", 1)[0]

    atoms = [
        line for line in atom_body.splitlines()
        if any(line.startswith(f"  | {name} ") for name in NAMES)
        or line.startswith("  | relation_call ")
    ]
    rules = [
        line for line in program_body.splitlines()
        if any(f"head := (@Atom.{name} " in line for name in NAMES)
        or line.startswith("  | external_call ")
    ]
    assert len(atoms) == len(NAMES) + 1, len(atoms)
    assert len(rules) == len(NAMES) + 1, len(rules)

    pieces = [
        prefix,
        "inductive Atom : Type 1 where\n" + "\n".join(atoms),
        "inductive InProgram : SpecTecWFS.Rule Atom → Prop where\n"
        + "\n".join(rules),
    ]
    for name in NAMES:
        pieces.append(extract(rf"^def {re.escape(name)}(?=\s|\().*?(?=\n\n)", source))
    for name in NAMES:
        pieces.append(extract(
            rf"^namespace {re.escape(name)}\n.*?^end {re.escape(name)}$", source
        ))
    sys.stdout.write("\n\n".join(pieces) + "\n\nend SpecTec\n")


if __name__ == "__main__":
    main()

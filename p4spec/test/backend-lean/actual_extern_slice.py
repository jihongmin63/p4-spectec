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
    atom_start = re.search(r"^inductive (?:Atom :|«Atom:)", source, re.M)
    assert atom_start is not None
    prefix, atom_tail = source[:atom_start.start()], source[atom_start.start():]
    program_start = re.search(r"^inductive (?:InProgram :|«InProgram:)", atom_tail, re.M)
    assert program_start is not None
    atom_body = atom_tail[:program_start.start()]
    program_body = atom_tail[program_start.start():].split("\n\ndef ", 1)[0]

    atoms = [
        re.sub(r" → «Atom:[^»]+»$", " → Atom", line)
        for line in atom_body.splitlines()
        if any(line.startswith(f"  | {name} ") for name in NAMES)
        or line.startswith("  | relation_call ")
    ]
    rules = [
        re.sub(r" : «InProgram:[^»]+» ", " : InProgram ", line)
        for line in program_body.splitlines()
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
        'macro "cases_in_program" h:Lean.Parser.Tactic.elimTarget : tactic =>\n'
        '  `(tactic| cases $h)',
    ]
    for name in NAMES:
        pieces.append(extract(rf"^def {re.escape(name)}(?=\s|\().*?(?=\n\n)", source))
    for name in NAMES:
        theorems = re.findall(
            rf"^theorem {re.escape(name)}\..*?(?=\n\n)", source, re.M | re.S
        )
        assert theorems, name
        pieces.extend(theorems)
    sys.stdout.write("\n\n".join(pieces) + "\n\nend SpecTec\n")


if __name__ == "__main__":
    main()

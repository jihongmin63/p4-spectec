#!/usr/bin/env python3
"""Check that every source extern in spec and spec-meta/common is emitted."""

import argparse
import pathlib
import re
import subprocess


EXPECTED = {
    "syntax": {"json", "archState", "objectState"},
    "dec": {"init_archState", "init_objectState"},
    "relation": {
        "Call_extern_func", "Call_builtin_func", "Call_extern_rel",
        "ExternFunctionCall_eval_lctk", "ExternFunctionCall_eval",
        "ExternMethodCall_eval",
    },
}
SOURCE = re.compile(r"^extern (syntax|dec|relation) \$?([A-Za-z_][A-Za-z_0-9]*)", re.M)


def declarations(root: pathlib.Path) -> dict[str, set[str]]:
    found = {kind: set() for kind in EXPECTED}
    for path in root.rglob("*.watsup"):
        for kind, name in SOURCE.findall(path.read_text()):
            found[kind].add(name)
    return found


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", required=True)
    parser.add_argument("--spec", type=pathlib.Path, required=True)
    parser.add_argument("--meta", type=pathlib.Path, required=True)
    args = parser.parse_args()

    actual = {kind: set() for kind in EXPECTED}
    for root in (args.spec, args.meta):
        source = declarations(root)
        for kind, names in source.items():
            actual[kind].update(names)
    assert actual == EXPECTED, f"source extern inventory changed: {actual!r}"

    for root in (args.spec, args.meta):
        translated = subprocess.run(
            [args.exe, "--fresh-exact-counter", "--keep-going", str(root)],
            capture_output=True, text=True,
            check=False,
        )
        assert "external type declaration" not in translated.stderr
        assert "external function declaration" not in translated.stderr
        assert "external relation declaration" not in translated.stderr
        assert "unknown external" not in translated.stderr
        for kind, names in declarations(root).items():
            for name in names:
                printed = f"«${name}»" if kind == "dec" else name
                marker = "abbrev" if kind == "syntax" else "def"
                assert re.search(rf"^{marker} {re.escape(printed)}(?=\s|\()", translated.stdout, re.M), (
                    f"{root}: {kind} {name} not emitted"
                )
    print("all 11 source extern declarations emitted")


if __name__ == "__main__":
    main()

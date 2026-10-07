#!/usr/bin/env python3
"""Check that the default Lean semantics is relation/SCC local."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, required=True)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--legacy-proof", type=Path, required=True)
    args = parser.parse_args()

    generated = subprocess.run(
        [str(args.exe.resolve()), str(args.source)],
        capture_output=True,
        text=True,
    )
    assert generated.returncode == 0, generated.stdout + generated.stderr
    lean = generated.stdout

    scopes = []
    root_semantics = []
    for line in lean.splitlines():
        if line.startswith("namespace "):
            scopes.append(line.removeprefix("namespace ").strip())
        elif line == "end" or line.startswith("end "):
            if scopes:
                scopes.pop()
        elif re.match(r"^(?:inductive|abbrev) (?:Atom|InProgram)\b", line):
            if scopes == ["SpecTec"]:
                root_semantics.append(line)
    assert not root_semantics, \
        f"default output still exposes program-wide semantics: {root_semantics}"
    assert "namespace «Decl_ok:Semantics»" in lean
    assert "namespace «CycleA:Semantics»" in lean
    assert "namespace «$invoke:Semantics»" in lean
    assert "def Decl_ok" in lean
    assert "theorem Decl_ok.checkedSuccess" in lean
    assert "theorem Decl_ok.ruleCases" in lean
    assert "def Decl_ok.fails" in lean
    assert "def CycleA.undetermined" in lean
    assert "def Nat_ok.undetermined" not in lean
    assert ('relations := ["CycleA", "CycleB"], dependencies := [], '
            'recursive := true, negativeCycle := true') in lean
    decl_component = lean.split("namespace «Decl_ok:Semantics»", 1)[1].split(
        "end «Decl_ok:Semantics»", 1
    )[0]
    assert "def rule_0_plan" in decl_component
    assert "SpecTecPlan.ProgramOf Allowed ()" in decl_component
    invoke_component = lean.split("namespace «$invoke:Semantics»", 1)[1].split(
        "end «$invoke:Semantics»", 1
    )[0]
    assert "SpecTecPlan.Plan.bindCall" in invoke_component
    assert "SpecTecPlan.Plan.bindExternal" in lean
    assert "SpecTecExternTypes" not in decl_component, \
        "an unused extern type polluted the Decl_ok component"
    assert "abbrev json" in lean, "the extern type interface disappeared"

    rooted = subprocess.run(
        [str(args.exe.resolve()), "--relation-root", "Decl_ok", str(args.source)],
        capture_output=True,
        text=True,
    )
    assert rooted.returncode == 0, rooted.stdout + rooted.stderr
    assert "namespace «Decl_ok:Semantics»" in rooted.stdout
    assert "namespace «CycleA:Semantics»" not in rooted.stdout
    assert "def CycleA" not in rooted.stdout

    with tempfile.TemporaryDirectory(prefix="p4-relation-local-") as directory:
        directory = Path(directory)
        target = directory / "RelationLocal.lean"
        target.write_text(lean + "\n" + args.proof.read_text())
        checked = subprocess.run(
            ["lean", "-j", "2", str(target)], capture_output=True, text=True
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr
        assert "'SpecTecPlan.Program.compiled_iff' depends on axioms:" in checked.stdout
        assert "'SpecTecPlan.Program.holds_cases' depends on axioms:" in checked.stdout
        assert "sorryAx" not in checked.stdout

        premature = directory / "PrematurePlanValue.lean"
        premature.write_text(lean + """
namespace SpecTecPrematureValue
inductive Atom where | result : Nat → Atom
def bad : SpecTecPlan.Plan Atom Nat :=
  .guard (fun input => input.2 = 0)
    (.ret (fun input => Atom.result input))
end SpecTecPrematureValue
""")
        invalid = subprocess.run(
            ["lean", str(premature)], capture_output=True, text=True
        )
        assert invalid.returncode != 0, "a future call result was used before binding"
        assert "Invalid projection" in invalid.stdout + invalid.stderr

        rooted_target = directory / "RelationRooted.lean"
        rooted_target.write_text(rooted.stdout)
        rooted_checked = subprocess.run(
            ["lean", "-j", "2", str(rooted_target)],
            capture_output=True,
            text=True,
        )
        assert rooted_checked.returncode == 0, \
            rooted_checked.stdout + rooted_checked.stderr

        legacy_command = [
            str(args.exe.resolve()), "--fresh-exact-counter", str(args.source)
        ]
        legacy = subprocess.run(legacy_command, capture_output=True, text=True)
        repeated = subprocess.run(legacy_command, capture_output=True, text=True)
        assert legacy.returncode == 0, legacy.stdout + legacy.stderr
        assert repeated.returncode == 0, repeated.stdout + repeated.stderr
        assert legacy.stdout == repeated.stdout, "legacy exact mode is not reproducible"
        assert re.search(r"^inductive Atom\b", legacy.stdout, re.MULTILINE)
        assert re.search(r"^inductive InProgram\b", legacy.stdout, re.MULTILINE)
        legacy_target = directory / "RelationLocalLegacy.lean"
        legacy_target.write_text(
            legacy.stdout + "\n" + args.legacy_proof.read_text()
        )
        legacy_checked = subprocess.run(
            ["lean", "-j", "2", str(legacy_target)], capture_output=True, text=True
        )
        assert legacy_checked.returncode == 0, \
            legacy_checked.stdout + legacy_checked.stderr

        wide_source = directory / "WideMembership.watsup"
        wide_source.write_text("relation Big: |- nat\n  hint(input %0)\n"
            + "".join(f"rule Big/case{index}:\n  |- {index}\n"
                      for index in range(40)))
        wide = subprocess.run(
            [str(args.exe.resolve()), str(wide_source)],
            capture_output=True, text=True,
        )
        assert wide.returncode == 0, wide.stdout + wide.stderr
        assert "inductive «Allowed:0:0»" in wide.stdout
        assert "abbrev InProgram.rule_39" in wide.stdout
        assert 'macro "cases_allowed_0"' in wide.stdout
        wide_target = directory / "WideMembership.lean"
        wide_target.write_text(wide.stdout + """
namespace SpecTec
example (proof : Big 0) : True := by
  obtain ⟨rule, member, head, side, positive, negative⟩ :=
    SpecTecWFS.Holds.cases proof
  rcases member with ⟨alternative, member, witness, rfl⟩
  cases_allowed_0 member
  all_goals trivial
end SpecTec
""")
        wide_checked = subprocess.run(
            ["lean", "-j", "2", str(wide_target)],
            capture_output=True, text=True,
        )
        assert wide_checked.returncode == 0, \
            wide_checked.stdout + wide_checked.stderr

        extern_wide_source = directory / "ExternWideMembership.watsup"
        extern_wide_source.write_text(
            "extern syntax json\n"
            "syntax externalBox = EXTERNAL json\n"
            "var box : externalBox\n"
            "relation Big: externalBox |- nat\n  hint(input %0)\n"
            + "".join(f"rule Big/case{index}:\n  box |- {index}\n"
                      for index in range(40)))
        extern_wide = subprocess.run(
            [str(args.exe.resolve()), str(extern_wide_source)],
            capture_output=True, text=True,
        )
        assert extern_wide.returncode == 0, \
            extern_wide.stdout + extern_wide.stderr
        assert "SpecTecPlan.Cases" in extern_wide.stdout
        extern_wide_target = directory / "ExternWideMembership.lean"
        extern_wide_target.write_text(extern_wide.stdout)
        extern_wide_checked = subprocess.run(
            ["lean", "-j", "2", str(extern_wide_target)],
            capture_output=True, text=True,
        )
        assert extern_wide_checked.returncode == 0, \
            extern_wide_checked.stdout + extern_wide_checked.stderr

        modules = directory / "modules"
        emitted = subprocess.run(
            [str(args.exe.resolve()), "--emit-modules", str(modules),
             str(args.source)], capture_output=True, text=True
        )
        assert emitted.returncode == 0, emitted.stdout + emitted.stderr
        assert (modules / "SpecTecCore.lean").exists()
        assert (modules / "SpecTecSupport.lean").exists()
        assert (modules / "SpecTecAll.lean").exists()
        assert (modules / "SpecTecProofs.lean").exists()
        assert list(modules.glob("SpecTecInversion*.lean"))
        assert list(modules.glob("SpecTecScc*.lean"))
        assert list(modules.glob("SpecTecEval*.lean"))
        final_semantics = sorted(modules.glob("SpecTecScc*.lean"))[-1].stem
        first_inversion = sorted(modules.glob("SpecTecInversion*.lean"))[0]
        assert first_inversion.read_text().startswith(
            f"import {final_semantics}\n"), \
            "inversion proofs unnecessarily import all evaluators"
        module_files = {path.stem: path for path in modules.glob("*.lean")}
        imports = {
            name: re.findall(r"^import (\w+)$", path.read_text(), re.MULTILINE)
            for name, path in module_files.items()
        }
        assert all(dependency in module_files for dependencies in imports.values()
                   for dependency in dependencies)
        visited = set()
        active = set()
        module_order = []

        def visit(name):
            assert name not in active, f"cyclic generated import: {name}"
            if name in visited:
                return
            active.add(name)
            for dependency in imports[name]:
                visit(dependency)
            active.remove(name)
            visited.add(name)
            module_order.append(name)

        for name in module_files:
            visit(name)
        repeated_modules = directory / "repeated_modules"
        repeated = subprocess.run(
            [str(args.exe.resolve()), "--emit-modules", str(repeated_modules),
             str(args.source)], capture_output=True, text=True
        )
        assert repeated.returncode == 0, repeated.stdout + repeated.stderr
        assert {name: path.read_bytes() for name, path in module_files.items()} == {
            path.stem: path.read_bytes() for path in repeated_modules.glob("*.lean")
        }, "module output changed across identical runs"
        module_env = dict(os.environ, LEAN_PATH=str(modules))
        for name in module_order:
            checked_module = subprocess.run(
                ["lean", "-j", "2", "-o", f"{name}.olean", f"{name}.lean"],
                cwd=modules, env=module_env, capture_output=True, text=True
            )
            assert checked_module.returncode == 0, \
                f"{name}: {checked_module.stdout}{checked_module.stderr}"

        forced = directory / "split_modules"
        split = subprocess.run(
            [str(args.exe.resolve()), "--module-split-bytes", "10000",
             "--emit-modules", str(forced), str(args.source)],
            capture_output=True, text=True,
        )
        assert split.returncode == 0, split.stdout + split.stderr
        assert list(forced.glob("SpecTecPart*.lean")), \
            "forced byte limit did not split an SCC internally"
        forced_files = {path.stem: path for path in forced.glob("*.lean")}
        forced_order = []
        visited = set()
        active = set()

        def visit_forced(name):
            assert name not in active, f"cyclic forced import: {name}"
            if name in visited:
                return
            active.add(name)
            for dependency in re.findall(
                    r"^import (\w+)$", forced_files[name].read_text(),
                    re.MULTILINE):
                assert dependency in forced_files
                visit_forced(dependency)
            active.remove(name)
            visited.add(name)
            forced_order.append(name)

        for name in forced_files:
            visit_forced(name)
        forced_env = dict(os.environ, LEAN_PATH=str(forced))
        for name in forced_order:
            checked_module = subprocess.run(
                ["lean", "-j", "2", "-o", f"{name}.olean", f"{name}.lean"],
                cwd=forced, env=forced_env, capture_output=True, text=True,
            )
            assert checked_module.returncode == 0, \
                f"{name}: {checked_module.stdout}{checked_module.stderr}"

    print("relation local: SCC-local and explicit legacy judgements checked")


if __name__ == "__main__":
    main()

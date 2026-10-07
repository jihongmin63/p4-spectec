#!/usr/bin/env python3
"""Compile split rule membership with positive, negative and extern proofs."""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def check_recursive_groups(exe, temp):
    path = Path(temp) / 'recursive.watsup'
    path.write_text('relation Deep: |- nat\n  hint(input %0)\n' + '\n'.join(
        f'rule Deep/r{i}: |- {i}' for i in range(4097)))
    generated = subprocess.run([str(exe.resolve()), '--fresh-exact-counter', str(path)], capture_output=True,
                               text=True, check=True).stdout
    lean = Path(temp) / 'recursive.lean'
    lean.write_text(generated + """
namespace SpecTec
set_option maxHeartbeats 0
example : Deep 4096 := Deep.r4096
example (h : InProgram {head := Atom.Deep 4096, positive := [], negative := [], side := True}) : True := by
  cases_in_program h <;> trivial
end SpecTec
""")
    result = subprocess.run(['lean', '-j', '2', str(lean)], capture_output=True,
                            text=True, timeout=120)
    assert result.returncode == 0, result.stdout + result.stderr
    assert 'sorry' not in result.stdout, result.stdout
    print('recursive groups: boundary rule and two-level elimination passed')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--exe', required=True, type=Path)
    parser.add_argument('--fixtures', default='.', type=Path)
    args = parser.parse_args()
    padding = 'relation Padding: |- nat\n  hint(input %0)\n' + '\n'.join(
        f'rule Padding/r{i}: |- {i}' for i in range(129))
    with tempfile.TemporaryDirectory() as temp:
        for name in ('relation-wfs', 'decidable-eq', 'print', 'fresh-regression',
                     'prefix-regression', 'extern-model', 'extern-static'):
            path = Path(temp) / f'{name}.watsup'
            base = 'extern-model' if name.startswith('extern-') else name
            specification = (args.fixtures / f'{base}.watsup').read_text()
            if name in ('extern-static'):
                specification = specification.split('extern dec $init_archState')[0] + '''
extern relation ExternFunctionCall_eval_lctk:
  typingContext |- nameIR `( nameIR* `) ~> value
  hint(input %0 %1 %2)
'''
            if name.startswith('extern-'):
                specification += '''
builtin dec $print_<X>(X) : text
dec $polyIdentity<X>(X) : X
def $polyIdentity<X>(X) = X
dec $polyEqual<X>(X, X) : bool
def $polyEqual<X>(X_a, X_b) = (X_a = X_b)
dec $polyPrint<X>(X) : text
def $polyPrint<X>(X) = $print_<X>(X)
'''
            path.write_text(specification + '\n' + padding)
            generated = subprocess.run([str(args.exe.resolve()), '--fresh-exact-counter', str(path)],
                                       capture_output=True, text=True, check=True).stdout
            widths = [len(re.findall(r'^  \| ', body, re.M)) for body in re.findall(
                r'^inductive (?:InProgram|«InProgram:[^»]+»)[^\n]*\n(.*?)(?=\n\n)',
                generated, re.M | re.S)]
            # Bound the source of superlinear Lean inductive elaboration.
            assert widths and max(widths) <= 32, (name, widths)
            proof = ((args.fixtures / f'{name}-proof.lean').read_text()
                     if name not in ('extern-static') else '')
            proof = proof.replace('cases inProgram', 'cases_in_program inProgram')
            # This fixture exhausts its original atoms; Padding is a new atom.
            if name == 'extern-model':
                proof = proof.replace('  | .relation_call _ _ _ => True',
                                      '  | .relation_call _ _ _ => True\n  | _ => True')
            extra = '''
namespace SpecTec
EXTERN_VARIABLE
example : Padding 0 := Padding.r0
example : Padding 128 := Padding.r128
example : ¬ Padding 129 := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases_in_program inProgram <;> simp_all [SpecTecWFS.All]
end SpecTec
'''.replace('EXTERN_VARIABLE', 'variable [SpecTecExternTypes] [SpecTecP4ExternModel]'
            if 'class SpecTecExternTypes' in generated else '')
            lean = Path(temp) / f'{name}.lean'
            lean.write_text(generated + '\n' + proof + extra)
            result = subprocess.run(['lean', '-j', '2', str(lean)], capture_output=True,
                                    text=True, timeout=120)
            assert result.returncode == 0, result.stdout + result.stderr
            assert 'sorry' not in result.stdout, result.stdout
            print(f'{name}: split rules and proofs passed (max width {max(widths)})')
        check_recursive_groups(args.exe, temp)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Check bounded Atom compilation and existing proofs across group boundaries."""
import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--exe', required=True, type=Path)
    parser.add_argument('--fixtures', default='.', type=Path)
    args = parser.parse_args()
    # These exercise recursion, negation, generic equality/printers, fresh state,
    # higher-order dispatch and extern type parameters with the split enabled.
    fixtures = ('relation-wfs', 'decidable-eq', 'print', 'prefix-regression', 'extern-model',
                'recursive-groups')
    padding = '\n'.join(
        f'relation Padding{i}: |- nat\n  hint(input %0)'
        for i in range(129)
    )
    with tempfile.TemporaryDirectory() as temp:
        for name in fixtures:
            source = Path(temp) / f'{name}.watsup'
            if name == 'recursive-groups':
                # 126 polymorphic constructors + relation_call leave one root
                # slot, forcing the monomorphic leaves through another level.
                specification = '\n'.join(
                    f'dec $generic{i}<X>(X) : X\ndef $generic{i}<X>(X) = X'
                    for i in range(126)
                ) + '\nrelation Marker: MARKER\n'
            else:
                specification = (args.fixtures / f'{name}.watsup').read_text()
            source.write_text(specification + '\n' + padding)
            generated = subprocess.run(
                [str(args.exe.resolve()), str(source)], check=True, capture_output=True, text=True
            ).stdout
            # A constructor-width budget catches the superlinear Lean auxiliary
            # generation even on machines where an elapsed-time test is noisy.
            widths = [len(re.findall(r'^  \| ', body, re.M)) for body in re.findall(
                r'^inductive (?:Atom|«Atom:[^»]+»)[^\n]*\n(.*?)(?=\n\n)', generated, re.M | re.S
            )]
            assert widths and max(widths) <= 128, (name, widths)
            # Keep the compatibility root broad enough for polymorphic fields,
            # but cap internal groups more tightly to bound auxiliary generation.
            internal_widths = [len(re.findall(r'^  \| ', body, re.M)) for body in re.findall(
                r'^inductive «Atom:[^»]+»[^\n]*\n(.*?)(?=\n\n)', generated, re.M | re.S
            )]
            assert internal_widths and max(internal_widths) <= 32, (name, internal_widths)
            if name == 'recursive-groups':
                proof = '''
namespace SpecTec
-- Existential type fields remain accessible in constructor patterns.
def genericType : Atom → Type
  | @Atom.«$generic0» X _ _ => X
  | _ => Unit
example : genericType (Atom.«$generic0» (3 : Nat) 3) = Nat := rfl
example : «$generic0» (3 : Nat) 3 := «$generic0».case_1 _
def isMarker : Atom → Bool
  | .Marker => true
  | _ => false
example : isMarker Atom.Marker = true := rfl
example : isMarker (Atom.Padding0 0) = false := rfl
end SpecTec
'''
            else:
                proof = (args.fixtures / f'{name}-proof.lean').read_text()
            # The extern fixture originally exhausts all atoms. Padding adds
            # unreachable atoms, so extend that interpretation to cover them.
            if name == 'extern-model':
                proof = proof.replace('  | .relation_call _ _ _ => True',
                                      '  | .relation_call _ _ _ => True\n  | _ => False')
            generated += '\n' + proof + '''
namespace SpecTec
example (n m : Nat) (h : Atom.Padding0 n = Atom.Padding0 m) : n = m := by
  simpa using h
example (n m : Nat) : Atom.Padding0 n ≠ Atom.Padding128 m := by
  simp [Atom.Padding0, Atom.Padding128]
def paddingValue : Atom → Nat
  | .Padding0 n => n
  | .Padding128 n => n + 1
  | _ => 0
example : paddingValue (Atom.Padding0 7) = 7 := rfl
example : paddingValue (Atom.Padding128 7) = 8 := rfl
end SpecTec
'''
            if 'class SpecTecExternTypes' in generated:
                generated = generated.replace('namespace SpecTec\nexample (n m', 'namespace SpecTec\nvariable [SpecTecExternTypes]\nexample (n m')
            target = Path(temp) / f'{name}.lean'
            target.write_text(generated)
            result = subprocess.run(['lean', '-j', '2', str(target)], capture_output=True,
                                    text=True, timeout=120)
            assert result.returncode == 0, result.stdout + result.stderr
            assert 'sorry' not in result.stdout, result.stdout
            print(f'{name}: split Atom and existing proofs passed (max width {max(widths)})')


if __name__ == '__main__':
    main()

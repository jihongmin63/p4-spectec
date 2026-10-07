#!/usr/bin/env python3
"""Exercise proof automation on actual generated WFS programs, including rejection."""
import argparse
import os
from pathlib import Path
import subprocess
import tempfile


def run(command, *, env=None, ok=True, cwd=None):
    result = subprocess.run(command, capture_output=True, text=True, env=env, cwd=cwd, timeout=120)
    output = result.stdout + result.stderr
    if ok:
        assert result.returncode == 0, output
        assert 'sorryAx' not in output, output
    else:
        assert result.returncode != 0, 'invalid proof was accepted\n' + output
    return output


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--exe', required=True, type=Path)
    parser.add_argument('--support', required=True, type=Path)
    parser.add_argument('--fixtures', default='.', type=Path)
    parser.add_argument('--case', help='run one named check')
    args = parser.parse_args()
    selected = 0
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        support = root / 'SpecTecProof.lean'
        support.write_text(args.support.read_text())
        run(['lean', '-j', '2', '-o', str(root / 'SpecTecProof.olean'), str(support)], cwd=root)
        env = dict(os.environ, LEAN_PATH=str(root))

        def check(name, spec, proof, *, ok=True, error=None):
            nonlocal selected
            if args.case and args.case != name:
                return
            selected += 1
            source = root / (name + '.watsup')
            source.write_text(spec)
            translated = run([
                str(args.exe.resolve()), "--fresh-exact-counter", str(source)
            ])
            target = root / (name + '.lean')
            target.write_text('import SpecTecProof\n' + translated + '\n' + proof)
            output = run(['lean', '-j', '2', str(target)], env=env, ok=ok)
            if error:
                assert error in output, output
            print(name + ': passed')

        spec = (args.fixtures / 'relation-wfs.watsup').read_text()
        check('composition', spec, (args.fixtures / 'wfs-composition-proof.lean').read_text())
        proofs = ((args.fixtures / 'relation-wfs-proof.lean').read_text() + '\n' +
                  (args.fixtures / 'proof-support-proof.lean').read_text())
        check('wfs', spec, proofs)

        # A predicate unrelated to P4 still uses the exact same interface.
        spec = 'var n : nat\nrelation Number: |- nat\n hint(input %0)\n'
        spec += '\n'.join(f'rule Number/r{i}: |- {i}' for i in range(4097))
        proof = '''
namespace SpecTec
set_option maxHeartbeats 4000000
def bounded : Atom → Prop
  | .Number n => n < 4097
  | _ => True
spec_invariant bounded_sound for InProgram : bounded where
  default => by
    cases member <;> simp [bounded]
theorem outside : ¬ Number 4097 := by
  intro h
  have b := bounded_sound (.Number 4097) h
  simp [bounded] at b
example : Number 4096 := Number.r4096
#print axioms outside
end SpecTec
'''
        check('recursive_groups', spec, proof)

        small = 'relation Number: |- nat\n hint(input %0)\nrule Number/zero: |- 0\n'
        check('unsplit', small, proof.replace('4097', '1').replace('4096', '0').replace(
            'Number.r0', 'Number.zero'))
        check('explicit_handler', small, '''
namespace SpecTec
def isZero : Atom → Prop
  | .Number n => n = 0
  | _ => True
spec_invariant zero_sound for InProgram : isZero where
  default => by fail "the explicit handler must override this default"
  InProgram => by cases member <;> simp [isZero]
example (h : Number 7) : False := by
  have z := zero_sound (.Number 7) h
  simp [isZero] at z
end SpecTec
''')
        section_proof = '''
namespace SpecTec
section
variable (bound : Nat) (hyp : 0 ≤ bound)
include hyp
def bounded : Atom → Prop
  | .Number n => n ≤ bound
  | _ => True
spec_invariant bound_sound for InProgram : bounded bound where
  default => by
    cases member <;> first | exact hyp | trivial
example (h : Number 0) : 0 ≤ bound := bound_sound bound hyp (.Number 0) h
end
end SpecTec
'''
        check('section_parameters', small, section_proof)
        padding = 'relation Padding: |- nat\n hint(input %0)\n' + '\n'.join(
            f'rule Padding/p{i}: |- {i}' for i in range(40))
        check('section_parameters_split', small + padding, section_proof)
        # Only the first leaf can conclude Number. Every other leaf must use
        # its proved head property, rather than run the deliberately failing
        # default tactic or split all its rule constructors again.
        shortcut_spec = small + 'relation Padding: |- nat\n hint(input %0)\n'
        shortcut_spec += '\n'.join(f'rule Padding/p{i}: |- {i}' for i in range(1025))
        shortcut_proof = '''
namespace SpecTec
def isZero : Atom → Prop
  | .Number n => n = 0
  | _ => True
spec_invariant zero_sound for InProgram : isZero where
  default => by fail "unrelated leaf was expanded"
  «InProgram:0:0» => by cases member <;> simp [isZero]
example (h : Number 7) : False := by
  have z := zero_sound (.Number 7) h
  simp [isZero] at z
#print axioms zero_sound
end SpecTec
'''
        check('unrelated_heads', shortcut_spec, shortcut_proof)
        check('unrelated_heads_using', shortcut_spec,
              shortcut_proof.replace('example (h : Number 7)', '''
spec_invariant another_sound for InProgram : isZero using zero_sound where
  default => by fail "unrelated leaf was expanded with known facts"
  «InProgram:0:0» => by cases member <;> simp [isZero]
example (h : Number 7)'''))
        check('local_known_fact', (args.fixtures / 'relation-wfs.watsup').read_text(), '''
namespace SpecTec
section
variable (bound : Nat)
def knownProperty : Atom → Prop
  | .Even n => n ≤ bound
  | _ => True
variable (fact : ∀ a, SpecTecWFS.Holds InProgram a → knownProperty bound a)
def pairProperty : Atom → Prop
  | .PairEven n => n ≤ bound
  | _ => True
spec_invariant result for InProgram : pairProperty bound using fact where
  default => by cases member <;> simp_all [pairProperty, knownProperty, SpecTecWFS.All]
example (h : PairEven 0) : 0 ≤ bound := result bound fact (.PairEven 0) h
end
end SpecTec
''')
        check('invalid', small, '''
namespace SpecTec
spec_invariant bad for InProgram : (fun _ => False) where
  default => by cases member <;> exact True.intro
end SpecTec
''', ok=False, error='spec_invariant:')
        check('unused_handler', small, '''
namespace SpecTec
spec_invariant valid for InProgram : (fun _ => True) where
  default => by trivial
  Nat => by trivial
end SpecTec
''', ok=False, error='unused membership handler')

        extern = (args.fixtures / 'extern-model.watsup').read_text()
        extern += '\ndec $identity<X>(X) : X\ndef $identity<X>(X) = X\n'
        generic_heads = extern + '''
builtin dec $print_<X>(X) : text
dec $polyEqual<X>(X, X) : bool
def $polyEqual<X>(X_a, X_b) = (X_a = X_b)
dec $polyPrint<X>(X) : text
def $polyPrint<X>(X) = $print_<X>(X)
''' + '\n'.join(
            f'dec $identity{i}<X>(X) : X\ndef $identity{i}<X>(X) = X'
            for i in range(64))
        check('unrelated_polymorphic_extern_heads', generic_heads, '''
namespace SpecTec
variable [SpecTecExternTypes] [SpecTecP4ExternModel]
spec_invariant all_sound for InProgram : (fun _ => True) where
  default => by fail "polymorphic or extern leaf was expanded"
example (atom : Atom) (h : SpecTecWFS.Holds InProgram atom) : True :=
  all_sound atom h
#print axioms all_sound
end SpecTec
''')
        check('polymorphic_extern', extern, '''
namespace SpecTec
variable [SpecTecExternTypes] [SpecTecP4ExternModel]
def identityInvariant : Atom → Prop
  | .«$identity» input output => input = output
  | _ => True
spec_invariant identity_sound for InProgram : identityInvariant where
  default => by cases member <;> simp_all [identityInvariant, SpecTecWFS.All]
example {X : Type} (input output : X) (h : «$identity» input output) : input = output :=
  identity_sound (.«$identity» input output) h
#print axioms identity_sound
end SpecTec
''')
        if not selected:
            parser.error('unknown check: ' + str(args.case))


if __name__ == '__main__':
    main()

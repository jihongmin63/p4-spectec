namespace SpecTec

private def parity : Atom → Prop
  | .Even n => n % 2 = 0
  | _ => True

spec_invariant parity_sound for InProgram : parity where
  default => by
    cases member <;> simp_all [parity, SpecTecWFS.All]

private def pairParity : Atom → Prop
  | .PairEven n => n % 2 = 0
  | _ => True

spec_invariant pair_sound for InProgram : pairParity using parity_sound where
  default => by
    cases member <;> simp_all [pairParity, parity, SpecTecWFS.All]

-- Using a negative premise must expose Fails, not simply a negated Holds.
private def negativePremise : Atom → Prop
  | .A 0 => SpecTecWFS.Fails InProgram (.B 0)
  | _ => True

spec_invariant negative_sound for InProgram : negativePremise where
  default => by
    cases member <;> simp_all [negativePremise, SpecTecWFS.All]

theorem reject_odd_pair : ¬ PairEven 3 := by
  intro h
  have p := pair_sound (Atom.PairEven 3) h
  simp [pairParity] at p

#print axioms parity_sound
#print axioms pair_sound
#print axioms reject_odd_pair
#print axioms negative_sound
end SpecTec

namespace SpecTec

-- A previously verified fact is available alongside the induction hypothesis.
private def parity : Atom → Prop
  | .Even n => n % 2 = 0
  | _ => True

private theorem parity_sound (a : Atom) (h : SpecTecWFS.Holds InProgram a) : parity a := by
  apply SpecTecWFS.Holds.sound h
  intro rule member side positive negative
  cases_in_program member <;> simp_all [parity, SpecTecWFS.All]

private def pairParity : Atom → Prop
  | .PairEven n => n % 2 = 0
  | _ => True

theorem pair_parity (a : Atom) (h : SpecTecWFS.Holds InProgram a) : pairParity a := by
  apply SpecTecWFS.Holds.sound_with h parity_sound
  intro rule member side positive known negative
  cases_in_program member <;> simp_all [pairParity, parity, SpecTecWFS.All]

-- Witness elimination retains the actual positive derivations.
theorem pair_has_even (n : Nat) (h : PairEven n) : Even n := by
  obtain ⟨rule, member, head, side, positive, negative⟩ :=
    SpecTecWFS.Holds.iff_rule.mp h
  cases_in_program member <;> simp_all [SpecTecWFS.All, Even]

-- Refuting truth is deliberately different from proving WFS falsity.
theorem odd_rejected : ¬ Even 1 := by
  apply SpecTecWFS.Holds.reject
  intro rule member head side positive negative
  cases_in_program member <;> simp_all

#print axioms pair_parity
#print axioms pair_has_even
#print axioms odd_rejected
end SpecTec

namespace SpecTec

private theorem unwrap_enabled_num_fails (n : Nat) :
    SpecTecWFS.Fails InProgram (Atom.«$unwrap:enabled» (.NUM n)) := by
  intro proof
  let interpretation : Atom → Prop := fun atom =>
    match atom with
    | .«$unwrap:enabled» (.NUM _) => False
    | _ => True
  apply proof interpretation
  intro rule inProgram side positive negative
  cases inProgram <;> simp [interpretation]

private theorem even_one_fails :
    SpecTecWFS.Fails InProgram (Atom.Even 1) := by
  intro proof
  let interpretation : Atom → Prop := fun atom =>
    match atom with
    | .Even 1 => False
    | _ => True
  apply proof interpretation
  intro rule inProgram side positive negative
  cases inProgram <;> simp [interpretation]

example : ¬ Even 1 := by
  intro proof
  exact even_one_fails (SpecTecWFS.lower_le_upper InProgram _ proof)

private theorem negative_cycle_lower_absent :
    ¬ SpecTecWFS.lower InProgram (Atom.A 0) ∧
    ¬ SpecTecWFS.lower InProgram (Atom.B 0) := by
  let interpretation : Atom → Prop := fun atom =>
    match atom with
    | .A 0 | .B 0 => False
    | _ => True
  have gammaA : SpecTecWFS.gamma InProgram interpretation (Atom.A 0) :=
    SpecTecWFS.Derives.rule _ InProgram.rule_8 trivial trivial
      ⟨by simp [interpretation], trivial⟩
  have gammaB : SpecTecWFS.gamma InProgram interpretation (Atom.B 0) :=
    SpecTecWFS.Derives.rule _ InProgram.rule_9 trivial trivial
      ⟨by simp [interpretation], trivial⟩
  have closed : ∀ rule : SpecTecWFS.Rule Atom, InProgram rule → rule.side →
      SpecTecWFS.All interpretation rule.positive →
      SpecTecWFS.All (fun atom => ¬ SpecTecWFS.gamma InProgram interpretation atom)
        rule.negative → interpretation rule.head := by
    intro rule inProgram side positive negative
    cases inProgram <;> simp_all [interpretation, SpecTecWFS.All]
  have prefixed : ∀ atom, SpecTecWFS.alternating InProgram interpretation atom →
      interpretation atom := by
    intro atom proof
    exact proof interpretation closed
  constructor
  · intro proof
    exact proof interpretation prefixed
  · intro proof
    exact proof interpretation prefixed

private theorem negative_cycle_upper_A :
    SpecTecWFS.upper InProgram (Atom.A 0) :=
  SpecTecWFS.Derives.rule _ InProgram.rule_8 trivial trivial
    ⟨negative_cycle_lower_absent.2, trivial⟩

private theorem negative_cycle_upper_B :
    SpecTecWFS.upper InProgram (Atom.B 0) :=
  SpecTecWFS.Derives.rule _ InProgram.rule_9 trivial trivial
    ⟨negative_cycle_lower_absent.1, trivial⟩

example : SpecTecWFS.Undetermined InProgram (Atom.A 0) :=
  ⟨negative_cycle_upper_A, negative_cycle_lower_absent.1⟩

private theorem uncertain_enabled_upper :
    SpecTecWFS.upper InProgram (Atom.«$uncertain:enabled» (.NUM 0)) := by
  exact SpecTecWFS.Derives.rule _ InProgram.rule_11 trivial
    ⟨SpecTecWFS.Derives.rule _ InProgram.rule_10 trivial
      ⟨negative_cycle_upper_A, trivial⟩ trivial, trivial⟩ trivial

private theorem uncertain_enabled_lower_absent :
    ¬ SpecTecWFS.lower InProgram (Atom.«$uncertain:enabled» (.NUM 0)) := by
  let interpretation : Atom → Prop := fun atom =>
    match atom with
    | .A 0 | .B 0 => False
    | .«$uncertain:regular» (.NUM 0) (.NUM 1) => False
    | .«$uncertain:enabled» (.NUM 0) => False
    | _ => True
  have closed : ∀ rule : SpecTecWFS.Rule Atom, InProgram rule → rule.side →
      SpecTecWFS.All interpretation rule.positive →
      SpecTecWFS.All (fun atom => ¬ SpecTecWFS.upper InProgram atom)
        rule.negative → interpretation rule.head := by
    intro rule inProgram side positive negative
    cases inProgram <;> simp_all [interpretation, SpecTecWFS.All]
    · exact negative negative_cycle_upper_B
    · exact negative negative_cycle_upper_A
  intro proof
  have derived := SpecTecWFS.lower_postfixed InProgram _ proof
  exact derived interpretation closed

example : SpecTecWFS.Undetermined InProgram
    (Atom.«$uncertain:enabled» (.NUM 0)) :=
  ⟨uncertain_enabled_upper, uncertain_enabled_lower_absent⟩

example : ¬ SpecTecWFS.Fails InProgram
    (Atom.«$uncertain:enabled» (.NUM 0)) := by
  intro failed
  exact failed uncertain_enabled_upper

example : Even 0 := Even.zero
example : Even 4 := Even.step 2 (Even.step 0 Even.zero)
example : PairEven 4 := PairEven.both 4 (Even.step 2 (Even.step 0 Even.zero))
  (Even.step 2 (Even.step 0 Even.zero))

example : «$unwrap» (.NUM 3) (.NUM 3) := by
  exact «$unwrap».case_2 _ (unwrap_enabled_num_fails 3)

example : «$unwrap» (.WRAP (.NUM 3)) (.NUM 3) := by
  exact «$unwrap».regular _ _
    («$unwrap:regular».case_1 _ _ («$unwrap».case_2 _ (unwrap_enabled_num_fails 3)))

example : «$unwrap» (.WRAP (.WRAP (.NUM 3))) (.NUM 3) := by
  exact «$unwrap».regular _ _
    («$unwrap:regular».case_1 _ _
      («$unwrap».regular _ _
        («$unwrap:regular».case_1 _ _
          («$unwrap».case_2 _ (unwrap_enabled_num_fails 3)))))

example : «$unwrap_step» (.WRAP (.NUM 3)) (.NUM 3) := by
  exact «$unwrap_step».case_1 _ _
    («$unwrap».regular _ _
      («$unwrap:regular».case_1 _ _
          («$unwrap».case_2 _ (unwrap_enabled_num_fails 3))))

example : «$via_twice» (.NUM 3) (.NUM 3) := by
  have unwrapped : «$unwrap» (.NUM 3) (.NUM 3) :=
    «$unwrap».case_2 _ (unwrap_enabled_num_fails 3)
  have called : SpecTecWFS.Holds InProgram
      (Atom.relation_call (SpecTecRelationRef.named "$unwrap")
        (value.NUM 3) (value.NUM 3)) :=
    «$unwrap».dispatch _ _ unwrapped
  exact «$via_twice».case_1 _ _
    («$apply_twice».case_1 _ _ _ _ called called)

example : «$choose» (.NUM 2) (.NUM 3) :=
  «$choose».regular _ _ «$choose:regular».case_2

example : ¬ SpecTecWFS.Fails InProgram (Atom.«$choose:enabled» (.NUM 2)) := by
  have enabled : «$choose:enabled» (.NUM 2) :=
    «$choose:enabled».from_case_2 «$choose:regular».case_2
  exact SpecTecWFS.Holds.not_fails enabled

example : «$via_constant» (.NUM 0) := by
  exact «$via_constant».case_1 _
    («$call_constant».case_1 _ _
      («$constant».dispatch _ «$constant».case_1))

example : «$equal_or_false» (2 : Nat) 2 true := by
  exact «$equal_or_false».regular _ _ _
    («$equal_or_false:regular».case_1 _ _ rfl)

end SpecTec

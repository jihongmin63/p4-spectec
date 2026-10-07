namespace SpecTec

theorem decl_error_inversion (n : Nat)
    (proof : Decl_ok (.ERRORDECLARATION n)) : ∃ m, n = m := by
  obtain ⟨rule, member, head, side, positive, negative⟩ :=
    SpecTecWFS.Holds.cases proof
  cases member with
  | rule_0 m => simp at head
  | rule_1 m =>
      simp at head
      exact ⟨m, head.symm⟩

private theorem negative_cycle_lower_absent :
    ¬ SpecTecWFS.lower «CycleA:Semantics».InProgram
        («CycleA:Semantics».Atom.CycleA 0) ∧
    ¬ SpecTecWFS.lower «CycleA:Semantics».InProgram
        («CycleA:Semantics».Atom.CycleB 0) := by
  let interpretation : «CycleA:Semantics».Atom → Prop := fun atom =>
    match atom with
    | .CycleA 0 | .CycleB 0 => False
    | _ => True
  have gammaA : SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation
      («CycleA:Semantics».Atom.CycleA 0) :=
    SpecTecWFS.Derives.rule _ «CycleA:Semantics».InProgram.rule_0 trivial
      trivial ⟨by simp [interpretation], trivial⟩
  have gammaB : SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation
      («CycleA:Semantics».Atom.CycleB 0) :=
    SpecTecWFS.Derives.rule _ «CycleA:Semantics».InProgram.rule_1 trivial
      trivial ⟨by simp [interpretation], trivial⟩
  have closed : ∀ rule, «CycleA:Semantics».InProgram rule → rule.side →
      SpecTecWFS.All interpretation rule.positive →
      SpecTecWFS.All
        (fun atom => ¬ SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation atom)
        rule.negative → interpretation rule.head := by
    intro rule member side positive negative
    cases member <;> simp_all [interpretation, SpecTecWFS.All]
  have prefixed : ∀ atom,
      SpecTecWFS.alternating «CycleA:Semantics».InProgram interpretation atom →
      interpretation atom := by
    intro atom derived
    exact derived interpretation closed
  constructor <;> intro proof <;> exact proof interpretation prefixed

private theorem negative_cycle_upper_A :
    SpecTecWFS.upper «CycleA:Semantics».InProgram
      («CycleA:Semantics».Atom.CycleA 0) :=
  SpecTecWFS.Derives.rule _ «CycleA:Semantics».InProgram.rule_0 trivial trivial
    ⟨negative_cycle_lower_absent.2, trivial⟩

example : CycleA.undetermined 0 :=
  ⟨negative_cycle_upper_A, negative_cycle_lower_absent.1⟩

example : «$recursive» (.WRAP .ZERO) .ZERO := by
  have base : «$recursive» .ZERO .ZERO := «$recursive».case_1
  have dispatched :=
    «$invoke:Semantics».«dispatch:$recursive» .ZERO .ZERO base
  have invoked := «$invoke».case_1
    (SpecTecRelationRef.named "$recursive") .ZERO .ZERO dispatched
  have forwarded := «$forward».case_1
    (SpecTecRelationRef.named "$recursive") .ZERO .ZERO invoked
  exact «$recursive».case_2 .ZERO .ZERO forwarded

end SpecTec

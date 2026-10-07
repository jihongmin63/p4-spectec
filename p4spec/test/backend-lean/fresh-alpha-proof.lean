namespace SpecTec

private def alphaTree (name : String) : freshAlphaNode :=
  .MANY [
    .BRANCH (.LEAF name 7 true (-3)),
    .BRANCH (.MAYBE (some (.BRANCH (.BOXED (.BOX (.BRANCH (.LEAF name 9 false 2))))))),
    .BRANCH (.PAIRED (.BRANCH (.MAYBE none), .BRANCH (.MANY []))) ]

private def alphaValue (first second reference literal : String) : p4programIR :=
  .RESULT ⟨(first, second, reference), alphaTree first, literal⟩

private def alphaExpected : p4programIR :=
  alphaValue "FRESH__0" "FRESH__1" "FRESH__0" "ordinary"

private def alphaSwapped : p4programIR :=
  alphaValue "FRESH__1" "FRESH__0" "FRESH__1" "ordinary"

private def alphaFirst : p4programIR → String
  | .RESULT value => value.IDS.1
private def alphaSecond : p4programIR → String
  | .RESULT value => value.IDS.2.1
private def alphaReference : p4programIR → String
  | .RESULT value => value.IDS.2.2
private def alphaLiteral : p4programIR → String
  | .RESULT value => value.LITERAL

-- Both failed and successful allocations may be included in the support. An
-- allocated name absent from the expected IR still cannot change ordinary data.
theorem alpha_swap :
    FreshAlphaIR ["FRESH__0", "FRESH__1", "unused_failed_allocation"] ["ordinary"]
      alphaExpected alphaSwapped := by
  apply FreshAlphaIR.swap _ _ "FRESH__0" "FRESH__1"
  · simp
  · simp
  · simp
  · simp
  · rfl

theorem alpha_reflexive (allocated protectedNames : List String) (value : p4programIR) :
    FreshAlphaIR allocated protectedNames value value := FreshAlphaIR.refl _ _ _

theorem alpha_no_collapse :
    ¬ FreshAlphaIR ["FRESH__0", "FRESH__1"] ["ordinary"] alphaExpected
      (alphaValue "FRESH__0" "FRESH__0" "FRESH__0" "ordinary") := by
  rintro ⟨ρ, bijective, _, equal⟩
  have first := congrArg alphaFirst equal
  have second := congrArg alphaSecond equal
  change ρ "FRESH__0" = "FRESH__0" at first
  change ρ "FRESH__1" = "FRESH__0" at second
  have collision := bijective.1 (first.trans second.symm)
  exact (by decide : ("FRESH__0" : String) ≠ "FRESH__1") collision

theorem alpha_no_inconsistent_reference :
    ¬ FreshAlphaIR ["FRESH__0", "FRESH__1"] ["ordinary"] alphaExpected
      (alphaValue "FRESH__1" "FRESH__0" "FRESH__0" "ordinary") := by
  rintro ⟨ρ, _, _, equal⟩
  have first := congrArg alphaFirst equal
  have reference := congrArg alphaReference equal
  change ρ "FRESH__0" = "FRESH__1" at first
  change ρ "FRESH__0" = "FRESH__0" at reference
  exact (by decide : ("FRESH__1" : String) ≠ "FRESH__0") (first.symm.trans reference)

theorem alpha_no_literal_change :
    ¬ FreshAlphaIR ["FRESH__0", "FRESH__1"] ["ordinary"] alphaExpected
      (alphaValue "FRESH__1" "FRESH__0" "FRESH__1" "changed literal") := by
  rintro ⟨ρ, _, fixed, equal⟩
  have literal := congrArg alphaLiteral equal
  change ρ "ordinary" = "changed literal" at literal
  have keep := fixed "ordinary" (Or.inr (by simp))
  exact (by decide : ("ordinary" : String) ≠ "changed literal") (keep.symm.trans literal)

-- Even a generated-looking input name is protected when it appears in the
-- protected list. No textual prefix is used to decide what may move.
theorem alpha_no_protected_allocation_change :
    ¬ FreshAlphaIR ["FRESH__0", "FRESH__1"] ["FRESH__0", "ordinary"]
      alphaExpected alphaSwapped := by
  rintro ⟨ρ, _, fixed, equal⟩
  have first := congrArg alphaFirst equal
  change ρ "FRESH__0" = "FRESH__1" at first
  have keep := fixed "FRESH__0" (Or.inr (by simp))
  exact (by decide : ("FRESH__0" : String) ≠ "FRESH__1") (keep.symm.trans first)

theorem alpha_no_unallocated_literal_change :
    ¬ FreshAlphaIR ["FRESH__0", "FRESH__1"] [] alphaExpected
      (alphaValue "FRESH__0" "FRESH__1" "FRESH__0" "changed literal") := by
  rintro ⟨ρ, _, fixed, equal⟩
  have literal := congrArg alphaLiteral equal
  change ρ "ordinary" = "changed literal" at literal
  have keep := fixed "ordinary" (Or.inl (by simp))
  exact (by decide : ("ordinary" : String) ≠ "changed literal") (keep.symm.trans literal)

private def numericValue (number : Nat) (flag : Bool) (integer : Int) : p4programIR :=
  .RESULT ⟨("FRESH__0", "FRESH__1", "FRESH__0"),
    .LEAF "FRESH__0" number flag integer, "ordinary"⟩
private def alphaNumeric : p4programIR → Nat × Bool × Int
  | .RESULT ⟨_, .LEAF _ number flag integer, _⟩ => (number, flag, integer)
  | _ => (0, false, 0)

theorem alpha_preserves_numeric_data (number : Nat) (flag : Bool) (integer : Int)
    (h : FreshAlphaIR ["FRESH__0", "FRESH__1"] ["ordinary"]
      (numericValue 7 true (-3)) (numericValue number flag integer)) :
    (7, true, (-3 : Int)) = (number, flag, integer) := by
  obtain ⟨ρ, _, _, equal⟩ := h
  exact congrArg alphaNumeric equal

#print axioms alpha_swap
#print axioms alpha_reflexive
#print axioms alpha_no_collapse
#print axioms alpha_no_inconsistent_reference
#print axioms alpha_no_literal_change
#print axioms alpha_no_protected_allocation_change
#print axioms alpha_no_unallocated_literal_change
#print axioms alpha_preserves_numeric_data

end SpecTec

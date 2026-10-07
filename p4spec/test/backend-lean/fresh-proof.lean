namespace SpecTec

private theorem fresh_at (n : Nat) :
    «$fresh_typeId:state» n ("FRESH__" ++ Nat.repr n) (n + 1) :=
  «$fresh_typeId:state».next n

private theorem fresh_zero : «$fresh_typeId:state» 0 "FRESH__0" 1 := by
  have same : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide
  rw [← same]
  exact fresh_at 0

private theorem fresh_one : «$fresh_typeId:state» 1 "FRESH__1" 2 := by
  have same : "FRESH__" ++ Nat.repr 1 = "FRESH__1" := by decide
  rw [← same]
  exact fresh_at 1

example : «$once» "FRESH__0" := by
  apply «$once».from_initial_counter 1
  exact «$once:state».case_1 0 "FRESH__0" 1 fresh_zero

example : «$twice» ("FRESH__0", "FRESH__1") := by
  apply «$twice».from_initial_counter 2
  exact «$twice:state».case_1 0 "FRESH__0" "FRESH__1" 1 2
    fresh_zero fresh_one

example : «$twice_via_function» ("FRESH__0", "FRESH__1") := by
  apply «$twice_via_function».from_initial_counter 2
  exact «$twice_via_function:state».case_1 0 "FRESH__0" "FRESH__1" 1 2
    («$once:state».case_1 0 "FRESH__0" 1 fresh_zero)
    («$once:state».case_1 1 "FRESH__1" 2 fresh_one)

example : «$after_failed» "FRESH__1" := by
  have first : «$after_failed:fail:0» 0 1 :=
    «$after_failed:fail:0».guard_1 0 "FRESH__0" 1
      fresh_zero (by decide)
  apply «$after_failed».from_initial_counter 2
  exact «$after_failed:state».case_2 0 "FRESH__1" 1 2 first
    fresh_one

private theorem only_zero_one_fails :
    SpecTecWFS.Fails InProgram (Atom.OnlyZero 1) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases inProgram <;> simp_all

example : «$after_rule_failure» "FRESH__1" := by
  have first : «$after_rule_failure:fail:0» 0 1 :=
    «$after_rule_failure:fail:0».guard_2 0 "FRESH__0" "FRESH__0" 1
      fresh_zero rfl only_zero_one_fails
  apply «$after_rule_failure».from_initial_counter 2
  exact «$after_rule_failure:state».case_2 0 "FRESH__1" 1 2 first fresh_one

private theorem only_zero_output_one_never (output : typeId)
    (negative : Atom → Prop) :
    ¬ SpecTecWFS.Derives InProgram negative (Atom.OnlyZeroOutput 1 output) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases inProgram <;> simp_all

private theorem output_call_match_fails (value : typeId) :
    SpecTecWFS.Fails InProgram
      (Atom.«$after_output_failure:callmatch:0:2» value value) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, positive, _⟩ :=
    SpecTecWFS.Derives.cases possible
  cases inProgram <;> simp_all [SpecTecWFS.All]
  exact only_zero_output_one_never _ _ positive

example : «$after_output_failure» "FRESH__1" := by
  have first : «$after_output_failure:fail:0» 0 1 :=
    «$after_output_failure:fail:0».guard_2 0 "FRESH__0" "FRESH__0"
      "zero" 1 fresh_zero rfl (output_call_match_fails "FRESH__0")
  apply «$after_output_failure».from_initial_counter 2
  exact «$after_output_failure:state».case_2 0 "FRESH__1" 1 2 first fresh_one

-- Each public entry point starts a separate program evaluation at counter 0.
example : «$once» "FRESH__0" ∧ «$once» "FRESH__0" := by
  constructor <;> exact «$once».from_initial_counter 1 "FRESH__0"
    («$once:state».case_1 0 "FRESH__0" 1 fresh_zero)

example : Program_ok 2 "FRESH__0" ∧ Program_ok 3 "FRESH__0" := by
  constructor
  · exact Program_ok.from_initial_counter 1 2 "FRESH__0"
      («Program_ok:state».fresh 0 2 "FRESH__0" 1 fresh_zero)
  · exact Program_ok.from_initial_counter 1 3 "FRESH__0"
      («Program_ok:state».fresh 0 3 "FRESH__0" 1 fresh_zero)

private theorem nonzero_match_fails (n : Nat) (nonzero : n ≠ 0) :
    SpecTecWFS.Fails InProgram (Atom.«$fresh_typeIds:match:0» n) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases inProgram <;> simp_all

example : «$fresh_typeIds» 2 ["FRESH__0", "FRESH__1"] := by
  have failed0 : «$fresh_typeIds:fail:0» 0 2 0 :=
    «$fresh_typeIds:fail:0».mismatch 0 2 (nonzero_match_fails 2 (by decide))
  have failed1 : «$fresh_typeIds:fail:0» 1 1 1 :=
    «$fresh_typeIds:fail:0».mismatch 1 1 (nonzero_match_fails 1 (by decide))
  have tail0 : «$fresh_typeIds:state» 2 0 [] 2 :=
    «$fresh_typeIds:state».case_1 2
  have tail1 : «$fresh_typeIds:state» 1 1 ["FRESH__1"] 2 := by
    exact «$fresh_typeIds:state».case_2 1 1 "FRESH__1" [] 0 1 2 2
      failed1 (by decide) (by decide) fresh_one tail0
  apply «$fresh_typeIds».from_initial_counter 2
  exact «$fresh_typeIds:state».case_2 0 2 "FRESH__0"
    ["FRESH__1"] 1 0 1 2 failed0 (by decide) (by decide)
    fresh_zero tail1

end SpecTec

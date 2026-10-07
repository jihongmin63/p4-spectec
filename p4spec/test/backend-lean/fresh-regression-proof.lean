namespace SpecTec

private theorem fresh_zero : «$fresh_typeId:state» 0 "FRESH__0" 1 := by
  have same : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 0

private theorem fresh_one : «$fresh_typeId:state» 1 "FRESH__1" 2 := by
  have same : "FRESH__" ++ Nat.repr 1 = "FRESH__1" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 1

-- A false guard must fail without evaluating either output expression.
private theorem ordered_failed : «Ordered:fail:0» 0 7 0 := by
  exact «Ordered:fail:0».guard_0 0 7 (by decide)

example : Ordered "FRESH__0" 7 "FRESH__1" := by
  apply Ordered.from_initial_counter 2
  apply «Ordered:state».good
  · exact ordered_failed
  · exact fresh_zero
  · exact fresh_one

-- Otherwise must remain reachable when only its fallback is stateful.
private theorem otherwise_mismatch :
    SpecTecWFS.Fails InProgram (Atom.«$otherwise_plain:match:0» 1) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all

example : «$otherwise_plain» 1 "FRESH__0" := by
  apply «$otherwise_plain».from_initial_counter 1
  apply «$otherwise_plain:state».case_2
  · exact «$otherwise_plain:fail:0».mismatch 0 1 otherwise_mismatch
  · exact fresh_zero

-- No head and tail match the empty list, including when they are newly bound.
example : «$pattern» [] "empty" := by
  apply «$pattern».from_initial_counter 0
  apply «$pattern:state».case_2
  · exact «$pattern:fail:0».guard_0 0 [] (by simp)
  · rfl

example : «$otherwise_plain» 0 "zero" :=
  «$otherwise_plain».from_initial_counter 0 0 "zero"
    («$otherwise_plain:state».case_1 0)

-- Failed regular guards consume a counter once, not again through enabled.
example : «$otherwise_effectful» "FRESH__1" := by
  have failed : «$otherwise_effectful:fail:0» 0 1 :=
    «$otherwise_effectful:fail:0».guard_1 0 "FRESH__0" 1 fresh_zero (by decide)
  exact «$otherwise_effectful».from_initial_counter 2 "FRESH__1"
    («$otherwise_effectful:state».case_2 0 "FRESH__1" 1 2 failed fresh_one)

example : «$otherwise_unvisited» "fallback" := by
  have failed : «$otherwise_unvisited:fail:0» 0 0 :=
    «$otherwise_unvisited:fail:0».guard_0 0 (by decide)
  exact «$otherwise_unvisited».from_initial_counter 0 "fallback"
    («$otherwise_unvisited:state».case_2 0 0 failed)

example : «$pattern» ["x"] "FRESH__0" :=
  «$pattern».from_initial_counter 1 ["x"] "FRESH__0"
    («$pattern:state».case_1 0 ["x"] "FRESH__0" "x" [] 1 rfl fresh_zero)

example : «$pattern_after_fresh» "FRESH__1" := by
  have failed : «$pattern_after_fresh:fail:0» 0 1 :=
    «$pattern_after_fresh:fail:0».guard_2 0 "FRESH__0" "FRESH__0" 1
      fresh_zero rfl (by simp)
  exact «$pattern_after_fresh».from_initial_counter 2 "FRESH__1"
    («$pattern_after_fresh:state».case_2 0 "FRESH__1" 1 2 failed fresh_one)

example : Guarded 7 "FRESH__1" :=
  Guarded.from_initial_counter 2 7 "FRESH__1"
    («Guarded:state».good 0 7 "FRESH__1" "FRESH__0" "FRESH__0" 1 2
      fresh_zero rfl fresh_one)

-- Proving the right output exists is not enough: rule out the old wrong ID.
private def orderedInvariant : Atom → Prop
  | .«$fresh_typeId:state» before value after =>
      value = "FRESH__" ++ Nat.repr before ∧ after = before + 1
  | .«Ordered:fail:0» before _ after => after = before
  | .«Ordered:state» before left _ right after =>
      left = "FRESH__" ++ Nat.repr before ∧
      right = "FRESH__" ++ Nat.repr (before + 1) ∧ after = before + 2
  | .Ordered left _ right => left = "FRESH__0" ∧ right = "FRESH__1"
  | _ => True

example (left right : typeId) (proof : Ordered left 7 right) :
    left = "FRESH__0" ∧ right = "FRESH__1" := by
  apply SpecTecWFS.Holds.sound (interpretation := orderedInvariant) proof
  intro rule inProgram side positive failures
  cases_in_program inProgram <;> simp_all [orderedInvariant, SpecTecWFS.All, Nat.add_assoc] <;> decide

-- A failed pattern does not need a witness for its newly bound element type.
example (X : Type) : «$generic_pattern:fail:0» (X := X) 0 [] 0 := by
  exact «$generic_pattern:fail:0».guard_0 0 [] (by simp)

-- A rulegroup and its otherwise branch may reuse the same source rule name.
private theorem grouped_mismatch :
    SpecTecWFS.Fails InProgram (Atom.«Grouped:match:0» 7) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all

example : Grouped 0 "zero" :=
  Grouped.from_initial_counter 0 0 "zero" («Grouped:state».fallback 0)

example : Grouped 7 "FRESH__0" := by
  apply Grouped.from_initial_counter 1
  apply «Grouped:state».fallback_2
  · exact «Grouped:fail:0».mismatch 0 7 grouped_mismatch
  · exact fresh_zero

private theorem fresh_at (n : Nat) :
    «$fresh_typeId:state» n ("FRESH__" ++ Nat.repr n) (n + 1) :=
  «$fresh_typeId:state».next n

private theorem fresh_two : «$fresh_typeId:state» 2 "FRESH__2" 3 := by
  have same : "FRESH__" ++ Nat.repr 2 = "FRESH__2" := by decide
  rw [← same]
  exact fresh_at 2

private theorem fresh_three : «$fresh_typeId:state» 3 "FRESH__3" 4 := by
  have same : "FRESH__" ++ Nat.repr 3 = "FRESH__3" := by decide
  rw [← same]
  exact fresh_at 3

example : «$after_three» "FRESH__3" := by
  have f0 : «$after_three:fail:0» 0 1 :=
    «$after_three:fail:0».guard_1 0 "FRESH__0" 1 («$tagged_fresh:state».case_1 0 0 "FRESH__0" 1 fresh_zero) (by decide)
  have f1 : «$after_three:fail:1» 0 2 :=
    «$after_three:fail:1».guard_1 0 1 "FRESH__1" 2 f0 («$tagged_fresh:state».case_1 1 1 "FRESH__1" 2 fresh_one) (by decide)
  have f2 : «$after_three:fail:2» 0 3 :=
    «$after_three:fail:2».guard_1 0 2 "FRESH__2" 3 f1 («$tagged_fresh:state».case_1 2 2 "FRESH__2" 3 fresh_two) (by decide)
  exact «$after_three».from_initial_counter 4 "FRESH__3"
    («$after_three:state».case_4 0 "FRESH__3" 3 4 f2 fresh_three)

example : «$after_all_failed» "FRESH__2" := by
  have f0 : «RejectFresh:fail:0» 0 0 1 :=
    «RejectFresh:fail:0».guard_1 0 0 "FRESH__0" 1 («$tagged_fresh:state».case_1 0 0 "FRESH__0" 1 fresh_zero) (by decide)
  have f1 : «RejectFresh:fail:1» 0 0 2 :=
    «RejectFresh:fail:1».guard_1 0 1 0 "FRESH__1" 2 f0 («$tagged_fresh:state».case_1 1 1 "FRESH__1" 2 fresh_one) (by decide)
  have failed : «RejectFresh:fail» 0 0 2 :=
    «RejectFresh:fail».all_failed 0 2 0 f1
  have first : «$after_all_failed:fail:0» 0 2 :=
    «$after_all_failed:fail:0».guard_0 0 2 failed
  exact «$after_all_failed».from_initial_counter 3 "FRESH__2"
    («$after_all_failed:state».case_2 0 "FRESH__2" 2 3 first fresh_two)

-- Repeated variables must retain their equality constraint after optimization.
private theorem diagonal_mismatch :
    SpecTecWFS.Fails InProgram (Atom.«$diagonal:match:0» 0 1) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all <;> omega

example : «$diagonal» 0 1 "FRESH__0" := by
  apply «$diagonal».from_initial_counter 1
  apply «$diagonal:state».case_2
  · exact «$diagonal:fail:0».mismatch 0 0 1 diagonal_mismatch
  · decide
  · exact fresh_zero

example : «$diagonal» 1 1 "same" :=
  «$diagonal».from_initial_counter 0 1 1 "same"
    («$diagonal:state».case_1 0 1)

-- Every derivation of the shared failure chain consumes exactly its effects.
private def failureCounterInvariant : Atom → Prop
  | .«$fresh_typeId:state» before _ after => after = before + 1
  | .«$tagged_fresh:state» before _ _ after => after = before + 1
  | .«$after_three:fail:0» before after => after = before + 1
  | .«$after_three:fail:1» before after => after = before + 2
  | .«$after_three:fail:2» before after => after = before + 3
  | .«RejectFresh:fail:0» before _ after => after = before + 1
  | .«RejectFresh:fail:1» before _ after => after = before + 2
  | .«RejectFresh:fail» before _ after => after = before + 2
  | .«$after_all_failed:fail:0» before after => after = before + 2
  | _ => True

private theorem failureCounterInvariant_sound (atom : Atom)
    (proof : SpecTecWFS.Holds InProgram atom) : failureCounterInvariant atom := by
  apply SpecTecWFS.Holds.sound (interpretation := failureCounterInvariant) proof
  intro rule inProgram side positive failures
  cases_in_program inProgram <;> simp_all [failureCounterInvariant, SpecTecWFS.All, Nat.add_assoc]

example (before after : Nat) (proof : «$after_three:fail:2» before after) :
    after = before + 3 :=
  failureCounterInvariant_sound _ proof

example (before after : Nat) (proof : «$after_all_failed:fail:0» before after) :
    after = before + 2 :=
  failureCounterInvariant_sound _ proof

end SpecTec

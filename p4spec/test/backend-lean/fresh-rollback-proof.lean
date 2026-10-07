namespace SpecTec

private theorem fresh_never (value suffix : String) :
    "FRESH__" ++ value ≠ "never" ++ suffix := by
  intro equality
  have chars := congrArg String.toList equality
  simp [String.toList_append] at chars

@[simp] private theorem fresh_never_zero (value : String) :
    "FRESH__" ++ value ≠ "never0" := fresh_never value "0"

@[simp] private theorem fresh_never_one (value : String) :
    "FRESH__" ++ value ≠ "never1" := fresh_never value "1"

@[simp] private theorem fresh_never_two (value : String) :
    "FRESH__" ++ value ≠ "never2" := fresh_never value "2"

@[simp] private theorem never_fresh_zero (value : String) :
    "never0" ≠ "FRESH__" ++ value := (fresh_never_zero value).symm

@[simp] private theorem never_fresh_one (value : String) :
    "never1" ≠ "FRESH__" ++ value := (fresh_never_one value).symm

@[simp] private theorem never_fresh_two (value : String) :
    "never2" ≠ "FRESH__" ++ value := (fresh_never_two value).symm

@[simp] private theorem fresh_text_zero : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide
@[simp] private theorem fresh_text_one : "FRESH__" ++ Nat.repr 1 = "FRESH__1" := by decide
@[simp] private theorem fresh_text_five : "FRESH__" ++ Nat.repr 5 = "FRESH__5" := by decide

private theorem fresh_zero : «$fresh_typeId:state» 0 "FRESH__0" 1 := by
  have same : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 0

private theorem fresh_one : «$fresh_typeId:state» 1 "FRESH__1" 2 := by
  have same : "FRESH__" ++ Nat.repr 1 = "FRESH__1" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 1

private theorem fresh_five : «$fresh_typeId:state» 5 "FRESH__5" 6 := by
  have same : "FRESH__" ++ Nat.repr 5 = "FRESH__5" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 5

private theorem after_three_at (entry : Nat) :
    «$after_three:state» entry ("FRESH__" ++ Nat.repr entry) (entry + 1) := by
  have alloc := «$fresh_typeId:state».next entry
  have tagged (tag : Nat) :=
    «$tagged_fresh:state».case_1 entry tag _ _ alloc
  have f0 : «$after_three:fail:0» entry := by
    apply «$after_three:fail:0».guard_1
    · exact tagged 0
    · simp
  have f1 : «$after_three:fail:1» entry := by
    apply «$after_three:fail:1».guard_1
    · exact f0
    · exact tagged 1
    · simp
  have f2 : «$after_three:fail:2» entry := by
    apply «$after_three:fail:2».guard_1
    · exact f1
    · exact tagged 2
    · simp
  apply «$after_three:state».case_4
  · exact f2
  · exact alloc

example : «$after_three» "FRESH__0" := by
  apply «$after_three».from_initial_counter 1
  simpa using after_three_at 0

example : «$after_three:state» 5 "FRESH__5" 6 := by
  simpa using after_three_at 5

private theorem reject_at (entry input : Nat) : «RejectFresh:fail» entry input := by
  have alloc := «$fresh_typeId:state».next entry
  have tagged (tag : Nat) :=
    «$tagged_fresh:state».case_1 entry tag _ _ alloc
  have f0 : «RejectFresh:fail:0» entry input := by
    apply «RejectFresh:fail:0».guard_1
    · exact tagged 0
    · simp
  have f1 : «RejectFresh:fail:1» entry input := by
    apply «RejectFresh:fail:1».guard_1
    · exact f0
    · exact tagged 1
    · simp
  exact «RejectFresh:fail».all_failed entry input f1

private theorem after_all_at (entry : Nat) :
    «$after_all_failed:state» entry ("FRESH__" ++ Nat.repr entry) (entry + 1) := by
  have first : «$after_all_failed:fail:0» entry :=
    «$after_all_failed:fail:0».guard_0 entry (reject_at entry 0)
  apply «$after_all_failed:state».case_2
  · exact first
  · exact «$fresh_typeId:state».next entry

example : «$after_all_failed» "FRESH__0" := by
  apply «$after_all_failed».from_initial_counter 1
  simpa using after_all_at 0

example : «$nested_twice» ("FRESH__0", "FRESH__1") := by
  apply «$nested_twice».from_initial_counter 2
  apply «$nested_twice:state».case_1
  · simpa using after_three_at 0
  · simpa using after_all_at 1

-- A nested failing call sees its current prefix counter, but its caller rolls
-- back both that prefix and the nested attempts before trying its fallback.
example : «$failed_prefix» "FRESH__0" := by
  have first : «$failed_prefix:fail:0» 0 := by
    apply «$failed_prefix:fail:0».guard_2
    · exact fresh_zero
    · rfl
    · exact reject_at 1 0
  apply «$failed_prefix».from_initial_counter 1
  apply «$failed_prefix:state».case_2
  · exact first
  · exact fresh_zero

example : «$otherwise_effectful» "FRESH__0" := by
  have first : «$otherwise_effectful:fail:0» 0 := by
    apply «$otherwise_effectful:fail:0».guard_1
    · exact «$tagged_fresh:state».case_1 0 0 _ _ fresh_zero
    · decide
  apply «$otherwise_effectful».from_initial_counter 1
  apply «$otherwise_effectful:state».case_2
  · exact first
  · exact fresh_zero

example : «$pattern_after_fresh» "FRESH__0" := by
  have first : «$pattern_after_fresh:fail:0» 0 := by
    apply «$pattern_after_fresh:fail:0».guard_2
    · exact fresh_zero
    · rfl
    · simp
  apply «$pattern_after_fresh».from_initial_counter 1
  apply «$pattern_after_fresh:state».case_2
  · exact first
  · exact fresh_zero

-- Failure quantifies newly introduced pattern variables, so an empty element
-- type does not need an arbitrary inhabitant to reach the next clause.
example (X : Type) : «$generic_pattern:fail:0» (X := X) 0 [] := by
  exact «$generic_pattern:fail:0».guard_0 0 [] (by simp)

example : «$generic_pattern» (X := Empty) [] "empty" := by
  apply «$generic_pattern».from_initial_counter 0
  apply «$generic_pattern:state».case_2
  · exact «$generic_pattern:fail:0».guard_0 0 [] (by simp)
  · rfl

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

private theorem nonzero_match_fails (n : Nat) (nonzero : n ≠ 0) :
    SpecTecWFS.Fails InProgram (Atom.«$fresh_typeIds:match:0» n) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all

example : «$fresh_typeIds» 2 ["FRESH__0", "FRESH__1"] := by
  have f0 : «$fresh_typeIds:fail:0» 0 2 :=
    «$fresh_typeIds:fail:0».mismatch 0 2 (nonzero_match_fails 2 (by decide))
  have f1 : «$fresh_typeIds:fail:0» 1 1 :=
    «$fresh_typeIds:fail:0».mismatch 1 1 (nonzero_match_fails 1 (by decide))
  have tail0 : «$fresh_typeIds:state» 2 0 [] 2 :=
    «$fresh_typeIds:state».case_1 2
  have tail1 : «$fresh_typeIds:state» 1 1 ["FRESH__1"] 2 := by
    apply «$fresh_typeIds:state».case_2 (n' := 0)
    · exact f1
    · decide
    · decide
    · exact fresh_one
    · exact tail0
  apply «$fresh_typeIds».from_initial_counter 2
  apply «$fresh_typeIds:state».case_2 (n' := 1)
  · exact f0
  · decide
  · decide
  · exact fresh_zero
  · exact tail1

-- Negative calls that succeed discard all allocations used to prove failure.
example : «$negative_success» "FRESH__0" := by
  apply «$negative_success».from_initial_counter 1
  apply «$negative_success:state».case_1
  · exact reject_at 0 0
  · exact fresh_zero

-- A positive witness falsifying a negative guard remains local to that failed
-- alternative, even after the alternative itself already allocated a value.
example : «$negative_failure» "FRESH__0" := by
  have accept : «AcceptFresh:state» 1 0 2 := by
    apply «AcceptFresh:state».accept
    · exact fresh_one
    · rfl
  have first : «$negative_failure:fail:0» 0 := by
    apply «$negative_failure:fail:0».guard_2
    · exact fresh_zero
    · rfl
    · exact accept
  apply «$negative_failure».from_initial_counter 1
  apply «$negative_failure:state».case_2
  · exact first
  · exact fresh_zero

example : «$priority» "chosen" :=
  «$priority».from_initial_counter 0 "chosen" («$priority:state».case_1 0)

private theorem only_zero_one_fails :
    SpecTecWFS.Fails InProgram (Atom.OnlyZero 1) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all

example : «$pure_failure» "FRESH__0" := by
  have first : «$pure_failure:fail:0» 0 := by
    apply «$pure_failure:fail:0».guard_2
    · exact fresh_zero
    · rfl
    · exact only_zero_one_fails
  apply «$pure_failure».from_initial_counter 1
  apply «$pure_failure:state».case_2
  · exact first
  · exact fresh_zero

private theorem only_zero_output_one_never (value : typeId)
    (negative : Atom → Prop) :
    ¬ SpecTecWFS.Derives InProgram negative (Atom.OnlyZeroOutput 1 value) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, _, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all

private theorem output_match_fails (value : typeId) :
    SpecTecWFS.Fails InProgram
      (Atom.«$pure_output_failure:callmatch:0:2» value value) := by
  intro possible
  obtain ⟨rule, inProgram, head, _, positive, _⟩ := SpecTecWFS.Derives.cases possible
  cases_in_program inProgram <;> simp_all [SpecTecWFS.All]
  exact only_zero_output_one_never _ _ positive

example : «$pure_output_failure» "FRESH__0" := by
  have first : «$pure_output_failure:fail:0» 0 := by
    apply «$pure_output_failure:fail:0».guard_2
    · exact fresh_zero
    · rfl
    · exact output_match_fails "FRESH__0"
  apply «$pure_output_failure».from_initial_counter 1
  apply «$pure_output_failure:state».case_2
  · exact first
  · exact fresh_zero

-- Soundness excludes stale outputs as well as proving the expected outputs.
private def rollbackInvariant : Atom → Prop
  | .«$fresh_typeId:state» before value after =>
      value = "FRESH__" ++ Nat.repr before ∧ after = before + 1
  | .«$tagged_fresh:state» before _ value after =>
      value = "FRESH__" ++ Nat.repr before ∧ after = before + 1
  | .«$after_three:state» before value after =>
      value = "FRESH__" ++ Nat.repr before ∧ after = before + 1
  | .«$after_three» value => value = "FRESH__0"
  | .«RejectFresh:state» _ _ _ => False
  | .RejectFresh _ => False
  | .«$after_all_failed:state» before value after =>
      value = "FRESH__" ++ Nat.repr before ∧ after = before + 1
  | .«$after_all_failed» value => value = "FRESH__0"
  | .«$nested_twice:state» before values after =>
      values = ("FRESH__" ++ Nat.repr before, "FRESH__" ++ Nat.repr (before + 1)) ∧
      after = before + 2
  | .«$nested_twice» values => values = ("FRESH__0", "FRESH__1")
  | .«$priority:fail:0» _ => False
  | .«$priority:state» before value after => value = "chosen" ∧ after = before
  | .«$priority» value => value = "chosen"
  | _ => True

private theorem rollbackInvariant_sound (atom : Atom)
    (proof : SpecTecWFS.Holds InProgram atom) : rollbackInvariant atom := by
  apply SpecTecWFS.Holds.sound (interpretation := rollbackInvariant) proof
  intro rule inProgram side positive failures
  cases_in_program inProgram <;>
    simp_all [rollbackInvariant, SpecTecWFS.All, Nat.add_assoc] <;> decide

example (value : typeId) (proof : «$after_three» value) : value = "FRESH__0" :=
  rollbackInvariant_sound _ proof

example (values : typeId × typeId) (proof : «$nested_twice» values) :
    values = ("FRESH__0", "FRESH__1") :=
  rollbackInvariant_sound _ proof

example (value : typeId) (proof : «$priority» value) : value = "chosen" :=
  rollbackInvariant_sound _ proof

end SpecTec

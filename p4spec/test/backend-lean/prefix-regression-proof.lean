namespace SpecTec

-- A guard that fails before a pattern must not require a future X witness.
example (X : Type) : «$late_pattern:fail:0» (X := X) 0 [] 0 := by
  apply «$late_pattern:fail:0».guard_0
  decide

private theorem fresh_zero : «$fresh_typeId:state» 0 "FRESH__0" 1 := by
  have same : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 0

private theorem fresh_one : «$fresh_typeId:state» 1 "FRESH__1" 2 := by
  have same : "FRESH__" ++ Nat.repr 1 = "FRESH__1" := by decide
  rw [← same]
  exact «$fresh_typeId:state».next 1

-- Sharing must retain the fresh effect and the existential list witness.
example : «$guarded_prefix» 16 [7] "FRESH__0" := by
  apply «$guarded_prefix».from_initial_counter 1
  apply «$guarded_prefix:state».case_1 0 16 [7] "FRESH__0" "FRESH__0" 7 [] 1
  all_goals first | exact fresh_zero | rfl | decide

example : «$guarded_prefix» 12 [7] "FRESH__1" := by
  have first : «$guarded_prefix:fail:0:prefix:0» 0 12 [7] 1 := by
    apply «$guarded_prefix:fail:0:prefix:0».intro 0 12 [7] "FRESH__0" "FRESH__0" 7 [] 1
    all_goals first | exact fresh_zero | rfl | decide
  have second : «$guarded_prefix:fail:0:prefix:1» 0 12 [7] 1 := by
    apply «$guarded_prefix:fail:0:prefix:1».intro
    · exact first
    all_goals decide
  have failed : «$guarded_prefix:fail:0» 0 12 [7] 1 := by
    apply «$guarded_prefix:fail:0».guard_15
    · exact second
    all_goals decide
  exact «$guarded_prefix».from_initial_counter 2 12 [7] "FRESH__1"
    («$guarded_prefix:state».case_2 0 12 [7] "FRESH__1" 1 2 failed fresh_one)

-- An empty type must remain usable when the input pattern fails.
example (X : Type) : «$guarded_prefix» (X := X) 12 [] "FRESH__1" := by
  have failed : «$guarded_prefix:fail:0» (X := X) 0 12 [] 1 :=
    «$guarded_prefix:fail:0».guard_2 0 12 [] "FRESH__0" "FRESH__0" 1 fresh_zero rfl (by simp)
  exact «$guarded_prefix».from_initial_counter 2 12 [] "FRESH__1"
    («$guarded_prefix:state».case_2 0 12 [] "FRESH__1" 1 2 failed fresh_one)

example (X : Type) : «$late_pattern» (X := X) [] "FRESH__0" := by
  apply «$late_pattern».from_initial_counter 1
  apply «$late_pattern:state».case_2
  · exact «$late_pattern:fail:0».guard_0 0 [] (by decide)
  · exact fresh_zero

private def counterInvariant : Atom → Prop
  | .«$fresh_typeId:state» before _ after => after = before + 1
  | .«$guarded_prefix:fail:0:prefix:0» before _ _ after => after = before + 1
  | .«$guarded_prefix:fail:0:prefix:1» before _ _ after => after = before + 1
  | .«$guarded_prefix:fail:0:prefix:2» before _ after => after = before + 1
  | .«$guarded_prefix:fail:0» before _ _ after => after = before + 1
  | _ => True

-- Every failure derivation through a shared prefix consumes fresh exactly once.
example (X : Type) (values : List X) (before after n : Nat)
    (proof : «$guarded_prefix:fail:0» before n values after) : after = before + 1 := by
  apply SpecTecWFS.Holds.sound (interpretation := counterInvariant) proof
  intro rule inProgram side positive failures
  cases_in_program inProgram <;> simp_all [counterInvariant, SpecTecWFS.All]

end SpecTec

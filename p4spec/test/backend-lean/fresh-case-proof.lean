namespace SpecTec

private def candidate : p4programIR := .RESULT "FRESH__0" "FRESH__0" "FRESH__99"

private theorem fresh_never (entry : Nat) :
    "FRESH__" ++ Nat.repr entry ≠ "never" := by
  intro equal
  have chars := congrArg String.toList equal
  simp [String.toList_append] at chars

@[simp] private theorem never_fresh (entry : Nat) :
    "never" ≠ "FRESH__" ++ Nat.repr entry := (fresh_never entry).symm

@[simp] private theorem fresh_zero_text : "FRESH__" ++ Nat.repr 0 = "FRESH__0" := by decide

private def correct : Atom → Prop
  | .«$fresh_typeId:state» entry output _ => output = "FRESH__" ++ Nat.repr entry
  | .«$pick:state» entry output _ => output = "FRESH__" ++ Nat.repr entry
  | .«Program_ok:state» entry _ output _ =>
      output = .RESULT ("FRESH__" ++ Nat.repr entry) ("FRESH__" ++ Nat.repr entry) "FRESH__99"
  | .Program_ok _ output => output = candidate
  | _ => True

private theorem correct_sound {atom : Atom} (proof : SpecTecWFS.Holds InProgram atom) :
    correct atom := by
  apply SpecTecWFS.Holds.sound proof
  intro rule member side positive negative
  cases member <;> simp_all [correct, SpecTecWFS.All, candidate]

private theorem accepted : Program_ok case_0_input candidate := by
  have alloc : «$fresh_typeId:state» 0 "FRESH__0" 1 := by
    simpa using «$fresh_typeId:state».next 0
  have failed := «$pick:fail:0».guard_1 0 "FRESH__0" 1 alloc (by decide)
  have pick := «$pick:state».case_2 0 "FRESH__0" 1 failed alloc
  exact Program_ok.from_initial_counter 1 case_0_input candidate
    («Program_ok:state».empty 0 "FRESH__0" "FRESH__0" 1 pick rfl)

private theorem alpha_candidate :
    FreshAlphaIR case_0_fresh_names case_0_protected_names case_0_expected candidate := by
  apply FreshAlphaIR.swap _ _ "FRESH__1" "FRESH__0"
  · decide
  · decide
  · decide
  · decide
  · rfl

theorem fresh_case_proved : case_0 := by
  refine ⟨⟨candidate, accepted, alpha_candidate⟩, ?_⟩
  intro output proof
  have equal : output = candidate := correct_sound proof
  rw [equal]
  exact alpha_candidate

#print axioms correct_sound
#print axioms fresh_case_proved

end SpecTec

example : SpecTec.«$list_slice» [1, 2, 3] 1 2 [2, 3] := by
  apply SpecTec.«$list_slice».case_1
  decide

example : SpecTec.«$list_slice» [1, 2, 3] 3 0 [] := by
  apply SpecTec.«$list_slice».case_1
  decide

example : ¬ SpecTec.«$list_slice» [1, 2, 3] 3 1 [] := by
  intro h
  let interpretation : SpecTec.Atom → Prop := fun atom =>
    match atom with
    | .«$list_slice» ns start length _ => start + length ≤ ns.length
    | _ => True
  have valid := SpecTecWFS.Holds.sound (interpretation := interpretation) h (by
    intro rule inProgram side positive negative
    cases_in_program inProgram <;> simp_all [interpretation, SpecTecWFS.All])
  exact (by decide : ¬ (3 + 1 ≤ ([1, 2, 3] : List Nat).length)) valid

example : SpecTec.«$text_slice» "abc" 1 1 "b" := by
  exact SpecTec.«$text_slice».case_1 "abc" 1 1 "b" "a" "c"
    (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$text_slice» "abc" 3 1 "x" := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases_in_program inProgram <;> simp_all [SpecTecWFS.All]
  intro hwhole hstart hlength hresult
  have size := congrArg String.utf8ByteSize hwhole
  have literal_size : ("abc").utf8ByteSize = 3 := by decide
  simp only [String.utf8ByteSize_append] at size
  omega

example : SpecTec.«$text_index» "abc" 1 "b" := by
  exact SpecTec.«$text_index».case_1 "abc" 1 "b" "a" "c"
    (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$text_index» "abc" 3 "x" := by
  apply SpecTecWFS.Holds.not_of_rules
  intro rule inProgram side positive negative
  cases_in_program inProgram <;> simp_all [SpecTecWFS.All]
  intro hwhole hstart hresult
  have size := congrArg String.utf8ByteSize hwhole
  have literal_size : ("abc").utf8ByteSize = 3 := by decide
  simp only [String.utf8ByteSize_append] at size
  omega

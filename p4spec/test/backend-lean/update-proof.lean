example :
    SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 9) 3) := by
  exact SpecTec.«$update_nested».case_1 _

example :
    ¬ SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 9) 4) := by
  intro h
  cases h

example :
    ¬ SpecTec.«$update_nested»
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 1 2) 3)
      (SpecTec.outerRecord.mk (SpecTec.innerRecord.mk 4 9) 3) := by
  intro h
  cases h

example : SpecTec.«$update_list» [1, 2, 3] 1 9 [1, 9, 3] := by
  apply SpecTec.«$update_list».case_1
  decide

example : ¬ SpecTec.«$update_list» [1, 2, 3] 3 9 [1, 2, 3] := by
  intro h
  cases h
  simp_all

example : SpecTec.«$update_text» "abc" 1 "x" "axc" := by
  exact SpecTec.«$update_text».case_1 "abc" 1 "x" "a" "c" "b"
    (by decide) (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$update_text» "abc" 3 "x" "abc" := by
  intro h
  have no_result : ∀ result, ¬ SpecTec.«$update_text» "abc" 3 "x" result := by
    intro result derived
    cases derived with
    | case_1 pre suf old_text hwhole pre_size old_size new_size =>
        have size := congrArg String.utf8ByteSize hwhole
        have literal_size : ("abc").utf8ByteSize = 3 := by decide
        simp only [String.utf8ByteSize_append] at size
        omega
  exact no_result "abc" h

example : ¬ SpecTec.«$update_text» "abc" 1 "xy" "axyc" := by
  intro h
  have no_result : ∀ result, ¬ SpecTec.«$update_text» "abc" 1 "xy" result := by
    intro result derived
    cases derived with
    | case_1 pre suf old_text hwhole pre_size old_size new_size =>
        have literal_size : ("xy").utf8ByteSize = 2 := by decide
        omega
  exact no_result "axyc" h

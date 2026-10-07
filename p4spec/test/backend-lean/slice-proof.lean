example : SpecTec.«$list_slice» [1, 2, 3] 1 2 [2, 3] := by
  apply SpecTec.«$list_slice».case_1
  decide

example : SpecTec.«$list_slice» [1, 2, 3] 3 0 [] := by
  apply SpecTec.«$list_slice».case_1
  decide

example : ¬ SpecTec.«$list_slice» [1, 2, 3] 3 1 [] := by
  intro h
  cases h
  simp_all

example : SpecTec.«$text_slice» "abc" 1 1 "b" := by
  exact SpecTec.«$text_slice».case_1 "abc" 1 1 "b" "a" "c"
    (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$text_slice» "abc" 3 1 "x" := by
  intro h
  cases h with
  | case_1 pre suf hwhole pre_size slice_size =>
      have size := congrArg String.utf8ByteSize hwhole
      have literal_size : ("abc").utf8ByteSize = 3 := by decide
      simp only [String.utf8ByteSize_append] at size
      omega

example : SpecTec.«$text_index» "abc" 1 "b" := by
  exact SpecTec.«$text_index».case_1 "abc" 1 "b" "a" "c"
    (by decide) (by decide) (by decide)

example : ¬ SpecTec.«$text_index» "abc" 3 "x" := by
  intro h
  cases h with
  | case_1 pre suf hwhole pre_size result_size =>
      have size := congrArg String.utf8ByteSize hwhole
      have literal_size : ("abc").utf8ByteSize = 3 := by decide
      simp only [String.utf8ByteSize_append] at size
      omega

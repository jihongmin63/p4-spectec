def textSet (elements : List String) : SpecTec.set String :=
  .«`{ % `}» elements

def textLeft : SpecTec.set String :=
  textSet ["b", "a", "a", "Z", "é", ""]

def textRight : SpecTec.set String :=
  textSet ["z", "ab", "b", "FRESH__2", "FRESH__10", "a"]

def textAll : SpecTec.set String :=
  textSet ["", "FRESH__10", "FRESH__2", "Z", "a", "ab", "b", "z", "é"]

example : SpecTec.«$union_set» textLeft textRight = textAll := by
  rfl

example :
    SpecTec.«$union_set» textLeft (textSet []) =
      textSet ["", "Z", "a", "b", "é"] := by
  rfl

example : SpecTec.«$unions_set» [] = textSet [] := by
  rfl

example :
    SpecTec.«$unions_set»
      [ textSet ["b", "FRESH__2", ""],
        textSet ["a", "Z", "FRESH__10"],
        textSet ["é", "z", "ab", "b"] ] = textAll := by
  rfl

example :
    SpecTec.«$diff_set» textLeft (textSet ["b", "Z", "x", "b"]) =
      textSet ["", "a", "é"] := by
  rfl

example :
    SpecTec.«$intersect_set» textLeft (textSet ["b", "Z", "x", "b"]) =
      textSet ["Z", "b"] := by
  rfl

example : SpecTec.«$intersect_set» textLeft (textSet []) = textSet [] := by
  rfl

example : SpecTec.«$union_alias» textLeft textRight textAll := by
  exact SpecTec.«$union_alias».case_1 textLeft textRight

example :
    SpecTec.«$unions_alias»
      [ textSet ["b", "FRESH__2", ""],
        textSet ["a", "Z", "FRESH__10"],
        textSet ["é", "z", "ab", "b"] ] textAll := by
  exact SpecTec.«$unions_alias».case_1 _

example :
    SpecTec.«$diff_alias» textLeft (textSet ["b", "Z", "x", "b"])
      (textSet ["", "a", "é"]) := by
  exact SpecTec.«$diff_alias».case_1 _ _

example :
    SpecTec.«$intersect_alias» textLeft (textSet ["b", "Z", "x", "b"])
      (textSet ["Z", "b"]) := by
  exact SpecTec.«$intersect_alias».case_1 _ _

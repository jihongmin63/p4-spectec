example : SpecTec.«$triple» 1 2 3 (1, (2, 3)) := by
  exact SpecTec.«$triple».case_1 1 2 3

example : ¬ SpecTec.«$triple» 1 2 3 (1, (3, 2)) := by
  intro h
  cases h

example : SpecTec.«$triple_nat» 1 2 3 true := by
  exact SpecTec.«$triple_nat».case_1 1 2 3

example : SpecTec.«$triple_nat» (-1) 2 3 false := by
  exact SpecTec.«$triple_nat».case_1 (-1) 2 3

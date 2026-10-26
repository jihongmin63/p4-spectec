example :
    SpecTec.«$eq_shadow» SpecTec.shade.LIGHT SpecTec.shade.LIGHT true := by
  exact SpecTec.«$eq_shadow».case_1 SpecTec.shade.LIGHT SpecTec.shade.LIGHT

example :
    SpecTec.«$eq_shadow» SpecTec.shade.LIGHT SpecTec.shade.DARK false := by
  exact SpecTec.«$eq_shadow».case_1 SpecTec.shade.LIGHT SpecTec.shade.DARK

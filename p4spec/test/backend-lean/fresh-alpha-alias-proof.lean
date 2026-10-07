namespace SpecTec

theorem alpha_nested_alias_swap :
    FreshAlphaIR ["left", "right"] [] (.BOX (.BOX "left")) (.BOX (.BOX "right")) := by
  apply FreshAlphaIR.swap _ _ "left" "right"
  · simp
  · simp
  · simp
  · simp
  · rfl

theorem alpha_nested_alias_identity (allocated protectedNames : List String)
    (value : p4programIR) : FreshAlphaIR allocated protectedNames value value :=
  FreshAlphaIR.refl _ _ _

#print axioms alpha_nested_alias_swap
#print axioms alpha_nested_alias_identity
end SpecTec

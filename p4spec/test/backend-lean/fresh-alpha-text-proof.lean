namespace SpecTec

theorem alpha_text_swap : FreshAlphaIR ["left", "right"] [] "left" "right" := by
  apply FreshAlphaIR.swap _ _ "left" "right"
  · simp
  · simp
  · simp
  · simp
  · rfl

theorem alpha_text_identity (allocated protectedNames : List String) (name : String) :
    FreshAlphaIR allocated protectedNames name name := FreshAlphaIR.refl _ _ _

#print axioms alpha_text_swap
#print axioms alpha_text_identity
end SpecTec

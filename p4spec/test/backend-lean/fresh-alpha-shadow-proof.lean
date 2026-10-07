namespace SpecTec

theorem alpha_shadow_swap :
    FreshAlphaIR ["left", "right"] []
      (.EXPECTED (.OUTPUT (.VALUE "left"))) (.EXPECTED (.OUTPUT (.VALUE "right"))) := by
  apply FreshAlphaIR.swap _ _ "left" "right"
  · simp
  · simp
  · simp
  · simp
  · rfl

theorem alpha_shadow_identity (allocated protectedNames : List String)
    (value : p4programIR) : FreshAlphaIR allocated protectedNames value value :=
  FreshAlphaIR.refl _ _ _

#print axioms alpha_shadow_swap
#print axioms alpha_shadow_identity
end SpecTec

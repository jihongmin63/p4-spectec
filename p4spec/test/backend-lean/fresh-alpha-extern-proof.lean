namespace SpecTec
variable [SpecTecExternTypes]

-- Extern values are fixed by the rename operation, even when their concrete
-- model happens to contain String values.
theorem alpha_extern_fixed (ρ : String → String) (value : json) (name : String) :
    FreshRename_p4programIR ρ (.EXTERNAL value name) = .EXTERNAL value (ρ name) := rfl

theorem alpha_extern_no_change (allocated protectedNames : List String)
    (left right : json) (name : String)
    (h : FreshAlphaIR allocated protectedNames (.EXTERNAL left name) (.EXTERNAL right name)) :
    left = right := by
  obtain ⟨ρ, _, _, equal⟩ := h
  exact (p4programIR.EXTERNAL.inj equal).1

theorem alpha_extern_wrapper (ρ : String → String) (value : json) :
    FreshRename_p4programIR ρ (.WRAPPED (.BOX value)) = .WRAPPED (.BOX value) := rfl

example (allocated protectedNames : List String) (value : p4programIR) :
    FreshAlphaIR allocated protectedNames value value := FreshAlphaIR.refl _ _ _

#print axioms alpha_extern_fixed
#print axioms alpha_extern_no_change
#print axioms alpha_extern_wrapper
end SpecTec

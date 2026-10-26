namespace SpecTec

variable [SpecTecExternTypes] [SpecTecP4ExternModel]

example (state : archState) :
    «$init_archState» state ↔ SpecTecExternTypes.validArchState state := by
  constructor
  · intro proof; cases proof with | allowed valid => exact valid
  · intro valid; exact «$init_archState».allowed state valid

example (ctx : typingContext) (name : nameIR) (args : List nameIR)
    (result : value) :
    ExternFunctionCall_eval_lctk ctx name args result ↔
      externStaticAllowed ctx name args result := by
  constructor
  · intro proof; cases proof with | allowed valid => exact valid
  · intro valid; exact ExternFunctionCall_eval_lctk.allowed ctx name args result valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (result : callResult) :
    ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result ↔
      externFunctionAllowed ctx₀ arch₀ name args ctx₁ arch₁ result := by
  constructor
  · intro proof; cases proof with | allowed valid => exact valid
  · intro valid
    exact ExternFunctionCall_eval.allowed ctx₀ arch₀ name args ctx₁ arch₁ result valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (object : objectId) (name : nameIR) (args : List nameIR)
    (result : callResult) :
    ExternMethodCall_eval ctx₀ arch₀ object name args ctx₁ arch₁ result ↔
      externMethodAllowed ctx₀ arch₀ object name args ctx₁ arch₁ result := by
  constructor
  · intro proof; cases proof with | allowed valid => exact valid
  · intro valid
    exact ExternMethodCall_eval.allowed ctx₀ arch₀ object name args ctx₁ arch₁ result valid

example (ctx₀ ctx₁ : evalContext) (arch₀ arch₁ : arch)
    (name : nameIR) (args : List nameIR) (result : callResult)
    (invalid : ¬ SpecTecExternTypes.validArchState arch₀.STATE) :
    ¬ ExternFunctionCall_eval ctx₀ arch₀ name args ctx₁ arch₁ result := by
  intro proof
  cases proof with
  | allowed valid => exact invalid valid.2.2.2.2.1

example (v : val) : «$via_first» v 7 := by
  apply «$via_first».case_1
  constructor

end SpecTec

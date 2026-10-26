-- Selector premises of concrete rows close by `rfl`.
example : SpecTec.«$is_small» (SpecTec.ty.WRAP "w" (SpecTec.ty.S2 3)) true :=
  .row_1 _ _ _ rfl (.row_0 _ rfl)

example : SpecTec.«$is_small» (SpecTec.ty.LIST []) true :=
  .row_2 [] true [] rfl .nil .case_1

-- Overlapping rows: (WRAP, WRAP) selects the earlier row, as the interpreter does.
example :
    SpecTec.«$compat:row» (SpecTec.ty.WRAP "a" SpecTec.ty.A)
      (SpecTec.ty.WRAP "b" SpecTec.ty.A) = 2 := rfl

example :
    SpecTec.«$compat» (SpecTec.ty.WRAP "a" SpecTec.ty.A)
      (SpecTec.ty.WRAP "b" SpecTec.ty.A) true :=
  .row_2 _ _ _ _ rfl (.row_3 _ _ _ _ rfl (.row_0 rfl))

-- The selector makes the relation functional.
theorem compat_deterministic {l r : SpecTec.ty} {b₁ b₂ : Bool}
    (h₁ : SpecTec.«$compat» l r b₁) (h₂ : SpecTec.«$compat» l r b₂) : b₁ = b₂ := by
  induction h₁ generalizing b₂ with
  | row_2 _ _ _ _ _ _ ih =>
      cases h₂ <;> first | exact ih (by assumption) | simp_all [SpecTec.«$compat:row»]
  | row_3 _ _ _ _ _ _ ih =>
      cases h₂ <;> first | exact ih (by assumption) | simp_all [SpecTec.«$compat:row»]
  | _ => cases h₂ <;> simp_all [SpecTec.«$compat:row»]

-- Inversion works on the subtype row: its conclusion has no coercion.
example : ¬ SpecTec.«$is_small» SpecTec.ty.A true := by
  intro h
  cases h <;> simp_all [SpecTec.«$is_small:row»]

-- Exhaustive rows without a catch-all row.
example : SpecTec.«$is_warm» SpecTec.color.BLUE false := .row_2 rfl

-- A partial table has no derivation outside its rows.
example : ¬ ∃ b, SpecTec.«$is_red» SpecTec.color.GREEN b := by
  rintro ⟨b, h⟩
  cases h

-- A parameterless table has a constant fallback selector.
example : SpecTec.«$never:row» = 0 := rfl

example : ¬ ∃ b, SpecTec.«$never» b := by
  rintro ⟨b, h⟩
  cases h

-- Callers: a premise and a function argument.
example : SpecTec.Small_ok SpecTec.ty.S1 := .table _ _ (.row_0 _ rfl) rfl

example : SpecTec.«$wrapped_small» SpecTec.ty.S1 true :=
  .case_1 _ _ (.case_1 _ _ _ (.row_1 _ _ _ rfl (.row_0 _ rfl)))

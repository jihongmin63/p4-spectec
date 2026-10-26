/- Relational ordered execution with a shared fresh supply.
   SpecTecRunEval supplies the optional executable refinement. -/
set_option autoImplicit false

namespace SpecTecExecution

universe u v w

inductive Outcome (α : Type v) where
  | success (value : α)
  | unmatch
  | abort (message : String)
  deriving DecidableEq, Repr

inductive Value : Type 1 where
  | of {α : Type} (value : α)

inductive Action (Request : Type u) : Type (max u 1) where
  | pure {α : Type} (value : α) : Action Request
  | unmatch : Action Request
  | abort (message : String) : Action Request
  | freshId : Action Request
  | call (request : Request) : Action Request
  | choose (α : Type) (allowed : α → Prop) : Action Request
  | guard (condition : Prop) : Action Request
  | bind {α : Type} (plan : Action Request) (next : α → Action Request) : Action Request
  | orElse (plan : Action Request) (next : Unit → Action Request) : Action Request
  | notHold (plan : Action Request) : Action Request

def freshName (supply : Nat) : String := "FRESH__" ++ toString supply

/- Every outcome retains its consumed supply, including failed alternatives.
   Fallback continues from the preceding attempt's final supply. -/
inductive Eval {Request : Type u} (program : Request → Action Request) :
    Action Request → Nat → Outcome Value → Nat → Prop where
  | pure {α : Type} {n : Nat} (value : α) :
      Eval program (.pure value) n (.success (.of value)) n
  | unmatch {n : Nat} : Eval program .unmatch n .unmatch n
  | abort {n : Nat} (message : String) : Eval program (.abort message) n (.abort message) n
  | freshId {n : Nat} : Eval program .freshId n (.success (.of (freshName n))) (n + 1)
  | call {request : Request} {outcome : Outcome Value} {start final : Nat} :
      Eval program (program request) start outcome final →
      Eval program (.call request) start outcome final
  | choose {α : Type} {allowed : α → Prop} {n : Nat} (value : α) : allowed value →
      Eval program (.choose α allowed) n (.success (.of value)) n
  | guard_true {condition : Prop} {n : Nat} : condition →
      Eval program (.guard condition) n (.success (.of ())) n
  | guard_false {condition : Prop} {n : Nat} : ¬ condition →
      Eval program (.guard condition) n .unmatch n
  | bind_success {α : Type} {plan : Action Request} {next : α → Action Request}
      {value : α} {outcome : Outcome Value} {start middle final : Nat} :
      Eval program plan start (.success (.of value)) middle →
      Eval program (next value) middle outcome final →
      Eval program (.bind plan next) start outcome final
  | bind_unmatch {α : Type} {plan : Action Request} {next : α → Action Request} {start final : Nat} :
      Eval program plan start .unmatch final →
      Eval program (.bind plan next) start .unmatch final
  | bind_abort {α : Type} {plan : Action Request} {next : α → Action Request}
      {message : String} {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.bind plan next) start (.abort message) final
  | orElse_success {plan : Action Request} {next : Unit → Action Request} {value : Value}
      {start final : Nat} :
      Eval program plan start (.success value) final →
      Eval program (.orElse plan next) start (.success value) final
  | orElse_unmatch {plan : Action Request} {next : Unit → Action Request} {outcome : Outcome Value}
      {start failedFinal final : Nat} :
      Eval program plan start .unmatch failedFinal →
      Eval program (next ()) failedFinal outcome final →
      Eval program (.orElse plan next) start outcome final
  | orElse_abort {plan : Action Request} {next : Unit → Action Request} {message : String}
      {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.orElse plan next) start (.abort message) final
  | notHold_success {plan : Action Request} {start final : Nat} :
      Eval program plan start .unmatch final →
      Eval program (.notHold plan) start (.success (.of ())) final
  | notHold_unmatch {plan : Action Request} {value : Value} {start final : Nat} :
      Eval program plan start (.success value) final →
      Eval program (.notHold plan) start .unmatch final
  | notHold_abort {plan : Action Request} {message : String} {start final : Nat} :
      Eval program plan start (.abort message) final →
      Eval program (.notHold plan) start (.abort message) final


def require {Request : Type u} (condition : Prop) (message : String) : Action Request :=
  .orElse (.guard condition) (fun () => .abort message)

def tryClauses {Request : Type u} (clauses : List (Action Request)) : Action Request :=
  match clauses with
  | [] => .unmatch
  | clause :: rest => .orElse clause (fun () => tryClauses rest)

variable {Request : Type u} {program : Request → Action Request}

theorem tryClauses_nil (supply : Nat) :
    Eval program (tryClauses ([] : List (Action Request))) supply .unmatch supply :=
  .unmatch

theorem tryClauses_cons_success {clause : Action Request}
    {rest : List (Action Request)} {value : Value} {start final : Nat}
    (h : Eval program clause start (.success value) final) :
    Eval program (tryClauses (clause :: rest)) start (.success value) final :=
  .orElse_success h

theorem tryClauses_cons_unmatch {clause : Action Request}
    {rest : List (Action Request)} {outcome : Outcome Value}
    {start failedFinal final : Nat}
    (h : Eval program clause start .unmatch failedFinal)
    (tail : Eval program (tryClauses rest) failedFinal outcome final) :
    Eval program (tryClauses (clause :: rest)) start outcome final :=
  .orElse_unmatch h tail

theorem tryClauses_cons_abort {clause : Action Request}
    {rest : List (Action Request)} {message : String} {start final : Nat}
    (h : Eval program clause start (.abort message) final) :
    Eval program (tryClauses (clause :: rest)) start (.abort message) final :=
  .orElse_abort h

/-- Every `choose` step used by this derivation admits at most one value. -/
inductive Functional (program : Request → Action Request) : {plan : Action Request} → {start : Nat} →
    {outcome : Outcome Value} → {final : Nat} → Eval program plan start outcome final → Prop where
  | pure {α : Type} {n : Nat} (value : α) : Functional program (Eval.pure (n := n) value)
  | unmatch {n : Nat} : Functional program (Eval.unmatch (n := n))
  | abort {n : Nat} (message : String) : Functional program (Eval.abort (n := n) message)
  | freshId {n : Nat} : Functional program (Eval.freshId (n := n))
  | call {request : Request} {outcome : Outcome Value} {start final : Nat}
      {h : Eval program (program request) start outcome final} :
      Functional program h → Functional program (Eval.call h)
  | choose {α : Type} {allowed : α → Prop} {n : Nat} {value : α} {ok : allowed value} :
      (∀ x y, allowed x → allowed y → x = y) → Functional program (Eval.choose (n := n) value ok)
  | guard_true {condition : Prop} {n : Nat} {h : condition} :
      Functional program (Eval.guard_true (n := n) h)
  | guard_false {condition : Prop} {n : Nat} {h : ¬ condition} :
      Functional program (Eval.guard_false (n := n) h)
  | bind_success {α : Type} {plan : Action Request} {next : α → Action Request} {value : α}
      {outcome : Outcome Value} {start middle final : Nat}
      {h : Eval program plan start (.success (.of value)) middle}
      {k : Eval program (next value) middle outcome final} :
      Functional program h → Functional program k → Functional program (Eval.bind_success h k)
  | bind_unmatch {α : Type} {plan : Action Request} {next : α → Action Request} {start final : Nat}
      {h : Eval program plan start .unmatch final} :
      Functional program h → Functional program (Eval.bind_unmatch (next := next) h)
  | bind_abort {α : Type} {plan : Action Request} {next : α → Action Request} {message : String}
      {start final : Nat} {h : Eval program plan start (.abort message) final} :
      Functional program h → Functional program (Eval.bind_abort (next := next) h)
  | orElse_success {plan : Action Request} {next : Unit → Action Request} {value : Value} {start final : Nat}
      {h : Eval program plan start (.success value) final} :
      Functional program h → Functional program (Eval.orElse_success (next := next) h)
  | orElse_unmatch {plan : Action Request} {next : Unit → Action Request} {outcome : Outcome Value}
      {start failedFinal final : Nat} {h : Eval program plan start .unmatch failedFinal}
      {k : Eval program (next ()) failedFinal outcome final} :
      Functional program h → Functional program k → Functional program (Eval.orElse_unmatch h k)
  | orElse_abort {plan : Action Request} {next : Unit → Action Request} {message : String} {start final : Nat}
      {h : Eval program plan start (.abort message) final} :
      Functional program h → Functional program (Eval.orElse_abort (next := next) h)
  | notHold_success {plan : Action Request} {start final : Nat} {h : Eval program plan start .unmatch final} :
      Functional program h → Functional program (Eval.notHold_success h)
  | notHold_unmatch {plan : Action Request} {value : Value} {start final : Nat}
      {h : Eval program plan start (.success value) final} :
      Functional program h → Functional program (Eval.notHold_unmatch h)
  | notHold_abort {plan : Action Request} {message : String} {start final : Nat}
      {h : Eval program plan start (.abort message) final} :
      Functional program h → Functional program (Eval.notHold_abort h)

/-- A derivation whose choices are functional fixes the outcome and final supply. -/
theorem eval_deterministic
    {plan : Action Request} {start leftFinal rightFinal : Nat} {left right : Outcome Value}
    {a : Eval program plan start left leftFinal} (functional : Functional program a)
    (b : Eval program plan start right rightFinal) : left = right ∧ leftFinal = rightFinal := by
  induction functional generalizing right rightFinal with
  | pure => cases b; exact ⟨rfl, rfl⟩
  | unmatch => cases b; exact ⟨rfl, rfl⟩
  | abort => cases b; exact ⟨rfl, rfl⟩
  | freshId => cases b; exact ⟨rfl, rfl⟩
  | call _ ih => cases b with | call h => exact ih h
  | @choose _ _ _ _ ok det => cases b with
    | choose _ ok' => cases det _ _ ok ok'; exact ⟨rfl, rfl⟩
  | @guard_true _ _ h => cases b with
    | guard_true => exact ⟨rfl, rfl⟩
    | guard_false h' => exact False.elim (h' h)
  | @guard_false _ _ h => cases b with
    | guard_true h' => exact False.elim (h h')
    | guard_false => exact ⟨rfl, rfl⟩
  | bind_success _ _ first second => cases b with
    | bind_success h k =>
      obtain ⟨e, s⟩ := first h
      cases e; cases s; exact second k
    | bind_unmatch h => cases (first h).1
    | bind_abort h => cases (first h).1
  | bind_unmatch _ ih => cases b with
    | bind_success h _ => cases (ih h).1
    | bind_unmatch h => exact ih h
    | bind_abort h => cases (ih h).1
  | bind_abort _ ih => cases b with
    | bind_success h _ => cases (ih h).1
    | bind_unmatch h => cases (ih h).1
    | bind_abort h => exact ih h
  | orElse_success _ ih => cases b with
    | orElse_success h => exact ih h
    | orElse_unmatch h _ => cases (ih h).1
    | orElse_abort h => cases (ih h).1
  | orElse_unmatch _ _ first second => cases b with
    | orElse_success h => cases (first h).1
    | orElse_unmatch h k =>
      obtain ⟨_, supply_eq⟩ := first h
      cases supply_eq
      exact second k
    | orElse_abort h => cases (first h).1
  | orElse_abort _ ih => cases b with
    | orElse_success h => cases (ih h).1
    | orElse_unmatch h _ => cases (ih h).1
    | orElse_abort h => exact ih h
  | notHold_success _ ih => cases b with
    | notHold_success h => exact ⟨rfl, (ih h).2⟩
    | notHold_unmatch h => cases (ih h).1
    | notHold_abort h => cases (ih h).1
  | notHold_unmatch _ ih => cases b with
    | notHold_success h => cases (ih h).1
    | notHold_unmatch h => exact ⟨rfl, (ih h).2⟩
    | notHold_abort h => cases (ih h).1
  | notHold_abort _ ih => cases b with
    | notHold_success h => cases (ih h).1
    | notHold_unmatch h => cases (ih h).1
    | notHold_abort h => exact ih h

theorem supply_monotone {plan : Action Request} {start final : Nat} {outcome : Outcome Value}
    (h : Eval program plan start outcome final) : start ≤ final := by
  induction h with
  | freshId => exact Nat.le_succ _
  | bind_success _ _ first second => exact Nat.le_trans first second
  | orElse_unmatch _ _ first second => exact Nat.le_trans first second
  | call _ ih | bind_unmatch _ ih | bind_abort _ ih | orElse_success _ ih
    | orElse_abort _ ih | notHold_success _ ih | notHold_unmatch _ ih
    | notHold_abort _ ih => exact ih
  | _ => exact Nat.le_refl _

theorem unmatch_excludes_success
    {plan : Action Request} {start failedFinal successFinal : Nat}
    {failed : Eval program plan start .unmatch failedFinal} (functional : Functional program failed)
    (value : Value) :
    ¬ Eval program plan start (.success value) successFinal := by
  intro success
  cases (eval_deterministic functional success).1

/- Failed clauses pass their consumed supply to the next attempt. -/
inductive AllUnmatch (program : Request → Action Request) :
    List (Action Request) → Nat → Nat → Prop where
  | nil {supply : Nat} : AllUnmatch program [] supply supply
  | cons {clause : Action Request} {rest : List (Action Request)}
      {start failedFinal final : Nat} :
      Eval program clause start .unmatch failedFinal →
      AllUnmatch program rest failedFinal final →
      AllUnmatch program (clause :: rest) start final

inductive Selected (program : Request → Action Request) :
    List (Action Request) → Nat → Nat → Value → Nat → Prop where
  | here {clause : Action Request} {rest : List (Action Request)} {value : Value}
      {start final : Nat} :
      Eval program clause start (.success value) final →
      Selected program (clause :: rest) start 0 value final
  | next {clause : Action Request} {rest : List (Action Request)} {index : Nat} {value : Value}
      {start failedFinal final : Nat} :
      Eval program clause start .unmatch failedFinal →
      Selected program rest failedFinal index value final →
      Selected program (clause :: rest) start (index + 1) value final

theorem tryClauses_success_iff (clauses : List (Action Request))
    (start : Nat) (value : Value) (final : Nat) :
    Eval program (tryClauses clauses) start (.success value) final ↔
      ∃ index, Selected program clauses start index value final := by
  induction clauses generalizing start with
  | nil => constructor <;> intro h
           · cases h
           · obtain ⟨_, h⟩ := h; cases h
  | cons clause rest ih =>
    constructor
    · intro h; cases h with
      | orElse_success h => exact ⟨0, .here h⟩
      | orElse_unmatch h k =>
        obtain ⟨i, selected⟩ := (ih _).mp k
        exact ⟨i + 1, .next h selected⟩
    · rintro ⟨i, h⟩; cases h with
      | here h => exact .orElse_success h
      | next h k => exact .orElse_unmatch h ((ih _).mpr ⟨_, k⟩)

@[simp] theorem eval_call_iff {request : Request} {outcome : Outcome Value} {start final : Nat} :
    Eval program (.call request) start outcome final ↔
      Eval program (program request) start outcome final := by
  constructor
  · intro h; cases h with | call h => exact h
  · exact Eval.call

theorem tryClauses_unmatch_iff (clauses : List (Action Request))
    (start final : Nat) :
    Eval program (tryClauses clauses) start .unmatch final ↔
      AllUnmatch program clauses start final := by
  induction clauses generalizing start with
  | nil =>
    constructor
    · intro h; cases h; exact .nil
    · intro h; cases h; exact .unmatch
  | cons clause rest ih =>
    constructor
    · intro h; cases h with
      | orElse_unmatch first tail => exact .cons first ((ih _).mp tail)
    · intro h; cases h with
      | cons first tail => exact .orElse_unmatch first ((ih _).mpr tail)

theorem tryClauses_append_of_unmatch {prior rest : List (Action Request)}
    {outcome : Outcome Value} {start failedFinal final : Nat}
    (failed : Eval program (tryClauses prior) start .unmatch failedFinal)
    (tail : Eval program (tryClauses rest) failedFinal outcome final) :
    Eval program (tryClauses (prior ++ rest)) start outcome final := by
  induction prior generalizing start with
  | nil => cases failed; exact tail
  | cons clause prior ih =>
    cases failed with
    | orElse_unmatch first failed => exact .orElse_unmatch first (ih failed)

end SpecTecExecution

/- Byte operations preserve the backend's existing valid-UTF8 fragment. -/
def specTecTextSlice (text : String) (start length : Nat) : String :=
  (String.fromUTF8? (text.toUTF8.extract start (start + length))).getD ""

abbrev specTecTextSliceValid (text : String) (start length : Nat) : Prop :=
  start + length ≤ text.utf8ByteSize ∧
  (String.fromUTF8? (text.toUTF8.extract start (start + length))).isSome = true

def specTecTextUpdate (text : String) (index : Nat) (replacement : String) : String :=
  specTecTextSlice text 0 index ++ replacement ++
    specTecTextSlice text (index + 1) (text.utf8ByteSize - index - 1)

abbrev specTecTextUpdateValid (text : String) (index : Nat) (replacement : String) : Prop :=
  index < text.utf8ByteSize ∧ replacement.utf8ByteSize = 1 ∧
  specTecTextSliceValid text 0 index ∧ specTecTextSliceValid text index 1 ∧
  specTecTextSliceValid text (index + 1) (text.utf8ByteSize - index - 1)

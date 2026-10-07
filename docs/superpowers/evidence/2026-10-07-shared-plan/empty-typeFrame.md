# Exact full-context generated excerpts: `$empty_typeFrame`

## before / sem

```lean
namespace «$empty_typeFrame:Semantics»

inductive Atom : Type 1 where
  | «$empty_typeFrame» : typeFrame → Atom
  | relation_call {α β : Type} : _root_.SpecTecRelationRef α β → α → β → Atom

def rule_0_plan : SpecTecPlan.Alternative Atom Unit :=
  { sourceIndex := 0, recoverable := [], body := (SpecTecPlan.Plan.at 0 (SpecTecPlan.Plan.externalCall ({ Input := _root_.Unit, Output := (map id varTypeIR), inputPositions := [], policy := .ordered, boundary := .priorSCC, holds := fun () «plan:arg:0» => (@«$empty_map» id varTypeIR «plan:arg:0») } : SpecTecPlan.ExternalSignature) (fun () => ()) (SpecTecPlan.Plan.ret (fun ⟨(), «eval:0»⟩ => (@Atom.«$empty_typeFrame» «eval:0»))))) }

inductive InProgram : SpecTecWFS.Rule Atom → Prop where
  | rule_0 («eval:0» : (map id varTypeIR)) : InProgram ((rule_0_plan).body.compile () ⟨«eval:0», ()⟩)

def metadata : SpecTecWFS.ComponentMetadata :=
  { relations := ["$empty_typeFrame"], dependencies := ["$empty_map"], recursive := false, negativeCycle := false, externalCallback := false }

end «$empty_typeFrame:Semantics»

def «$empty_typeFrame» (arg0 : typeFrame) : Prop :=
  SpecTecWFS.Holds «$empty_typeFrame:Semantics».InProgram (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)

def «$empty_typeFrame».fails (arg0 : typeFrame) : Prop :=
  SpecTecWFS.Fails «$empty_typeFrame:Semantics».InProgram (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)

theorem «$empty_typeFrame».checkedSuccess (arg0 : typeFrame) (same : «$empty_typeFrame:Semantics».Atom → «$empty_typeFrame:Semantics».Atom → Bool) (sameSound : ∀ left right, same left right = true → left = right) (fuel : Nat) (certificate : SpecTecPlan.SuccessCertificate «$empty_typeFrame:Semantics».InProgram) (accepted : SpecTecPlan.checkSuccessWith same fuel certificate = some (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)) : («$empty_typeFrame» arg0) := by
  exact SpecTecPlan.checkSuccessWith_sound same sameSound fuel certificate _ accepted

theorem «$empty_typeFrame».case_1 («eval:0» : (map id varTypeIR)) (h0 : (@«$empty_map» id varTypeIR «eval:0»)) : (SpecTec.«$empty_typeFrame» «eval:0») :=
  SpecTecWFS.Holds.rule _ («$empty_typeFrame:Semantics».InProgram.rule_0 «eval:0»)
    (by dsimp [«$empty_typeFrame:Semantics».rule_0_plan, SpecTecPlan.Plan.compile]; all_goals exact ⟨h0, trivial⟩)
    (by dsimp [«$empty_typeFrame:Semantics».rule_0_plan, SpecTecPlan.Plan.compile, SpecTecWFS.All]; all_goals exact trivial)
    (by dsimp [«$empty_typeFrame:Semantics».rule_0_plan, SpecTecPlan.Plan.compile, SpecTecWFS.All]; all_goals exact trivial)
```

## before / eval

```lean
abbrev «$empty_typeFrame».EvalInput : Type := _root_.Unit

abbrev «$empty_typeFrame».EvalOutput : Type := typeFrame

def «$empty_typeFrame».evalSucceeds : «$empty_typeFrame».EvalInput → «$empty_typeFrame».EvalOutput → Prop
  | (), «eval:arg:0» => («$empty_typeFrame» «eval:arg:0»)

def «$empty_typeFrame».freshSites : List SpecTecFresh.Site := []

def «$empty_typeFrame:eval:rule:0:plan» :
    SpecTecEval.EvalRulePlan «$empty_typeFrame».EvalInput «$empty_typeFrame».EvalOutput «$empty_typeFrame».evalSucceeds := {
  Witness := (_root_.Sigma (fun («eval:0» : (map id varTypeIR)) => _root_.Unit))
  input := fun ⟨«eval:0», _⟩ => ()
  output := fun ⟨«eval:0», _⟩ => «eval:0»
  premises := fun ⟨«eval:0», _⟩ => ([(@«$empty_map».evalSelected id varTypeIR () «eval:0»)] : List Prop)
  recoverable := []
  publicSound := by
    intro witness premiseProof
    rcases witness with ⟨«eval:0», _⟩
    have result := («$empty_typeFrame».case_1 «eval:0» (by simpa only [«$empty_map».evalSucceeds] using («$empty_map».selected_sound (SpecTecEval.Prefix.get premiseProof (position := 0) (by rfl)))))
    simpa only [«$empty_typeFrame».evalSucceeds] using result
}

def «$empty_typeFrame».evalRules : List (SpecTecEval.EvalRulePlan «$empty_typeFrame».EvalInput «$empty_typeFrame».EvalOutput «$empty_typeFrame».evalSucceeds) := [«$empty_typeFrame:eval:rule:0:plan»]

def «$empty_typeFrame».evalUndetermined (_input : «$empty_typeFrame».EvalInput) : Prop := False

def «$empty_typeFrame».evaluator : SpecTecEval.Evaluator «$empty_typeFrame».EvalInput «$empty_typeFrame».EvalOutput «$empty_typeFrame».evalSucceeds :=
  { policy := .ordered, rules := («$empty_typeFrame».evalRules), undetermined := («$empty_typeFrame».evalUndetermined) }

abbrev «$empty_typeFrame».allRulesFailed : «$empty_typeFrame».EvalInput → Prop :=
  SpecTecEval.AllFailed («$empty_typeFrame».evalRules)

abbrev «$empty_typeFrame».evalSelected : «$empty_typeFrame».EvalInput → «$empty_typeFrame».EvalOutput → Prop :=
  SpecTecEval.Selected .ordered («$empty_typeFrame».evalRules)

theorem «$empty_typeFrame».selected_sound {input : «$empty_typeFrame».EvalInput} {output : «$empty_typeFrame».EvalOutput}
    (proof : «$empty_typeFrame».evalSelected input output) :
    «$empty_typeFrame».evalSucceeds input output :=
  SpecTecEval.Selected.sound proof

abbrev «$empty_typeFrame».eval [SpecTecEval.Boundary «$empty_typeFrame».EvalInput _root_.String _root_.String] : _root_.Nat → «$empty_typeFrame».EvalInput → (SpecTecEval.Outcome «$empty_typeFrame».EvalOutput _root_.String _root_.String) → Prop :=
  («$empty_typeFrame».evaluator).Evaluation
```

## before / inv

```lean
theorem «$empty_typeFrame».ruleCases (arg0 : typeFrame) (proof : («$empty_typeFrame» arg0)) :
    let __plan_expected_atom : «$empty_typeFrame:Semantics».Atom := (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)
    (∃ («eval:0» : (map id varTypeIR)), ((@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» «eval:0») = __plan_expected_atom) ∧ ((@«$empty_map» id varTypeIR «eval:0»)) ∧ (True)) := by
  obtain ⟨__plan_rule, __plan_member, __plan_head_eq, __plan_side, __plan_positive, __plan_negative⟩ :=
    SpecTecWFS.Holds.cases proof
  cases __plan_member
  case rule_0 «eval:0» =>
    exact ⟨«eval:0», (by exact __plan_head_eq), __plan_side.1, trivial⟩
  all_goals cases __plan_head_eq
```

## after / sem

```lean
namespace «$empty_typeFrame:Semantics»

inductive Atom : Type 1 where
  | «$empty_typeFrame» : typeFrame → Atom
  | relation_call {α β : Type} : _root_.SpecTecRelationRef α β → α → β → Atom

abbrev «$empty_typeFrame:signature» : SpecTecPlan.Signature Atom :=
  { Input := _root_.Unit, Output := typeFrame, inputPositions := [], policy := .ordered, atom := fun () arg0 => (@Atom.«$empty_typeFrame» arg0) }

def rule_0_plan : SpecTecPlan.Alternative Atom Unit :=
  { sourceIndex := 0, recoverable := [], body := (SpecTecPlan.Plan.at 0 (SpecTecPlan.Plan.bindExternal (@«$empty_map».externalSignature id varTypeIR) (fun () => ()) (fun «eval:0» => (SpecTecPlan.Plan.ret (fun () => (@Atom.«$empty_typeFrame» «eval:0»)))))) }

inductive Allowed : SpecTecPlan.Alternative Atom Unit → Prop where
  | rule_0 : Allowed (rule_0_plan)

abbrev InProgram : SpecTecWFS.Program Atom := SpecTecPlan.ProgramOf Allowed ()

abbrev InProgram.rule_0 := SpecTecPlan.ProgramOf.compiled (allowed := Allowed) (entry := ()) (Allowed.rule_0 )

def metadata : SpecTecWFS.ComponentMetadata :=
  { relations := ["$empty_typeFrame"], dependencies := ["$empty_map"], recursive := false, negativeCycle := false, externalCallback := false }

end «$empty_typeFrame:Semantics»

def «$empty_typeFrame» (arg0 : typeFrame) : Prop :=
  SpecTecWFS.Holds «$empty_typeFrame:Semantics».InProgram (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)

def «$empty_typeFrame».fails (arg0 : typeFrame) : Prop :=
  SpecTecWFS.Fails «$empty_typeFrame:Semantics».InProgram (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)

theorem «$empty_typeFrame».checkedSuccess (arg0 : typeFrame) (same : «$empty_typeFrame:Semantics».Atom → «$empty_typeFrame:Semantics».Atom → Bool) (sameSound : ∀ left right, same left right = true → left = right) (fuel : Nat) (certificate : SpecTecPlan.SuccessCertificate «$empty_typeFrame:Semantics».InProgram) (accepted : SpecTecPlan.checkSuccessWith same fuel certificate = some (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0)) : («$empty_typeFrame» arg0) := by
  exact SpecTecPlan.checkSuccessWith_sound same sameSound fuel certificate _ accepted

theorem «$empty_typeFrame».case_1 («eval:0» : (map id varTypeIR)) (h0 : (@«$empty_map» id varTypeIR «eval:0»)) : (SpecTec.«$empty_typeFrame» «eval:0») :=
  SpecTecPlan.Plan.holds_rule (program := «$empty_typeFrame:Semantics».InProgram) («$empty_typeFrame:Semantics».rule_0_plan).body () ⟨«eval:0», ()⟩ (@«$empty_typeFrame:Semantics».InProgram.rule_0 (⟨«eval:0», ()⟩ : («$empty_typeFrame:Semantics».rule_0_plan).body.Witness))
    (by dsimp [«$empty_typeFrame:Semantics».rule_0_plan, SpecTecPlan.Plan.premises, SpecTecEval.Prefix]; all_goals exact ⟨h0, trivial⟩)
```

## after / eval

```lean
abbrev «$empty_typeFrame».EvalInput : Type := _root_.Unit

abbrev «$empty_typeFrame».EvalOutput : Type := typeFrame

def «$empty_typeFrame».evalSucceeds : «$empty_typeFrame».EvalInput → «$empty_typeFrame».EvalOutput → Prop
  | (), «eval:arg:0» => («$empty_typeFrame» «eval:arg:0»)

def «$empty_typeFrame».freshSites : List SpecTecFresh.Site := []

def «$empty_typeFrame».evaluator : SpecTecEval.Evaluator «$empty_typeFrame».EvalInput «$empty_typeFrame».EvalOutput «$empty_typeFrame».evalSucceeds :=
  SpecTecPlan.evaluator «$empty_typeFrame:Semantics».Allowed («$empty_typeFrame:Semantics».«$empty_typeFrame:signature») [⟨«$empty_typeFrame:Semantics».rule_0_plan, «$empty_typeFrame:Semantics».Allowed.rule_0⟩] _root_.Bool.false

abbrev «$empty_typeFrame».evalRules := («$empty_typeFrame».evaluator).rules

abbrev «$empty_typeFrame».evalUndetermined := («$empty_typeFrame».evaluator).undetermined

abbrev «$empty_typeFrame».allRulesFailed := («$empty_typeFrame».evaluator).AllFailed

abbrev «$empty_typeFrame».evalSelected := («$empty_typeFrame».evaluator).Selected

theorem «$empty_typeFrame».selected_sound {input : «$empty_typeFrame».EvalInput} {output : «$empty_typeFrame».EvalOutput} (proof : «$empty_typeFrame».evalSelected input output) : «$empty_typeFrame».evalSucceeds input output :=
  SpecTecEval.Evaluator.selected_sound (evaluator := («$empty_typeFrame».evaluator)) proof

abbrev «$empty_typeFrame».eval [SpecTecEval.Boundary «$empty_typeFrame».EvalInput _root_.String _root_.String] : _root_.Nat → «$empty_typeFrame».EvalInput → (SpecTecEval.Outcome «$empty_typeFrame».EvalOutput _root_.String _root_.String) → Prop :=
  («$empty_typeFrame».evaluator).Evaluation

abbrev «$empty_typeFrame».externalSignature : SpecTecPlan.ExternalSignature :=
  SpecTecPlan.Signature.evaluated («$empty_typeFrame:Semantics».«$empty_typeFrame:signature») «$empty_typeFrame:Semantics».InProgram («$empty_typeFrame».evaluator)
```

## after / inv

```lean
theorem «$empty_typeFrame».ruleCases (arg0 : typeFrame) (proof : («$empty_typeFrame» arg0)) : SpecTecPlan.Cases «$empty_typeFrame:Semantics».Allowed () (@«$empty_typeFrame:Semantics».Atom.«$empty_typeFrame» arg0) :=
  SpecTecPlan.ProgramOf.holds_cases proof
```

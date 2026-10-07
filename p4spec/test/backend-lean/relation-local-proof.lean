namespace SpecTec

theorem decl_plan_membership_iff
    (rule : SpecTecWFS.Rule «Decl_ok:Semantics».Atom) :
    «Decl_ok:Semantics».InProgram rule ↔
      (∃ n : Nat, rule = («Decl_ok:Semantics».rule_0_plan).body.compile
        () ⟨n, ()⟩) ∨
      (∃ n : Nat, rule = («Decl_ok:Semantics».rule_1_plan).body.compile
        () ⟨n, ()⟩) := by
  constructor
  · intro member
    rcases member with ⟨alternative, member, witness, rfl⟩
    cases member with
    | rule_0 =>
        rcases witness with ⟨n, rest⟩
        cases rest
        exact Or.inl ⟨n, rfl⟩
    | rule_1 =>
        rcases witness with ⟨n, rest⟩
        cases rest
        exact Or.inr ⟨n, rfl⟩
  · intro cases
    rcases cases with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact «Decl_ok:Semantics».InProgram.rule_0 ⟨n, ()⟩
    · exact «Decl_ok:Semantics».InProgram.rule_1 ⟨n, ()⟩

theorem decl_error_inversion (n : Nat)
    (proof : Decl_ok (.ERRORDECLARATION n)) : ∃ m, n = m := by
  obtain ⟨alternative, member, witness, head, premises⟩ := Decl_ok.ruleCases _ proof
  cases member <;> rcases witness with ⟨m, rest⟩ <;> cases rest <;> cases head
  exact ⟨n, rfl⟩

private theorem nat_ok_no_succ (n : Nat) : ¬ Nat_ok (Nat.succ n) := by
  intro proof
  obtain ⟨alternative, member, witness, head, premises⟩ := Nat_ok.ruleCases _ proof
  cases member
  cases witness
  cases head

theorem constant_succ_rejected (n : Nat) :
    ¬ Decl_ok (.CONSTANTDECLARATION (Nat.succ n)) := by
  intro proof
  obtain ⟨alternative, member, witness, head, premises⟩ := Decl_ok.ruleCases _ proof
  cases member <;> rcases witness with ⟨m, rest⟩ <;> cases rest <;> cases head
  exact nat_ok_no_succ n premises.1

private theorem negative_cycle_lower_absent :
    ¬ SpecTecWFS.lower «CycleA:Semantics».InProgram
        («CycleA:Semantics».Atom.CycleA 0) ∧
    ¬ SpecTecWFS.lower «CycleA:Semantics».InProgram
        («CycleA:Semantics».Atom.CycleB 0) := by
  let interpretation : «CycleA:Semantics».Atom → Prop := fun atom =>
    match atom with
    | .CycleA 0 | .CycleB 0 => False
    | _ => True
  have gammaA : SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation
      («CycleA:Semantics».Atom.CycleA 0) :=
    SpecTecWFS.Derives.rule _ («CycleA:Semantics».InProgram.rule_0 ()) trivial
      trivial ⟨by simp [interpretation], trivial⟩
  have gammaB : SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation
      («CycleA:Semantics».Atom.CycleB 0) :=
    SpecTecWFS.Derives.rule _ («CycleA:Semantics».InProgram.rule_1 ()) trivial
      trivial ⟨by simp [interpretation], trivial⟩
  have closed : ∀ rule, «CycleA:Semantics».InProgram rule → rule.side →
      SpecTecWFS.All interpretation rule.positive →
      SpecTecWFS.All
        (fun atom => ¬ SpecTecWFS.gamma «CycleA:Semantics».InProgram interpretation atom)
        rule.negative → interpretation rule.head := by
    intro rule member side positive negative
    rcases member with ⟨alternative, member, witness, rfl⟩
    cases member <;> cases witness <;> simp_all [interpretation, SpecTecWFS.All,
      «CycleA:Semantics».rule_0_plan, «CycleA:Semantics».rule_1_plan,
      SpecTecPlan.Plan.compile]
  have prefixed : ∀ atom,
      SpecTecWFS.alternating «CycleA:Semantics».InProgram interpretation atom →
      interpretation atom := by
    intro atom derived
    exact derived interpretation closed
  constructor <;> intro proof <;> exact proof interpretation prefixed

private theorem negative_cycle_upper_A :
    SpecTecWFS.upper «CycleA:Semantics».InProgram
      («CycleA:Semantics».Atom.CycleA 0) :=
  SpecTecWFS.Derives.rule _ («CycleA:Semantics».InProgram.rule_0 ()) trivial trivial
    ⟨negative_cycle_lower_absent.2, trivial⟩

example : CycleA.undetermined 0 :=
  ⟨negative_cycle_upper_A, negative_cycle_lower_absent.1⟩

example : «$recursive» (.WRAP .ZERO) .ZERO := by
  have base : «$recursive» .ZERO .ZERO := «$recursive».case_1
  have dispatched :=
    «$invoke:Semantics».«dispatch:$recursive» .ZERO .ZERO base
  have invoked := «$invoke».case_1
    (SpecTecRelationRef.named "$recursive") .ZERO .ZERO dispatched
  have forwarded := «$forward».case_1
    (SpecTecRelationRef.named "$recursive") .ZERO .ZERO invoked
  exact «$recursive».case_2 .ZERO .ZERO forwarded

private def errorCertificate (n : Nat) :
    SpecTecPlan.SuccessCertificate «Decl_ok:Semantics».InProgram :=
  .node ((«Decl_ok:Semantics».rule_1_plan).body.compile () ⟨n, ()⟩)
    («Decl_ok:Semantics».InProgram.rule_1 ⟨n, ()⟩)
    (by simp [«Decl_ok:Semantics».rule_1_plan, SpecTecPlan.Plan.compile])
    (by simp [«Decl_ok:Semantics».rule_1_plan, SpecTecPlan.Plan.compile,
      SpecTecWFS.All]) []

example (n : Nat) : Decl_ok (.ERRORDECLARATION n) := by
  exact Decl_ok.checkedSuccess (.ERRORDECLARATION n)
    (fun _ _ => false) (by intro left right accepted; cases accepted)
    1 (errorCertificate n) (by rfl)

end SpecTec

namespace SpecTecPlanFixture

inductive Atom where
  | lookup : Nat → Nat → Atom
  | result : Nat → Nat → Atom
  | freshResult : String → Atom
deriving DecidableEq

def lookup : SpecTecPlan.Signature Atom :=
  { Input := Nat, Output := Nat, inputPositions := [0],
    policy := .nondeterministic,
    atom := Atom.lookup }

example : lookup.inputPositions = [0] := rfl

def plan : SpecTecPlan.Plan Atom Nat :=
  .call lookup id
    (.guard (fun state => state.2 = state.1 + 1)
      (.ret (fun state => Atom.result state.1 state.2)))

private theorem plannedRule : SpecTecPlan.Rules plan 2
    { head := .result 2 3, positive := [.lookup 2 3],
      negative := [], side := (3 = 2 + 1 ∧ True) } := by
  exact ⟨⟨(3 : Nat), ()⟩, rfl⟩

example : SpecTecPlan.Plan.compile plan 2 ⟨(3 : Nat), ()⟩ =
    { head := .result 2 3, positive := [.lookup 2 3],
      negative := [], side := (3 = 2 + 1 ∧ True) } := by
  rfl

private def knownPlan : SpecTecPlan.Plan Atom Nat :=
  .callKnown lookup id (fun input => input + 1)
    (.ret (fun input => Atom.result input (input + 1)))

private def indexedPlan : SpecTecPlan.Plan Atom Nat :=
  .at 7 knownPlan

example : indexedPlan.compile 2 () = knownPlan.compile 2 () := by
  rfl

example : knownPlan.compile 2 () =
    { head := .result 2 3, positive := [.lookup 2 3],
      negative := [], side := True } := by
  rfl

private def negativePlan : SpecTecPlan.Plan Atom Nat :=
  .negative lookup id (fun input => input + 1)
    (.ret (fun input => Atom.result input 0))

example : negativePlan.compile 2 () =
    { head := .result 2 0, positive := [], negative := [.lookup 2 3],
      side := True } := by
  rfl

private def externalSignature : SpecTecPlan.ExternalSignature :=
  { Input := Nat, Output := Nat, inputPositions := [0],
    policy := .nondeterministic, boundary := .priorSCC,
    holds := fun input output => output = input + 1 }

example : externalSignature.boundary = .priorSCC := rfl

private def externalPlan : SpecTecPlan.Plan Atom Nat :=
  .externalCall externalSignature id
    (.ret (fun state => Atom.result state.1 state.2))

example : externalPlan.compile 2 ⟨(3 : Nat), ()⟩ =
    { head := .result 2 3, positive := [], negative := [],
      side := (3 = 2 + 1 ∧ True) } := by
  rfl

private def externalKnownPlan : SpecTecPlan.Plan Atom Nat :=
  .externalKnown externalSignature id (fun input => input + 1)
    (.ret (fun input => Atom.result input (input + 1)))

example : externalKnownPlan.compile 2 () =
    { head := .result 2 3, positive := [], negative := [],
      side := (3 = 2 + 1 ∧ True) } := by
  rfl

private def externalNegativePlan : SpecTecPlan.Plan Atom Nat :=
  .externalNegative externalSignature
    (fun (input output : Nat) => output ≠ input + 1)
    id (fun input => input + 1)
    (.ret (fun input => Atom.result input (input + 1)))

example : externalNegativePlan.compile 2 () =
    { head := .result 2 3, positive := [], negative := [],
      side := (3 ≠ 2 + 1 ∧ True) } := by
  rfl

private def base : SpecTecPlan.Plan Atom Nat :=
  .ret (fun _ => Atom.lookup 2 3)

private def plannedAlternative : SpecTecPlan.Alternative Atom Nat :=
  { sourceIndex := 0, recoverable := [], body := plan }

private def baseAlternative : SpecTecPlan.Alternative Atom Nat :=
  { sourceIndex := 1, recoverable := [], body := base }

private def program : SpecTecWFS.Program Atom :=
  SpecTecPlan.Program [plannedAlternative, baseAlternative] 2

example (rule : SpecTecWFS.Rule Atom) :
    program rule ↔
      ∃ alternative ∈ [plannedAlternative, baseAlternative],
        ∃ witness : alternative.body.Witness,
          alternative.body.compile 2 witness = rule := by
  exact SpecTecPlan.Program.compiled_iff

example : SpecTecWFS.Holds program (.result 2 3) := by
  have lookupHolds : SpecTecWFS.Holds program (.lookup 2 3) := by
    apply SpecTecWFS.Holds.rule (program := program)
      { head := Atom.lookup 2 3, positive := [], negative := [], side := True }
    · exact ⟨baseAlternative, by simp, (), rfl⟩
    · trivial
    · trivial
    · trivial
  apply SpecTecWFS.Holds.rule (program := program)
    { head := Atom.result 2 3, positive := [Atom.lookup 2 3],
      negative := [], side := (3 = 2 + 1 ∧ True) }
  · exact ⟨plannedAlternative, by simp, plannedRule⟩
  · exact ⟨rfl, trivial⟩
  · exact ⟨lookupHolds, trivial⟩
  · trivial

example (proof : SpecTecWFS.Holds program (.result 2 3)) :
    ∃ alternative ∈ [plannedAlternative, baseAlternative],
      ∃ witness : alternative.body.Witness,
        (alternative.body.compile 2 witness).head = .result 2 3 := by
  change SpecTecWFS.Holds
    (SpecTecPlan.Program [plannedAlternative, baseAlternative] 2)
    (.result 2 3) at proof
  obtain ⟨alternative, member, witness, head, _, _, _⟩ :=
    SpecTecPlan.Program.holds_cases proof
  exact ⟨alternative, member, witness, head⟩

private def freshSite : SpecTecFresh.Site :=
  { relation := "fixture", rule := 0, premise := 0 }

private def root : SpecTecFresh.Supply := SpecTecFresh.Supply.root []

private def freshPlan : SpecTecPlan.Plan Atom SpecTecFresh.Supply :=
  .fresh (fun _ => freshSite) id
    (.ret (fun state => Atom.freshResult state.2.1))

private def freshKnownPlan : SpecTecPlan.Plan Atom String :=
  .freshKnown (fun _ => freshSite) (fun _ => root) id
    (fun _ => root.record freshSite 0)
    (.ret Atom.freshResult)

example : freshKnownPlan.compile (SpecTecFresh.freshText 0) () =
    { head := .freshResult (SpecTecFresh.freshText 0), positive := [],
      negative := [], side :=
        SpecTecFresh.Allocates freshSite root (SpecTecFresh.freshText 0)
          (root.record freshSite 0) ∧ True } := by
  rfl

private def freshAlternative :
    SpecTecPlan.Alternative Atom SpecTecFresh.Supply :=
  { sourceIndex := 0, recoverable := [], body := freshPlan }

private def freshProgram : SpecTecWFS.Program Atom :=
  SpecTecPlan.Program [freshAlternative] root

example : SpecTecWFS.Holds freshProgram (.freshResult (SpecTecFresh.freshText 0)) := by
  apply SpecTecWFS.Holds.rule (program := freshProgram)
    { head := .freshResult (SpecTecFresh.freshText 0), positive := [],
      negative := [], side :=
        SpecTecFresh.Allocates freshSite root (SpecTecFresh.freshText 0)
          (root.record freshSite 0) ∧ True }
  · exact ⟨freshAlternative, by simp,
      ((SpecTecFresh.freshText 0, root.record freshSite 0), ()), rfl⟩
  · exact ⟨SpecTecFresh.Allocates.record 0
      (by decide) (by decide) (by decide) (by decide), trivial⟩
  · trivial
  · trivial

private def baseRule : SpecTecWFS.Rule Atom :=
  { head := .lookup 2 3, positive := [], negative := [], side := True }

private def resultRule : SpecTecWFS.Rule Atom :=
  { head := .result 2 3, positive := [.lookup 2 3], negative := [],
    side := (3 = 2 + 1 ∧ True) }

private def baseCertificate : SpecTecPlan.SuccessCertificate program :=
  .node baseRule (by exact ⟨baseAlternative, by simp, (), rfl⟩)
    trivial trivial []

private def resultCertificate : SpecTecPlan.SuccessCertificate program :=
  .node resultRule (by exact ⟨plannedAlternative, by simp, plannedRule⟩)
    ⟨rfl, trivial⟩ trivial [baseCertificate]

private def missingChild : SpecTecPlan.SuccessCertificate program :=
  .node resultRule (by exact ⟨plannedAlternative, by simp, plannedRule⟩)
    ⟨rfl, trivial⟩ trivial []

private def wrongChild : SpecTecPlan.SuccessCertificate program :=
  .node resultRule (by exact ⟨plannedAlternative, by simp, plannedRule⟩)
    ⟨rfl, trivial⟩ trivial [resultCertificate]

example : SpecTecPlan.checkSuccess 2 resultCertificate = some (.result 2 3) := by
  rfl

example : SpecTecPlan.checkSuccess 2 missingChild = none := by
  rfl

example : SpecTecPlan.checkSuccess 3 wrongChild = none := by
  rfl

private def exactMatch (left right : Atom) : Bool := decide (left = right)

example : SpecTecPlan.checkSuccessWith exactMatch 2 resultCertificate =
    some (Atom.result 2 3) := by
  rfl

example : SpecTecWFS.Holds program (.result 2 3) := by
  apply SpecTecPlan.checkSuccessWith_sound exactMatch
    (by intro left right accepted; simpa [exactMatch] using accepted)
    2 resultCertificate
  rfl

example : SpecTecPlan.checkSuccess 2 baseCertificate ≠ some (.result 2 3) := by
  decide

example : SpecTecWFS.Holds program (.result 2 3) := by
  apply SpecTecPlan.checkSuccess_sound 2 resultCertificate
  rfl

example {Env First Second : Type} (next :
    SpecTecPlan.Plan Atom ((Env × First) × Second))
    (env : Env) (first : First) (second : Second)
    (witness : next.Witness) :
    (SpecTecPlan.Plan.splitPair next).compile
      (env, (first, second)) witness =
      next.compile ((env, first), second) witness := by
  rfl

end SpecTecPlanFixture

#print axioms SpecTecPlan.Program.compiled_iff
#print axioms SpecTecPlan.Program.holds_cases
#print axioms SpecTecPlan.checkSuccess_sound
#print axioms SpecTecPlan.checkSuccessWith_sound
#print axioms SpecTec.Decl_ok.checkedSuccess
#print axioms SpecTec.decl_plan_membership_iff
#print axioms SpecTec.decl_error_inversion
#print axioms SpecTec.constant_succ_rejected

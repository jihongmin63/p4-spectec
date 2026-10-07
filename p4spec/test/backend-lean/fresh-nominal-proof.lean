namespace SpecTec


attribute [local simp] SpecTecPlan.evaluator SpecTecPlan.Alternative.toEvalRule SpecTecPlan.Plan.compile SpecTecPlan.Plan.premises SpecTecPlan.Plan.Witness SpecTecPlan.ExternalSignature.selected «$fresh_typeId:supply:Semantics».rule_0_plan «$fresh_typeId:Semantics».rule_0_plan «$nominal_once:supply:Semantics».rule_0_plan «$nominal_once:fail:Semantics».rule_0_plan «$nominal_once:Semantics».rule_0_plan «$nominal_pair:supply:Semantics».rule_0_plan «$nominal_pair:fail:Semantics».rule_0_plan «$nominal_pair:Semantics».rule_0_plan «$nominal_after_failure:fail:0:Semantics».rule_0_plan «$nominal_after_failure:supply:Semantics».rule_0_plan «$nominal_after_failure:supply:Semantics».rule_1_plan «$nominal_after_failure:fail:Semantics».rule_0_plan «$nominal_after_failure:Semantics».rule_0_plan «$nominal_recurse:match:0:Semantics».rule_0_plan «$nominal_recurse:fail:0:Semantics».rule_0_plan «$nominal_recurse:supply:Semantics».rule_0_plan «$nominal_recurse:supply:Semantics».rule_1_plan «$nominal_recurse:fail:1:Semantics».rule_0_plan «$nominal_recurse:fail:1:Semantics».rule_1_plan «$nominal_recurse:fail:Semantics».rule_0_plan «$nominal_recurse:Semantics».rule_0_plan «$nominal_repeat:supply:Semantics».rule_0_plan «$nominal_repeat:fail:Semantics».rule_0_plan «$nominal_repeat:Semantics».rule_0_plan «$fresh_typeId».evaluator «$nominal_once».evaluator «$nominal_pair».evaluator «$nominal_after_failure».evaluator «$nominal_recurse».evaluator «$nominal_repeat».evaluator «$fresh_typeId».evalRules «$nominal_once».evalRules «$nominal_pair».evalRules «$nominal_after_failure».evalRules «$nominal_recurse».evalRules «$nominal_repeat».evalRules

open SpecTecFresh

example {output : String} (proof : Allocated output) :
    ∃ n : Nat, output = freshText n :=
  proof.numeric

example (site : Site) (path : List Nat) (n : Nat) :
    AllocatedAt site path (freshText n) :=
  allocatedAt_of_text site path 0 n

example : ¬ Allocated "ordinary" := by
  intro proof
  rcases proof.numeric with ⟨number, equal⟩
  have chars := congrArg String.toList equal.symm
  simp [freshText, String.toList_append] at chars

example (site : Site) (path : List Nat) :
    ¬ AllocatedAt site path "ordinary" := by
  intro proof
  have allocated := proof.toAllocated
  rcases allocated.numeric with ⟨number, equal⟩
  have chars := congrArg String.toList equal.symm
  simp [freshText, String.toList_append] at chars

private def siteA : Site :=
  { relation := "$nominal_pair", rule := 0, premise := 0 }

private def siteB : Site :=
  { relation := "$nominal_pair", rule := 0, premise := 1 }

private def rootSupply : Supply := Supply.root ["FRESH__0", "ordinary"]

example : (rootSupply.allocate siteA).1 ≠
    ((rootSupply.allocate siteA).2.allocate siteB).1 :=
  Supply.sequential_ids_distinct siteA siteB rootSupply

example : (rootSupply.allocate siteA).2.protectedNames =
    rootSupply.protectedNames :=
  Supply.allocate_preserves_protected siteA rootSupply

example : FreshName.ordinary "FRESH__0" ≠
    FreshName.allocated (rootSupply.nextId siteA) :=
  FreshName.ordinary_ne_allocated _ _

example : (Supply.enter 0 rootSupply).nextId siteA ≠
    (Supply.enter 1 rootSupply).nextId siteA := by
  simp [Supply.enter, Supply.nextId, rootSupply]

example : BranchResult.committedSupply rootSupply
    (BranchResult.recoverableFailure :
      BranchResult FreshName String String) = rootSupply :=
  BranchResult.rollback rootSupply

example : ¬ BranchResult.mayTryNext
    (BranchResult.abort "stop" : BranchResult FreshName String String) :=
  BranchResult.abort_stops "stop"

private def identityAlpha : AlphaRenaming where
  toFun := id
  invFun := id
  leftInv := by intro value; rfl
  rightInv := by intro value; rfl

private def repeatedId : FreshId :=
  { site := siteA, path := [0, 2], occurrence := 3 }

example : AlphaList identityAlpha
    [.allocated repeatedId, .allocated repeatedId]
    [.allocated repeatedId, .allocated repeatedId] := by
  exact ⟨rfl, rfl, trivial⟩

example : Observation.supportedNominally .captureAvoidance := by
  trivial

example : ¬ Observation.supportedNominally .concatenation := by
  intro proof
  exact proof

private def pairRoot : Supply := Supply.root []

private def pairAfterA : Supply :=
  Supply.record siteA pairRoot 0

private def pairAfterB : Supply :=
  Supply.record siteB pairAfterA 1

private theorem siteA_text :
    Allocates siteA pairRoot "FRESH__0" pairAfterA := by
  exact Allocates.record 0 (by decide) (by decide) (by decide) (by decide)

example (rendering : Rendering pairAfterA) :
    rendering.render (pairRoot.nextId siteA) = freshText 0 :=
  rendering.agreesAssigned _ _ (by decide)

example {after : Supply}
    (proof : Allocates siteB pairAfterA "FRESH__0" after) : False := by
  exact proof.output_ne_existing siteA_text.recorded rfl

private theorem siteB_text :
    Allocates siteB pairAfterA "FRESH__1" pairAfterB := by
  exact Allocates.record 1 (by decide) (by decide) (by decide) (by decide)

private theorem pair_supply :
    «$nominal_pair:supply» pairRoot
      ("FRESH__0", "FRESH__1") pairAfterB := by
  exact «$nominal_pair:supply».case_1 pairRoot "FRESH__0" "FRESH__1"
    pairAfterA pairAfterB siteA_text siteB_text

example : «$nominal_pair».evalSelected () ("FRESH__0", "FRESH__1") := by
  apply SpecTecEval.Selected.here
  exact ⟨⟨(("FRESH__0", "FRESH__1"), pairAfterB), ()⟩,
    rfl, ⟨pair_supply, trivial⟩⟩

end SpecTec

#print axioms SpecTecFresh.Allocated.numeric

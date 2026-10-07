namespace SpecTec

open SpecTecFresh

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

private theorem siteA_text :
    AllocatedAt siteA [] "nominal-A" :=
  allocatedAt_of_text siteA [] 0 "nominal-A"

private theorem siteB_text :
    AllocatedAt siteB [] "nominal-B" :=
  allocatedAt_of_text siteB [] 0 "nominal-B"

example : «$nominal_pair».evalSelected () ("nominal-A", "nominal-B") := by
  constructor
  · trivial
  · exact ⟨"nominal-A", "nominal-B", rfl, rfl,
      siteA_text, siteB_text, trivial⟩

end SpecTec

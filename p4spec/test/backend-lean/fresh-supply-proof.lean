namespace SpecTec
open SpecTecFresh

example {site : Site} {before after : Supply} {output : String}
    (proof : Allocates site before output after) :
    ∃ n : Nat, output = freshText n :=
  proof.numeric

example (site : Site) (before after : Supply) :
    ¬ Allocates site before "ordinary" after := by
  intro proof
  rcases proof.numeric with ⟨number, equal⟩
  have chars := congrArg String.toList equal.symm
  simp [freshText, String.toList_append] at chars

private def protectedSupply : Supply := Supply.root ["ordinary"]
private def protectedNumber : Supply := Supply.root ["FRESH__0"]
private def siteA : Site := { relation := "Program_ok", rule := 0, premise := 0 }
private def siteB : Site := { relation := "Program_ok", rule := 0, premise := 1 }
private def assignedWithoutUse : Supply :=
  { (Supply.root []) with assigned := [((Supply.root []).nextId siteA, 0)] }
private def contextSite : Site :=
  { relation := "Context_ok", rule := 0, premise := 0 }

example {after : Supply}
    (proof : Allocates siteA protectedNumber "FRESH__0" after) : False := by
  exact proof.output_ne_protected (by decide) rfl

example : Allocates siteA protectedNumber "FRESH__1"
    (protectedNumber.record siteA 1) := by
  exact Allocates.record 1 (by decide) (by decide) (by decide) (by decide)

example {after : Supply}
    (proof : Allocates siteA assignedWithoutUse "FRESH__1" after) : False := by
  exact proof.newAssignment 0 (by decide)

private def contextRoot : Supply := Supply.root
  (FreshProtectedRelation_9f0f524e4d24bf288f1705ee511a418c
    (context.CONTEXT "ordinary"))

example : contextRoot.protectedNames = ["ordinary"] := by
  simp [contextRoot, FreshProtectedRelation_9f0f524e4d24bf288f1705ee511a418c,
    FreshProtect_context, Supply.root]

example {after : Supply}
    (proof : Allocates contextSite contextRoot "ordinary" after) : False := by
  exact proof.output_ne_protected
    (by simp [contextRoot,
      FreshProtectedRelation_9f0f524e4d24bf288f1705ee511a418c,
      FreshProtect_context, Supply.root]) rfl

private def afterA : Supply :=
  Supply.record siteA protectedSupply 0

private def afterB : Supply :=
  Supply.record siteB afterA 1

example : Allocates siteA protectedSupply "FRESH__0" afterA := by
  exact Allocates.record 0 (by decide) (by decide) (by decide) (by decide)

example : Allocates siteB afterA "FRESH__1" afterB := by
  exact Allocates.record 1 (by decide) (by decide) (by decide) (by decide)

example (proof : Allocates siteA protectedSupply "FRESH__0" afterA) :
    "FRESH__0" ≠ "ordinary" := by
  exact proof.output_ne_protected (by simp [protectedSupply, Supply.root])

example (first : String) (middle : Supply)
    (one : Allocates siteA protectedSupply first middle)
    (second : String) (final : Supply)
    (two : Allocates siteB middle second final) : first ≠ second := by
  exact (two.output_ne_existing one.recorded).symm

private def afterComposite : Supply :=
  Supply.recordDerived afterB (afterA.nextId siteB) "ordinary_FRESH__1"

example : Derives afterB "FRESH__1" "ordinary_FRESH__1" afterComposite := by
  exact Derives.record (afterA.nextId siteB)
    (by decide)
    (by decide) (by decide)

example (proof : Derives afterB "FRESH__1" "ordinary_FRESH__1"
    afterComposite) : "ordinary_FRESH__1" ≠ "ordinary" := by
  exact proof.output_ne_protected
    (by simp [afterB, afterA, protectedSupply, Supply.root, Supply.record])

example : (Supply.enter 3 protectedSupply).path = [3] := by
  rfl

example : Supply.leave protectedSupply (Supply.enter 3 protectedSupply) =
    protectedSupply := by
  rfl

end SpecTec

#print axioms SpecTecFresh.Allocates.numeric

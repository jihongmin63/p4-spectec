namespace SpecTec
open SpecTecFresh

private def protectedSupply : Supply := Supply.root ["ordinary"]
private def siteA : Site := { relation := "Program_ok", rule := 0, premise := 0 }
private def siteB : Site := { relation := "Program_ok", rule := 0, premise := 1 }
private def contextSite : Site :=
  { relation := "Context_ok", rule := 0, premise := 0 }

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
  Supply.record siteA protectedSupply "generated-a"

private def afterB : Supply :=
  Supply.record siteB afterA "generated-b"

example : Allocates siteA protectedSupply "generated-a" afterA := by
  exact Allocates.record (by decide) (by decide)

example : Allocates siteB afterA "generated-b" afterB := by
  exact Allocates.record (by decide) (by decide)

example (proof : Allocates siteA protectedSupply "generated-a" afterA) :
    "generated-a" ≠ "ordinary" := by
  exact proof.output_ne_protected (by simp [protectedSupply, Supply.root])

example (first : String) (middle : Supply)
    (one : Allocates siteA protectedSupply first middle)
    (second : String) (final : Supply)
    (two : Allocates siteB middle second final) : first ≠ second := by
  exact (two.output_ne_existing one.recorded).symm

private def afterComposite : Supply :=
  Supply.recordDerived afterB (afterA.nextId siteB) "ordinary_generated-b"

example : Derives afterB "generated-b" "ordinary_generated-b" afterComposite := by
  exact Derives.record (afterA.nextId siteB)
    (by simp [afterB, afterA, Supply.record])
    (by decide) (by decide)

example (proof : Derives afterB "generated-b" "ordinary_generated-b"
    afterComposite) : "ordinary_generated-b" ≠ "ordinary" := by
  exact proof.output_ne_protected
    (by simp [afterB, afterA, protectedSupply, Supply.root, Supply.record])

example : (Supply.enter 3 protectedSupply).path = [3] := by
  rfl

example : Supply.leave protectedSupply (Supply.enter 3 protectedSupply) =
    protectedSupply := by
  rfl

end SpecTec

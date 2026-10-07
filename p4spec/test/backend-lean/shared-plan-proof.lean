namespace SharedPlanTest
open SpecTecPlan

inductive Atom where
  | input : Nat → Atom
  | forbidden : Nat → Atom
  | result : Nat → Nat → Atom
  deriving DecidableEq

abbrev sig : Signature Atom :=
  { Input := Nat, Output := Nat, inputPositions := [0],
    policy := .ordered, atom := Atom.result }

def plan : Plan Atom Nat :=
  .choose (.at 0 (.guard (fun e => e.2 = e.1 + 1)
    (.at 1 (.callKnown
      { Input := Nat, Output := Unit, inputPositions := [0],
        policy := .ordered, atom := fun n _ => .input n }
      Prod.fst (fun _ => ())
      (.at 2 (.negative
        { Input := Nat, Output := Unit, inputPositions := [0],
          policy := .ordered, atom := fun n _ => .forbidden n }
        Prod.snd (fun _ => ())
        (.ret (fun e => .result e.1 e.2))))))))

example (positive negative : Atom → Prop) :
    plan.premises false positive negative 2 (3, ()) =
      [3 = 2 + 1, positive (.input 2), negative (.forbidden 3)] := rfl

example (positive negative : Atom → Prop) :
    SpecTecEval.Prefix (plan.premises false positive negative 2 (3, ())) ↔
      (plan.compile 2 (3, ())).side ∧
      SpecTecWFS.All positive (plan.compile 2 (3, ())).positive ∧
      SpecTecWFS.All negative (plan.compile 2 (3, ())).negative :=
  plan.premises_iff positive negative 2 (3, ())

example (positive negative : Atom → Prop) :
    ¬ SpecTecEval.Prefix (plan.premises false positive negative 2 (9, ())) := by
  intro proof
  have bad : 9 = 2 + 1 := proof.1
  contradiction

def alt : Alternative Atom Nat := ⟨0, [0], plan⟩
def allowed : Alternative Atom Nat → Prop := fun alternative => alternative = alt
def program : SpecTecWFS.Program Atom := ProgramOf allowed 2

example (rule : SpecTecWFS.Rule Atom) :
    program rule ↔ ∃ alternative, allowed alternative ∧
      ∃ witness : alternative.body.Witness,
        alternative.body.compile 2 witness = rule := ProgramOf.compiled_iff

/-- A hand-written WFS rule, independent of the compiler's record construction. -/
def expectedRule (value : Nat) : SpecTecWFS.Rule Atom :=
  { head := .result 2 value, positive := [.input 2],
    negative := [.forbidden value], side := value = 2 + 1 ∧ True }

example (rule : SpecTecWFS.Rule Atom) :
    program rule ↔ ∃ value, rule = expectedRule value := by
  constructor
  · rintro ⟨alternative, member, witness, compiled⟩
    change alternative = alt at member
    cases member
    rcases witness with ⟨value, rest⟩
    cases rest
    exact ⟨value, compiled.symm⟩
  · rintro ⟨value, rfl⟩
    exact ProgramOf.compiled (allowed := allowed) (entry := 2) rfl (value, ())

/-- The external callback boundary's extra terminal True changes no rule. -/
example (f : Nat → Nat → Prop) (input output : Nat) :
    (Plan.guard (fun _ : Unit => f input output)
      (.ret (fun _ => Atom.result input output))).compile () () =
      { head := Atom.result input output, positive := [], negative := [],
        side := f input output } := by
  simp [Plan.compile]


example (h : SpecTecWFS.Holds program (.result 2 3)) :
    ∃ alternative, allowed alternative ∧
      ∃ witness : alternative.body.Witness,
        (alternative.body.compile 2 witness).head = .result 2 3 ∧
        SpecTecEval.Prefix (alternative.body.premises false
          (SpecTecWFS.Holds program) (SpecTecWFS.Fails program) 2 witness) :=
  ProgramOf.holds_cases h

def single : Alternative Atom Unit :=
  ⟨0, [0], .choose (.guard (fun e => e.2 = 3)
    (.ret (fun e => .result 2 e.2)))⟩
def singleton : SpecTecWFS.Program Atom := ProgramOf (fun a => a = single) ()
def evaluated := single.toEvalRule () sig singleton
  (fun witness => ProgramOf.compiled (allowed := fun a => a = single) (entry := ()) rfl witness)

example : evaluated.Succeeds 2 3 := ⟨(3, ()), rfl, rfl, trivial⟩
example : ¬ evaluated.Succeeds 2 9 := by
  rintro ⟨⟨value, rest⟩, head, premises⟩
  have eq : value = 9 := (Atom.result.inj head).2
  have correct : value = 3 := premises.1
  omega

example : SpecTecWFS.Holds singleton (.result 2 3) :=
  SpecTecEval.EvalRulePlan.Succeeds.sound (plan := evaluated)
    (show evaluated.Succeeds 2 3 from ⟨(3, ()), rfl, rfl, trivial⟩)

/-- A public external success does not bypass ordered selection. -/
abbrev blockedExternal : ExternalSignature :=
  { Input := Unit, Output := Nat, inputPositions := [], policy := .ordered,
    boundary := .priorSCC, holds := fun _ _ => True,
    selection := some ⟨(fun _ _ => False), fun _ _ impossible => impossible.elim⟩ }

def externalPlan : Plan Atom Unit :=
  .bind (fun (input : Nat) =>
    .bindExternal blockedExternal (fun _ => ())
      (fun output => .ret (fun _ => .result input output)))

example : SpecTecEval.Prefix
    (externalPlan.premises false (fun _ => True) (fun _ => True) () ⟨2, 3, ()⟩) :=
  ⟨trivial, trivial⟩
example : ¬ SpecTecEval.Prefix
    (externalPlan.premises true (fun _ => True) (fun _ => True) () ⟨2, 3, ()⟩) := by
  intro proof
  exact proof.1

def site : SpecTecFresh.Site := ⟨"shared-fixture", 0, 0⟩
def root : SpecTecFresh.Supply := SpecTecFresh.Supply.root []
def allocation : Plan Atom Unit :=
  .bindFresh (fun _ => site) (fun _ => root)
    (fun _ _ => .ret (fun _ => .input 0))

example : ¬ SpecTecEval.Prefix
    (allocation.premises true (fun _ => True) (fun _ => True) ()
      ⟨"FRESH__0", root, ()⟩) := by
  intro proof
  have recorded := proof.1.recorded
  simp [root, SpecTecFresh.Supply.root] at recorded

example : ¬ SpecTecEval.Prefix
    (allocation.premises false (fun _ => True) (fun _ => True) ()
      ⟨"ordinary", root.record site 0, ()⟩) := by
  intro proof
  obtain ⟨n, equal⟩ := proof.1.numeric
  have chars := congrArg String.toList equal.symm
  simp [SpecTecFresh.freshText, String.toList_append] at chars

#print axioms SpecTecPlan.Alternative.toEvalRule
#print axioms SpecTecPlan.ProgramOf.holds_cases
#print axioms SpecTecPlan.Plan.premises_iff
#print axioms SpecTecPlan.Plan.eval_premises_sound
end SharedPlanTest

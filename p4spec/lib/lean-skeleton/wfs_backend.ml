let source = {lean|
set_option autoImplicit false

universe u

namespace SpecTecWFS

structure Rule (Atom : Type u) where
  head : Atom
  positive : List Atom
  negative : List Atom
  side : Prop

abbrev Program (Atom : Type u) := Rule Atom → Prop
abbrev Interpretation (Atom : Type u) := Atom → Prop

def All {Atom : Type u} (P : Atom → Prop) : List Atom → Prop
  | [] => True
  | atom :: rest => P atom ∧ All P rest

theorem All.map {Atom : Type u} {P Q : Atom → Prop}
    (step : ∀ atom, P atom → Q atom) {atoms : List Atom}
    (proof : All P atoms) : All Q atoms := by
  induction atoms with
  | nil => trivial
  | cons atom rest ih =>
      exact ⟨step atom proof.1, ih proof.2⟩

def Derives {Atom : Type u} (program : Program Atom)
    (negative : Interpretation Atom) (atom : Atom) : Prop :=
  ∀ interpretation : Interpretation Atom,
    (∀ rule : Rule Atom, program rule → rule.side →
      All interpretation rule.positive →
      All (fun negativeAtom => ¬ negative negativeAtom) rule.negative →
      interpretation rule.head) → interpretation atom

def gamma {Atom : Type u} (program : Program Atom)
    (negative : Interpretation Atom) : Interpretation Atom :=
  Derives program negative

theorem Derives.rule {Atom : Type u} {program : Program Atom}
    {negative : Interpretation Atom} (rule : Rule Atom)
    (inProgram : program rule) (side : rule.side)
    (positive : All (Derives program negative) rule.positive)
    (failures : All (fun atom => ¬ negative atom) rule.negative) :
    Derives program negative rule.head := by
  intro interpretation closed
  exact closed rule inProgram side
    (All.map (fun atom proof => proof interpretation closed) positive) failures

theorem Derives.cases {Atom : Type u} {program : Program Atom}
    {negative : Interpretation Atom} {atom : Atom}
    (proof : Derives program negative atom) :
    ∃ rule : Rule Atom, program rule ∧ rule.head = atom ∧ rule.side ∧
      All (Derives program negative) rule.positive ∧
      All (fun other => ¬ negative other) rule.negative := by
  let witnesses : Interpretation Atom := fun other =>
    ∃ rule : Rule Atom, program rule ∧ rule.head = other ∧ rule.side ∧
      All (Derives program negative) rule.positive ∧
      All (fun next => ¬ negative next) rule.negative
  have lowerWitness : ∀ other, witnesses other → Derives program negative other := by
    intro other witness
    obtain ⟨rule, inProgram, equal, side, positive, failures⟩ := witness
    exact equal ▸ Derives.rule rule inProgram side positive failures
  apply proof witnesses
  intro rule inProgram side positive failures
  exact ⟨rule, inProgram, rfl, side,
    All.map (fun other witness => lowerWitness other witness) positive, failures⟩

theorem gamma_antitone {Atom : Type u} (program : Program Atom)
    {left right : Interpretation Atom}
    (subset : ∀ atom, left atom → right atom) :
    ∀ atom, gamma program right atom → gamma program left atom := by
  intro atom proof interpretation closed
  apply proof interpretation
  intro rule inProgram side positive failures
  exact closed rule inProgram side positive
    (All.map (fun atom absent present => absent (subset atom present)) failures)

def alternating {Atom : Type u} (program : Program Atom)
    (interpretation : Interpretation Atom) : Interpretation Atom :=
  gamma program (gamma program interpretation)

theorem alternating_mono {Atom : Type u} (program : Program Atom)
    {left right : Interpretation Atom}
    (subset : ∀ atom, left atom → right atom) :
    ∀ atom, alternating program left atom → alternating program right atom :=
  gamma_antitone program (gamma_antitone program subset)

def lower {Atom : Type u} (program : Program Atom) : Interpretation Atom :=
  fun atom => ∀ interpretation : Interpretation Atom,
    (∀ other, alternating program interpretation other → interpretation other) →
    interpretation atom

theorem lower_prefixed {Atom : Type u} (program : Program Atom) :
    ∀ atom, alternating program (lower program) atom → lower program atom := by
  intro atom proof interpretation closed
  exact closed atom
    (alternating_mono program (fun other h => h interpretation closed) atom proof)

theorem lower_postfixed {Atom : Type u} (program : Program Atom) :
    ∀ atom, lower program atom → alternating program (lower program) atom := by
  intro atom proof
  apply proof (alternating program (lower program))
  exact alternating_mono program (lower_prefixed program)

theorem lower_fixed {Atom : Type u} (program : Program Atom) (atom : Atom) :
    lower program atom ↔ alternating program (lower program) atom :=
  ⟨lower_postfixed program atom, lower_prefixed program atom⟩

def upper {Atom : Type u} (program : Program Atom) : Interpretation Atom :=
  gamma program (lower program)

theorem lower_le_upper {Atom : Type u} (program : Program Atom) :
    ∀ atom, lower program atom → upper program atom := by
  intro atom proof
  apply proof (upper program)
  intro other derived
  exact gamma_antitone program (lower_postfixed program) other derived

def Holds {Atom : Type u} (program : Program Atom) (atom : Atom) : Prop :=
  lower program atom

def Fails {Atom : Type u} (program : Program Atom) (atom : Atom) : Prop :=
  ¬ upper program atom

def Undetermined {Atom : Type u} (program : Program Atom) (atom : Atom) : Prop :=
  upper program atom ∧ ¬ lower program atom

theorem Holds.not_fails {Atom : Type u} {program : Program Atom}
    {atom : Atom} (proof : Holds program atom) : ¬ Fails program atom :=
  fun failed => failed (lower_le_upper program atom proof)

theorem Holds.sound {Atom : Type u} {program : Program Atom}
    {atom : Atom} {interpretation : Interpretation Atom}
    (proof : Holds program atom)
    (closed : ∀ rule : Rule Atom, program rule → rule.side →
      All interpretation rule.positive →
      All (Fails program) rule.negative → interpretation rule.head) :
    interpretation atom :=
  lower_postfixed program atom proof interpretation closed

theorem Holds.cases {Atom : Type u} {program : Program Atom}
    {atom : Atom} (proof : Holds program atom) :
    ∃ rule : Rule Atom, program rule ∧ rule.head = atom ∧ rule.side ∧
      All (Holds program) rule.positive ∧
      All (Fails program) rule.negative := by
  obtain ⟨rule, inProgram, equal, side, positive, failures⟩ :=
    Derives.cases (lower_postfixed program atom proof)
  exact ⟨rule, inProgram, equal, side,
    All.map (fun other witness => lower_prefixed program other witness) positive,
    failures⟩

theorem Holds.not_of_rules {Atom : Type u} {program : Program Atom}
    (atom : Atom)
    (closed : ∀ rule : Rule Atom, program rule → rule.side →
      All (fun other => other ≠ atom) rule.positive →
      All (Fails program) rule.negative → rule.head ≠ atom) :
    ¬ Holds program atom := by
  intro proof
  exact Holds.sound (interpretation := fun other => other ≠ atom) proof closed rfl

theorem Holds.rule {Atom : Type u} {program : Program Atom}
    (rule : Rule Atom) (inProgram : program rule) (side : rule.side)
    (positive : All (Holds program) rule.positive)
    (failures : All (Fails program) rule.negative) :
    Holds program rule.head := by
  apply lower_prefixed program
  exact Derives.rule rule inProgram side
    (All.map (fun atom proof => lower_postfixed program atom proof) positive)
    failures

/-- Compose a new invariant with facts already proved about the same program.
    Negative premises retain their WFS meaning; they are not mere absence of Holds. -/
theorem Holds.sound_with {Atom : Type u} {program : Program Atom}
    {atom : Atom} {P Q : Interpretation Atom}
    (proof : Holds program atom)
    (known : ∀ other, Holds program other → Q other)
    (closed : ∀ rule, program rule → rule.side →
      All P rule.positive → All Q rule.positive →
      All (Fails program) rule.negative → P rule.head) : P atom := by
  have both : Holds program atom ∧ P atom := by
    apply Holds.sound (interpretation := fun a => Holds program a ∧ P a) proof
    intro rule member side positive negative
    exact ⟨Holds.rule rule member side (All.map (fun _ h => h.1) positive) negative,
      closed rule member side (All.map (fun _ h => h.2) positive)
        (All.map (fun a h => known a h.1) positive) negative⟩
  exact both.2

/-- A successful judgement has an enabled rule with successful premises. -/
theorem Holds.iff_rule {Atom : Type u} {program : Program Atom} {atom : Atom} :
    Holds program atom ↔ ∃ rule, program rule ∧ rule.head = atom ∧ rule.side ∧
      All (Holds program) rule.positive ∧ All (Fails program) rule.negative := by
  constructor
  · exact Holds.cases
  · rintro ⟨rule, member, head, side, positive, negative⟩
    exact head ▸ Holds.rule rule member side positive negative

/-- Refute a judgement using its possible last rules, without claiming WFS falsity. -/
theorem Holds.reject {Atom : Type u} {program : Program Atom} {atom : Atom}
    (impossible : ∀ rule, program rule → rule.head = atom → rule.side →
      All (Holds program) rule.positive → All (Fails program) rule.negative → False) :
    ¬ Holds program atom := by
  intro proof
  obtain ⟨rule, member, head, side, positive, negative⟩ := Holds.cases proof
  exact impossible rule member head side positive negative

theorem gamma_positive {Atom : Type u} (program : Program Atom)
    (positiveProgram : ∀ rule, program rule → rule.negative = [])
    (left right : Interpretation Atom) (atom : Atom) :
    gamma program left atom ↔ gamma program right atom := by
  constructor
  · intro proof interpretation closed
    apply proof interpretation
    intro rule inProgram side positives failures
    exact closed rule inProgram side positives
      (by simp [positiveProgram rule inProgram, All])
  · intro proof interpretation closed
    apply proof interpretation
    intro rule inProgram side positives failures
    exact closed rule inProgram side positives
      (by simp [positiveProgram rule inProgram, All])

theorem Holds.positive_iff_derives {Atom : Type u}
    (program : Program Atom)
    (positiveProgram : ∀ rule, program rule → rule.negative = [])
    (atom : Atom) :
    Holds program atom ↔ gamma program (fun _ => False) atom := by
  constructor
  · intro proof
    exact (gamma_positive program positiveProgram (upper program)
      (fun _ => False) atom).mp (lower_postfixed program atom proof)
  · intro proof
    apply lower_prefixed program
    exact (gamma_positive program positiveProgram (fun _ => False)
      (upper program) atom).mp proof

end SpecTecWFS
|lean}

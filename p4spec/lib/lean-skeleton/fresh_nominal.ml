module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

exception Unsupported of string

let source = {lean|
set_option autoImplicit false

namespace SpecTecFresh

def freshText (n : Nat) : String := "FRESH__" ++ Nat.repr n

/-- A static allocation point.  Dynamic call and iteration positions live in
    `FreshId.path`, rather than in a program-wide counter. -/
structure Site where
  relation : String
  rule : Nat
  premise : Nat
deriving DecidableEq, Repr

structure FreshId where
  site : Site
  path : List Nat
  occurrence : Nat
deriving DecidableEq, Repr

/-- Ordinary source names and allocated identities are disjoint even when a
    later renderer happens to choose the same text. -/
inductive FreshName where
  | ordinary : String → FreshName
  | allocated : FreshId → FreshName
deriving DecidableEq, Repr

structure Supply where
  path : List Nat
  used : List FreshId
  assigned : List (FreshId × Nat) := []
  rendered : List (FreshId × String) := []
  protectedNames : List String
deriving Repr

def Supply.root (protectedNames : List String) : Supply :=
  { path := [], used := [], rendered := [], protectedNames }

def Supply.enter (position : Nat) (supply : Supply) : Supply :=
  { supply with path := supply.path ++ [position] }

/-- Return from a dynamic call without discarding its committed allocations. -/
def Supply.leave (entry result : Supply) : Supply :=
  { result with path := entry.path }

def Supply.nextId (site : Site) (supply : Supply) : FreshId :=
  { site, path := supply.path, occurrence := supply.used.length }

def Supply.allocate (site : Site) (supply : Supply) : FreshName × Supply :=
  let fresh := supply.nextId site
  (.allocated fresh, { supply with used := fresh :: supply.used })

/-- Record the concrete spelling selected for a new nominal identity. -/
def Supply.record (site : Site) (supply : Supply) (number : Nat) : Supply :=
  let fresh := supply.nextId site
  { supply with
    used := fresh :: supply.used
    assigned := (fresh, number) :: supply.assigned
    rendered := (fresh, freshText number) :: supply.rendered }

/-- Record another spelling derived from an already allocated identity. -/
def Supply.recordDerived (supply : Supply) (fresh : FreshId)
    (output : String) : Supply :=
  { supply with rendered := (fresh, output) :: supply.rendered }

/-- Allocation is globally fresh for this execution and avoids every ordinary
    name collected at the public entry point. -/
inductive Allocates (site : Site) (before : Supply) :
    String → Supply → Prop where
  | record (number : Nat)
      (newId : before.nextId site ∉ before.used)
      (unassigned : before.nextId site ∉ before.assigned.map Prod.fst)
      (notProtected : freshText number ∉ before.protectedNames)
      (notRendered : ∀ entry ∈ before.rendered,
        entry.2 ≠ freshText number) :
      Allocates site before (freshText number) (before.record site number)

theorem Allocates.newAssignment {site before output after}
    (proof : Allocates site before output after) (previous : Nat)
    (member : (before.nextId site, previous) ∈ before.assigned) : False := by
  cases proof with
  | record _ _ unassigned _ _ =>
      apply unassigned
      exact List.mem_map_of_mem member

theorem Allocates.numeric {site before output after}
    (proof : Allocates site before output after) :
    ∃ number, output = freshText number := by
  cases proof with
  | record number _ _ _ _ => exact ⟨number, rfl⟩

theorem Allocates.output_ne_protected {site before output after}
    (proof : Allocates site before output after) {ordinary : String}
    (member : ordinary ∈ before.protectedNames) : output ≠ ordinary := by
  cases proof with
  | record _ _ _ notProtected _ =>
      intro equal
      subst ordinary
      exact notProtected member

theorem Allocates.output_ne_existing {site before output after}
    (proof : Allocates site before output after) {fresh : FreshId}
    {existing : String} (member : (fresh, existing) ∈ before.rendered) :
    output ≠ existing := by
  cases proof with
  | record _ _ _ _ notRendered =>
      intro equal
      exact notRendered (fresh, existing) member equal.symm

theorem Allocates.recorded {site before output after}
    (proof : Allocates site before output after) :
    (before.nextId site, output) ∈ after.rendered := by
  cases proof
  simp [Supply.record]

theorem Allocates.assigned {site before output after}
    (proof : Allocates site before output after) :
    ∃ number, (before.nextId site, number) ∈ after.assigned ∧
      output = freshText number := by
  cases proof with
  | record number _ _ _ _ =>
      exact ⟨number, by simp [Supply.record], rfl⟩

/-- A rendering-sensitive constructor may add a spelling only when it is
    linked to an existing identity and preserves the same collision boundary. -/
inductive Derives (before : Supply) (source output : String) : Supply → Prop where
  | record (fresh : FreshId)
      (sourceRecorded : (fresh, source) ∈ before.rendered)
      (notProtected : output ∉ before.protectedNames)
      (notRendered : ∀ entry ∈ before.rendered, entry.2 ≠ output) :
      Derives before source output (before.recordDerived fresh output)

theorem Derives.output_ne_protected {before source output after}
    (proof : Derives before source output after) {ordinary : String}
    (member : ordinary ∈ before.protectedNames) : output ≠ ordinary := by
  cases proof with
  | record _ _ notProtected _ =>
      intro equal
      subst ordinary
      exact notProtected member

theorem Derives.same_identity {before source output after}
    (proof : Derives before source output after) :
    ∃ fresh, (fresh, source) ∈ before.rendered ∧
      (fresh, output) ∈ after.rendered := by
  cases proof with
  | record fresh sourceRecorded _ _ =>
      exact ⟨fresh, sourceRecorded, by simp [Supply.recordDerived]⟩

theorem Supply.allocate_name (site : Site) (supply : Supply) :
    (supply.allocate site).1 = .allocated (supply.nextId site) := by
  rfl

theorem Supply.allocate_preserves_protected (site : Site) (supply : Supply) :
    (supply.allocate site).2.protectedNames = supply.protectedNames := by
  rfl

theorem Supply.sequential_ids_distinct (site₁ site₂ : Site) (supply : Supply) :
    (supply.allocate site₁).1 ≠
      ((supply.allocate site₁).2.allocate site₂).1 := by
  simp [Supply.allocate, Supply.nextId]

theorem FreshName.ordinary_ne_allocated (name : String) (fresh : FreshId) :
    FreshName.ordinary name ≠ FreshName.allocated fresh := by
  intro equal
  cases equal

/-- A renderer is an explicit boundary certificate.  It must avoid every
    protected ordinary spelling and be injective over allocated identities. -/
structure Rendering (supply : Supply) where
  render : FreshId → String
  numeric : ∀ fresh, ∃ number, render fresh = freshText number
  agreesAssigned : ∀ fresh number,
    (fresh, number) ∈ supply.assigned → render fresh = freshText number
  avoidsProtected : ∀ fresh, fresh ∈ supply.used →
    render fresh ∉ supply.protectedNames
  injectiveOnUsed : ∀ left, left ∈ supply.used → ∀ right,
    right ∈ supply.used → render left = render right → left = right

def FreshName.renderWith {supply : Supply} (rendering : Rendering supply) :
    FreshName → String
  | .ordinary name => name
  | .allocated fresh => rendering.render fresh

theorem FreshName.rendered_fresh_avoids_protected {supply : Supply}
    (rendering : Rendering supply) (fresh : FreshId) :
    fresh ∈ supply.used →
    FreshName.renderWith rendering (.allocated fresh) ∉ supply.protectedNames :=
  rendering.avoidsProtected fresh

/-- Public allocation has a numeric spelling, while the particular number
    remains a relational choice subject to the supply's collision checks. -/
def Allocated (output : String) : Prop :=
  ∃ (supply : Supply) (rendering : Rendering supply) (fresh : FreshId),
    fresh ∈ supply.used ∧ rendering.render fresh = output

theorem Allocated.numeric {output : String} (proof : Allocated output) :
    ∃ number, output = freshText number := by
  rcases proof with ⟨_, rendering, fresh, _, equal⟩
  rcases rendering.numeric fresh with ⟨number, rendered⟩
  exact ⟨number, equal.symm.trans rendered⟩

def AllocatedAt (site : Site) (path : List Nat) (output : String) : Prop :=
  ∃ (supply : Supply) (rendering : Rendering supply) (occurrence : Nat),
    supply.path = path ∧
    { site, path, occurrence } ∈ supply.used ∧
    rendering.render { site, path, occurrence } = output

theorem AllocatedAt.toAllocated {site : Site} {path : List Nat}
    {output : String} (proof : AllocatedAt site path output) : Allocated output := by
  rcases proof with
    ⟨supply, rendering, occurrence, pathEqual, used, outputEqual⟩
  exact ⟨supply, rendering, { site, path, occurrence }, used, outputEqual⟩

def singletonSupply (site : Site) (path : List Nat) (occurrence : Nat) : Supply :=
  { path, used := [{ site, path, occurrence }], assigned := [], rendered := [],
    protectedNames := [] }

def singletonRendering (site : Site) (path : List Nat) (occurrence : Nat)
    (number : Nat) : Rendering (singletonSupply site path occurrence) where
  render := fun _ => freshText number
  numeric := by intro _; exact ⟨number, rfl⟩
  agreesAssigned := by simp [singletonSupply]
  avoidsProtected := by simp [singletonSupply]
  injectiveOnUsed := by
    intro left leftUsed right rightUsed equal
    simp [singletonSupply] at leftUsed rightUsed
    exact leftUsed.trans rightUsed.symm

theorem allocatedAt_of_text (site : Site) (path : List Nat) (occurrence : Nat)
    (number : Nat) : AllocatedAt site path (freshText number) := by
  let fresh : FreshId := { site, path, occurrence }
  exact ⟨singletonSupply site path occurrence,
    singletonRendering site path occurrence number, occurrence,
    rfl, by simp [singletonSupply], rfl⟩

inductive BranchResult (α : Type) (Error : Type) (Feature : Type) where
  | success : α → Supply → BranchResult α Error Feature
  | recoverableFailure : BranchResult α Error Feature
  | abort : Error → BranchResult α Error Feature
  | unsupported : Feature → BranchResult α Error Feature
  | timeout : BranchResult α Error Feature

def BranchResult.committedSupply {α Error Feature} (entry : Supply) :
    BranchResult α Error Feature → Supply
  | .success _ finalSupply => finalSupply
  | .recoverableFailure | .abort _ | .unsupported _ | .timeout => entry

def BranchResult.mayTryNext {α Error Feature} :
    BranchResult α Error Feature → Prop
  | .recoverableFailure => True
  | _ => False

theorem BranchResult.rollback {α Error Feature} (entry : Supply) :
    committedSupply entry
      (recoverableFailure : BranchResult α Error Feature) = entry := by
  rfl

theorem BranchResult.commit {α Error Feature} (entry finalSupply : Supply)
    (value : α) :
    committedSupply entry
      (success value finalSupply : BranchResult α Error Feature) = finalSupply := by
  rfl

theorem BranchResult.abort_stops {α Error Feature} (error : Error) :
    ¬ mayTryNext (abort error : BranchResult α Error Feature) := by
  intro proof
  exact proof

structure AlphaRenaming where
  toFun : FreshId → FreshId
  invFun : FreshId → FreshId
  leftInv : Function.LeftInverse invFun toFun
  rightInv : Function.RightInverse invFun toFun

def AlphaRenaming.apply (mapping : AlphaRenaming) : FreshName → FreshName
  | .ordinary name => .ordinary name
  | .allocated fresh => .allocated (mapping.toFun fresh)

def AlphaName (mapping : AlphaRenaming) (left right : FreshName) : Prop :=
  mapping.apply left = right

def AlphaList (mapping : AlphaRenaming) :
    List FreshName → List FreshName → Prop
  | [], [] => True
  | left :: lefts, right :: rights =>
      AlphaName mapping left right ∧ AlphaList mapping lefts rights
  | _, _ => False

theorem AlphaRenaming.fixes_ordinary (mapping : AlphaRenaming) (name : String) :
    mapping.apply (.ordinary name) = .ordinary name := by
  rfl

theorem AlphaRenaming.consistent_repetition (mapping : AlphaRenaming)
    (fresh : FreshId) :
    AlphaName mapping (.allocated fresh) (.allocated (mapping.toFun fresh)) ∧
    AlphaName mapping (.allocated fresh) (.allocated (mapping.toFun fresh)) := by
  exact ⟨rfl, rfl⟩

/-- Operations that inspect rendered text need a separate compatibility proof.
    Equality used only for binding/scope remains nominal. -/
inductive Observation where
  | nominalEquality
  | binding
  | scope
  | captureAvoidance
  | concatenation
  | lexicalOrder
  | printedControl
  | sortedSet
deriving DecidableEq, Repr

def Observation.supportedNominally : Observation → Prop
  | .nominalEquality | .binding | .scope | .captureAvoidance => True
  | .concatenation | .lexicalOrder | .printedControl | .sortedSet => False

structure CompatibleObservation (observation : Observation)
    (supply : Supply) where
  rendering : Rendering supply
  preserves : Prop

end SpecTecFresh

namespace SpecTec

abbrev FreshSupply := _root_.SpecTecFresh.Supply
abbrev FreshSite := _root_.SpecTecFresh.Site

end SpecTec
|lean}

let target_name = function L.Global name -> Some name | L.Local _ -> None

let rec term_variables = function
  | L.Variable (name, _) -> StringSet.singleton name
  | term -> List.fold_left (fun names child ->
      StringSet.union names (term_variables child)) StringSet.empty
      (Traversal.term_children term)

(* Structural cardinality observes the container shape, not the spelling of an
   identifier stored inside it.  Keep the identity taint for later elements,
   but do not misclassify list bounds as lexical name observations. *)
let rec observable_variables = function
  | L.Native ("List.length", _) -> StringSet.empty
  | L.Variable (name, _) -> StringSet.singleton name
  | term -> List.fold_left (fun names child ->
      StringSet.union names (observable_variables child)) StringSet.empty
      (Traversal.term_children term)

let unsafe_native name =
  List.exists (fun fragment ->
    let length = String.length fragment in
    let rec contains index =
      if index + length > String.length name then false
      else if String.sub name index length = fragment then true
      else contains (index + 1)
    in contains 0)
    ["compare"; "sort"; "repr"; "print"]

let rec text_like_term = function
  | L.Text _ -> true
  | L.Variable (_, (L.BuiltinType ("String", []) | L.Name _)) -> true
  | L.Typed (term, _) -> text_like_term term
  | L.Binary ("++", left, _) -> text_like_term left
  | _ -> false

let unsafe_term tainted =
  let observes term =
    not (StringSet.is_empty
      (StringSet.inter tainted (observable_variables term))) in
  let rec inspect = function
    | L.Binary ("++", left, right) as term
      when observes term && (text_like_term left || text_like_term right) ->
        Some ("string concatenation", left, right)
    | L.Binary (("<" | "<=" | ">" | ">=") as operator, left, right) as term
      when observes term ->
        Some ("lexical comparison " ^ operator, left, right)
    | L.Native (name, _) as term
      when unsafe_native name
        && observes term ->
        Some ("render-observing operation " ^ name, term, term)
    | term -> List.find_map inspect (Traversal.term_children term)
  in
  fun term -> Option.map (fun (reason, _, _) -> reason) (inspect term)

let rec declarations = function
  | L.Single declaration -> [ declaration ]
  | L.Mutual declarations -> declarations
  | L.DerivingDecidableEq group -> declarations group
  | L.ManualDecidableEq _ | L.ManualPrinter _ -> []

let relation_name = function
  | L.Relation { name; _ } -> name
  | _ -> invalid_arg "expected relation"

let relation_table (program : L.program) =
  program |> List.concat_map declarations
  |> List.filter (function L.Relation _ -> true | _ -> false)
  |> List.map (fun declaration -> relation_name declaration, declaration)
  |> List.to_seq |> StringMap.of_seq

let output_positions = function
  | L.Relation { argument_types; input_positions; _ } ->
      let inputs = Option.value input_positions
        ~default:(List.init (max 0 (List.length argument_types - 1)) Fun.id) in
      List.init (List.length argument_types) Fun.id
      |> List.filter (fun position -> not (List.mem position inputs))
  | _ -> []

let application_outputs table (application : L.application) =
  match target_name application.target with
  | Some target ->
      (match StringMap.find_opt target table with
      | Some declaration ->
          application.arguments
          |> List.filteri (fun position _ ->
               List.mem position (output_positions declaration))
      | None -> [])
  | None -> []

let application_produces summaries (application : L.application) =
  match target_name application.target with
  | Some "$fresh_typeId" -> true
  | Some target -> StringSet.mem target summaries
  | None -> false

let add_variables tainted term =
  StringSet.union tainted (term_variables term)

let propagate_prop tainted = function
  | L.Predicate (L.Native
      (("SpecTecFresh.Allocates" | "_root_.SpecTecFresh.Allocates"),
       [ _site; _before; output; _after ])) ->
      add_variables tainted output
  | L.Predicate (L.Native
      (("SpecTecFresh.Derives" | "_root_.SpecTecFresh.Derives"),
       [ _before; _source; output; _after ])) ->
      add_variables tainted output
  | L.Comparison (L.Eq, left, right) ->
      let left_tainted = not (StringSet.is_empty
        (StringSet.inter tainted (term_variables left))) in
      let right_tainted = not (StringSet.is_empty
        (StringSet.inter tainted (term_variables right))) in
      let tainted = if left_tainted then add_variables tainted right else tainted in
      if right_tainted then add_variables tainted left else tainted
  | _ -> tainted

let rule_taint table summaries (rule : L.rule) =
  List.fold_left (fun tainted premise ->
    match premise with
    | L.Holds application when application_produces summaries application ->
        List.fold_left add_variables tainted (application_outputs table application)
    | L.Prop proposition -> propagate_prop tainted proposition
    | L.Holds _ | L.NotHolds _ | L.NotExists _ -> tainted)
    StringSet.empty rule.premises

let relation_produces table summaries = function
  | L.Relation ({ rules; _ } as relation) ->
      let outputs = output_positions (L.Relation relation) in
      List.exists (fun (rule : L.rule) ->
        let tainted = rule_taint table summaries rule in
        rule.conclusion.arguments
        |> List.filteri (fun position _ -> List.mem position outputs)
        |> List.exists (fun term -> not (StringSet.is_empty
             (StringSet.inter tainted (term_variables term))))) rules
  | _ -> false

let fresh_summaries table =
  let rec close summaries =
    let next = StringMap.fold (fun name declaration result ->
      if StringSet.mem name result || relation_produces table summaries declaration
      then StringSet.add name result else result) table summaries in
    if StringSet.equal summaries next then summaries else close next
  in
  close (StringSet.singleton "$fresh_typeId")

let unsafe_application tainted (application : L.application) =
  let tainted_argument = List.exists (fun term ->
    not (StringSet.is_empty (StringSet.inter tainted (term_variables term))))
    application.arguments in
  match target_name application.target with
  | Some target when tainted_argument &&
      (target = "$print_" || target = "$concat_text" || target = "$join_text"
       || target = "$add_set" || target = "$adds_set"
       || target = "$sort" || target = "$compare") ->
      Some ("call to " ^ target)
  | _ -> None

let unsafe_prop tainted proposition =
  let unsafe = unsafe_term tainted in
  let comparison = match proposition with
    | L.Comparison ((L.Lt | L.Le | L.Gt | L.Ge), left, right) ->
        let term = L.Tuple (left, right) in
        if StringSet.is_empty
             (StringSet.inter tainted (observable_variables term))
        then None else Some "ordered comparison"
    | _ -> None in
  match comparison with
  | Some _ as found -> found
  | None -> List.find_map unsafe (Traversal.prop_terms proposition)

let audit_rule table summaries relation (rule : L.rule) =
  let derives_output output = function
    | L.Prop (L.Predicate (L.Native
        (("SpecTecFresh.Derives" | "_root_.SpecTecFresh.Derives"),
         [ _before; _source; derived; _after ]))) ->
        derived = output
    | _ -> false in
  let rec premises tainted position = function
    | [] ->
        List.find_map (unsafe_term tainted) rule.conclusion.arguments
        |> Option.map (fun reason -> position, reason)
    | premise :: rest ->
        let unsafe = match premise with
          | L.Prop proposition -> unsafe_prop tainted proposition
          | L.Holds application | L.NotHolds (application, _)
          | L.NotExists (_, application, _) ->
              (match unsafe_application tainted application with
              | Some _ when target_name application.target = Some "$concat_text"
                  && List.exists (fun output ->
                    match rest with
                    | certificate :: _ -> derives_output output certificate
                    | [] -> false) (application_outputs table application) ->
                  None
              | Some _ as found -> found
              | None -> List.find_map (unsafe_term tainted) application.arguments)
        in
        (match unsafe with
        | Some reason -> Some (position, reason)
        | None ->
            let tainted = match premise with
              | L.Holds application when application_produces summaries application ->
                  List.fold_left add_variables tainted
                    (application_outputs table application)
              | L.Prop proposition -> propagate_prop tainted proposition
              | L.Holds _ | L.NotHolds _ | L.NotExists _ -> tainted
            in premises tainted (position + 1) rest)
  in
  match premises StringSet.empty 0 rule.premises with
  | None -> Ok ()
  | Some (position, reason) ->
      Error (Printf.sprintf
        "fresh-derived text reaches %s in relation %s, rule %s, premise/output %d; \
         use --fresh-exact-counter or provide a rendering compatibility proof"
        reason relation rule.name position)

let audit (program : L.program) : (unit, string) result =
  let table = relation_table program in
  let summaries = fresh_summaries table in
  let failures = program |> List.concat_map declarations
    |> List.concat_map (function
         | L.Relation { name; rules; _ } ->
             List.filter_map (fun rule ->
               match audit_rule table summaries name rule with
               | Ok () -> None
               | Error message -> Some message) rules
         | _ -> [])
    |> List.sort_uniq String.compare in
  match failures with
  | [] -> Ok ()
  | failures ->
      Error (Printf.sprintf "%d unproved rendering observation(s):\n- %s"
        (List.length failures) (String.concat "\n- " failures))

import Lean

/- Optional proof authoring support. The generated semantics need not import Lean. -/
namespace SpecTecProof
open Lean Elab Command Meta

/-- Prove an invariant of a translated program with bounded closure lemmas.

Each handler receives `rule`, `member`, `_side`, `_positive`, and `_negative`.
With `using known_sound`, `_known` contains that theorem's conclusions on the
positive premises. `default` is mandatory; other handlers name leaf membership
types. No membership branch is skipped, including external-call rules.

Example (after importing this module and the generated semantics):

    spec_invariant invariant_sound for InProgram : invariant using known_sound where
      default => by cases member <;> exact True.intro
      «InProgram:0:4» => by
        cases member <;> simp_all [invariant, SpecTecWFS.All]

Omit `using` when no previous invariant is needed. For an unsplit program the
handler key is `InProgram` itself. Keys refer to the current generated program;
stale or unused keys are errors. Generated closure lemmas are private, but the
named result is reusable: `invariant_sound atom proof`. Keep the source predicate
generic in inputs, outputs and fresh counters when proving a reusable property.
Section parameters and hypotheses in `using` are retained. As with ordinary
Lean theorems, explicitly `include` section hypotheses used only in handlers.
The handler binder names above, plus `atom`, `proof`, `_known` and `_derivations`,
are reserved: avoid those names for section parameters used by the command.

For leaves without an explicit handler, a generated `head_property` theorem is
reused when the invariant reduces to True on every head. Its proof is checked
once with the semantics; the default tactic only handles the remaining leaves.
-/
syntax (name := specInvariant)
  "spec_invariant " ident " for " ident " : " term
  (" using " term)? " where" (ppLine ident " => " term)+ : command

private def source (stx : Syntax) : CommandElabM String :=
  match stx.reprint with
  | some s => pure s
  | none => throwErrorAt stx "cannot reprint invariant proof syntax"

private def elaborate (code : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command code with
  | .error e => throwError "invalid generated closure declaration: {e}"
  | .ok stx =>
      elabCommand stx
      if ← MonadLog.hasErrors then
        throwError "spec_invariant: closure proof failed"

private def resolve (id : Syntax) : CommandElabM Name :=
  liftCoreM <| realizeGlobalConstNoOverloadWithInfo id

/-- `using` is part of the command's interface, so its section hypotheses must
    also parameterize the generated declarations, even if absent from the goal. -/
private def knownParameters (known : Option (TSyntax `term)) : CommandElabM (List Name) := do
  let some known := known | return []
  let scope ← getScope
  runTermElabM fun _ => do
    let value ← Term.elabTerm known none
    Term.synthesizeSyntheticMVarsNoPostponing
    let free := (collectFVars {} (← instantiateMVars value)).fvarSet
    let sectionVars := (← readThe Term.Context).sectionFVars
    return scope.varUIds.toList.filter fun uid =>
      match sectionVars.find? uid with
      | some (.fvar id) => free.contains id
      | _ => false

private def children (name : Name) : CommandElabM (Array (Name × Name)) := do
  let info ← getConstInfoInduct name
  if info.ctors.isEmpty then return #[]
  let isGroup := info.ctors.all fun c => c.getString!.startsWith "group:"
  if !isGroup then return #[]
  info.ctors.toArray.mapM fun ctor => do
    let c ← getConstInfoCtor ctor
    if c.numFields != 1 && c.numFields != 2 then
      throwError "unsupported membership wrapper {ctor}: expected rule and child"
    let child ← liftTermElabM <| forallTelescope c.type fun xs _ => do
      let t ← inferType xs.back!
      match t.getAppFn with
      | .const n _ => pure n
      | _ => throwError "unsupported membership wrapper {ctor}"
    pure (ctor, child)

private structure Settings where
  program : String
  predicate : String
  known : Option String
  fallback : String
  handlers : Array (Name × String)
  stem : Name

private structure Generation where
  next : Nat := 0
  used : Array Name := #[]

private def parameters (s : Settings) (group : Name) : String :=
  " (rule : SpecTecWFS.Rule _) (member : " ++ group.toString ++ " rule)" ++
  " (_side : rule.side) (_positive : SpecTecWFS.All (" ++ s.predicate ++ ") rule.positive)" ++
  " (_negative : SpecTecWFS.All (SpecTecWFS.Fails " ++ s.program ++ ") rule.negative)" ++
  (if s.known.isSome then
    " (_derivations : SpecTecWFS.All (SpecTecWFS.Holds " ++ s.program ++ ") rule.positive)"
   else "") ++ " : (" ++ s.predicate ++ ") rule.head"

private def arguments (s : Settings) (member : String) : String :=
  " rule " ++ member ++ " _side _positive _negative" ++
    (if s.known.isSome then " _derivations" else "")

/-- Section parameters precede the generated rule binders. Preserve them by name,
    including proof hypotheses that cannot be inferred from the result type. -/
private def application (name : Name) (s : Settings) (member : String) : CommandElabM String := do
  let info ← getConstInfo (← resolve (mkIdent name))
  let rec captures : Expr → String
    | .forallE binder _ body kind =>
        if binder == `rule then ""
        else (if kind == .instImplicit then "" else
          " (" ++ binder.toString ++ " := " ++ binder.toString ++ ")") ++ captures body
    | _ => ""
  return name.toString ++ captures info.type ++ arguments s member

/-- Use only definitional truth, so no rule premise or WFS obligation is dropped.
    Older generated modules and user-defined programs can use the default tactic. -/
private def trivialHeads (s : Settings) (group : Name) : CommandElabM (Option String) := do
  let lemma := group ++ `head_property
  unless (← getEnv).contains lemma do return none
  let call := lemma.toString ++ " (" ++ s.predicate ++ ")"
  let result ← runTermElabM fun _ => do
    let stx ← match Parser.runParserCategory (← getEnv) `term call with
      | .ok stx => pure stx
      | .error error => throwError "invalid head property application: {error}"
    let value ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    forallTelescope (← inferType value) fun xs _ => do
      let mut count := 0
      for x in xs do
        if (← x.fvarId!.getDecl).userName.getString!.startsWith "head:case:" then
          let trivial ← forallTelescope (← inferType x) fun _ conclusion =>
            withTransparency .default <| isDefEq conclusion (mkConst ``True)
          unless trivial do return none
          count := count + 1
      return some count
  return result.map fun count =>
    "by\n  exact " ++ call ++
    String.join (List.replicate count " (by intros; exact True.intro)") ++ " member"

private partial def generate (s : Settings) (group : Name) (path : List Name) :
    StateT Generation CommandElabM Name := do
  if path.contains group then throwError "recursive membership wrapper {group}"
  let nodes ← children group
  let index := (← get).next
  modify fun state => { state with next := index + 1 }
  let name := s.stem.appendAfter ("_closure_" ++ toString index)
  let body ← if nodes.isEmpty then do
    let custom := s.handlers.find? fun h => h.1 == group
    if custom.isSome then modify fun state => { state with used := state.used.push group }
    let shortcut ← if custom.isSome then pure none else trivialHeads s group
    match shortcut with
    | some proof => pure proof
    | none =>
        let proof := custom.map Prod.snd |>.getD s.fallback
        pure <| match s.known with
          | none => proof
          | some known =>
              "by\n  have _known := SpecTecWFS.All.map (fun a h => (" ++ known ++
              ") a h) _derivations\n  clear _derivations\n  exact (" ++ proof ++ ")"
  else do
    let mut branches := #[]
    for (ctor, child) in nodes do
      let lemma ← generate s child (group :: path)
      branches := branches.push <|
        "  | " ++ (Name.mkSimple ctor.getString!).toString ++ " h => exact " ++
          (← application lemma s "h")
    pure ("by\n  cases member with\n" ++ String.intercalate "\n" branches.toList)
  elaborate ("set_option linter.unusedSectionVars false in\nprivate theorem " ++
    name.toString ++ parameters s group ++ " := " ++ body)
  return name

private def generateResult (name : TSyntax `ident) (programName : Name)
    (settings : Settings) (handlers : Array (Name × String)) : CommandElabM Unit := do
    let (root, generated) ← (generate settings programName []).run {}
    for (handler, _) in handlers do
      unless generated.used.contains handler do
        throwError "unused membership handler {handler}; expected a leaf of {programName}"
    let body := if settings.known.isSome then
        "by\n  apply SpecTecWFS.Holds.sound_with proof (fun _ h => h)\n" ++
        "  intro rule member _side _positive _derivations _negative\n"
      else
        "by\n  apply SpecTecWFS.Holds.sound proof\n" ++
        "  intro rule member _side _positive _negative\n"
    elaborate ("theorem " ++ name.getId.toString ++
      " (atom : _) (proof : SpecTecWFS.Holds " ++ settings.program ++ " atom) : (" ++
      settings.predicate ++ ") atom := " ++ body ++
      "  exact " ++ (← application root settings "member"))
    let theoremName ← resolve name
    let axioms ← collectAxioms theoremName
    for axiomName in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "spec_invariant: unapproved axiom dependency {axiomName}"

elab_rules : command
  | `(spec_invariant $name:ident for $program:ident : $predicate:term
        $[using $known:term]? where $keys:ident => $proofs:term $[ $moreKeys:ident => $moreProofs:term ]*) => do
    let programName ← resolve program
    let allKeys := #[keys] ++ moreKeys
    let allProofs := #[proofs] ++ moreProofs
    let mut fallback : Option String := none
    let mut handlers := #[]
    for key in allKeys, proof in allProofs do
      if key.getId.eraseMacroScopes == `default then
        if fallback.isSome then throwErrorAt key "duplicate default handler"
        fallback := some (← source proof)
      else
        let group ← resolve key
        if handlers.any (fun h => h.1 == group) then
          throwErrorAt key "duplicate membership handler"
        handlers := handlers.push (group, ← source proof)
    let some defaultProof := fallback | throwError "spec_invariant requires a default handler"
    let settings : Settings := {
      program := programName.toString
      predicate := ← source predicate
      known := ← known.mapM (fun k => source k)
      fallback := defaultProof, handlers, stem := name.getId }
    let captures ← knownParameters known
    withScope (fun sc => { sc with
      includedVars := sc.includedVars ++ captures
      omittedVars := sc.omittedVars.filter (!captures.contains ·) }) do
      generateResult name programName settings handlers


end SpecTecProof

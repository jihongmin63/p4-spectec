module S = Ast.SpecTec
module L = Ast.Lean
module Mixfix = Domain.Mixfix
open Util.Source

exception Unsupported_il of Diagnostic.t

type branch_argument = Expression of S.exp | Function of S.id * L.type_ref

type branch = {
  name : string;
  arguments : branch_argument list;
  premises : S.prem list;
  at : region;
}

let unsupported (at : region) (construct : string) : 'a =
  raise
    (Unsupported_il
       (Diagnostic.error ~source:"lean" at
          ("Lean skeleton does not support " ^ construct)))

let translate_branch (env : env) (type_parameters : string list)
    (relation_name : string) (arity : int) (branch : branch) : L.rule * L.declaration list =
  if List.length branch.arguments <> arity then
    unsupported branch.at ("arity mismatch in rule " ^ branch.name ^ " of " ^ relation_name);
  let env : env = { env with iteration_prefix = relation_name ^ ":" ^ branch.name } in
  let functions : (string * L.type_ref) list =
    List.filter_map (function Function (id, typ) -> Some (id.it, typ) | Expression _ -> None) branch.arguments
  in
  let translate_argument (next : int) (argument : branch_argument) : term_result =
    match argument with
    | Expression exp -> translate_term env type_parameters functions next exp
    | Function (id, typ) -> pure_term next (L.Variable ("$" ^ id.it, typ))
  in
  let result : terms_result = collect_terms translate_argument 0 branch.arguments in
  let conclusion : L.application =
    { target = L.Global relation_name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      arguments = result.terms }
  in
  let result : terms_result = List.fold_left
    (fun (result : terms_result) (premise : S.prem) ->
      let translated : terms_result =
        translate_premise env type_parameters functions result.next premise
      in
      { result with premises = result.premises @ translated.premises;
        binders = result.binders @ translated.binders; next = translated.next;
        helpers = result.helpers @ translated.helpers })
    result branch.premises
  in
  let variables : (string * L.type_ref) list =
    List.concat_map variables_in_term
      (conclusion.arguments @ List.concat_map Traversal.premise_terms result.premises)
  in
  { name = branch.name; binders = unique_binders env branch.at (variables @ result.binders);
    premises = result.premises; conclusion }, result.helpers

let branch_of_rule (rule : S.rule) : branch =
  let id, conclusion, premises = rule.it in
  let name : string = if id.it = "" then "rule" else id.it in
  {
    name;
    arguments = List.map (fun exp -> Expression exp) (Mixfix.args conclusion);
    premises;
    at = rule.at;
  }

let branch_of_clause (type_parameters : string list) (parameters : S.param list)
    (index : int) (clause : S.clause) : branch =
  let arguments, result, premises = clause.it in
  if List.length arguments <> List.length parameters then
    unsupported clause.at
      (Printf.sprintf "function clause argument count: expected %d, got %d"
         (List.length parameters) (List.length arguments));
  let arguments : branch_argument list =
    List.mapi
      (fun position ((parameter : S.param), (argument : S.arg)) ->
        match parameter.it, argument.it with
        | ExpP _, ExpA exp -> Expression exp
        | DefP _, DefA id ->
            Function
              (id, translate_parameter_with_parameters type_parameters parameter)
        | ExpP _, DefA _ ->
            unsupported argument.at
              (Printf.sprintf
                 "function clause argument %d: expected expression, got function"
                 (position + 1))
        | DefP _, ExpA _ ->
            unsupported argument.at
              (Printf.sprintf
                 "function clause argument %d: expected function, got expression"
                 (position + 1)))
      (List.combine parameters arguments)
  in
  {
    name = "case_" ^ string_of_int index;
    arguments = arguments @ [ Expression result ];
    premises;
    at = clause.at;
  }

let substitute_application (bindings : (string * L.type_ref) list)
    (application : L.application) : L.application =
  Traversal.map_application_types (substitute_type_parameters bindings) application

(* SpecTec uses a type name as a variable name, as in [$repeat_<X>(X, n)].
   A Lean binder [X] would shadow the type parameter [X], so rename the type
   parameter instead of the variable. *)
let rename_type_parameters (env : env) (type_parameters : string list)
    (argument_types : L.type_ref list) (rules : L.rule list) :
    string list * L.type_ref list * L.rule list =
  let binder_names : string list =
    List.concat_map (fun (rule : L.rule) -> List.map fst rule.binders) rules
  in
  let taken (name : string) : bool =
    List.mem name binder_names
    || List.mem name type_parameters
    || StringMap.mem name env.constructors
    || StringMap.mem name env.aliases
    || StringMap.mem name env.structures
  in
  let fresh (name : string) : string =
    let rec search (index : int) : string =
      let candidate : string =
        if index = 0 then name ^ "_T" else name ^ "_T" ^ string_of_int index
      in
      if taken candidate then search (index + 1) else candidate
    in
    search 0
  in
  let renamings : (string * string) list =
    List.filter_map
      (fun name ->
        if List.mem name binder_names then Some (name, fresh name) else None)
      type_parameters
  in
  if renamings = [] then (type_parameters, argument_types, rules)
  else
    let bindings : (string * L.type_ref) list =
      List.map (fun (name, renamed) -> (name, L.TypeParameter renamed)) renamings
    in
    let rename (name : string) : string =
      Option.value ~default:name (List.assoc_opt name renamings)
    in
    ( List.map rename type_parameters,
      List.map (substitute_type_parameters bindings) argument_types,
      List.map
        (fun (rule : L.rule) ->
          {
            rule with
            binders =
              List.map
                (fun (name, typ) ->
                  (name, substitute_type_parameters bindings typ))
                rule.binders;
            premises = List.map (Traversal.map_premise_types (substitute_type_parameters bindings)) rule.premises;
            conclusion = substitute_application bindings rule.conclusion;
          })
        rules )

let translate_relation_unrenamed (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  let arity : int = List.length argument_types in
  let (_, rules, helpers) : string list * L.rule list * L.declaration list =
    List.fold_left
      (fun (used, rules, helpers) (branch : branch) ->
        let rec unique_name (index : int) : string =
          let candidate : string =
            if index = 1 then branch.name
            else branch.name ^ "_" ^ string_of_int index
          in
          if List.mem candidate used then unique_name (index + 1) else candidate
        in
        let name_rule : string = unique_name 1 in
        let (rule, emitted) : L.rule * L.declaration list =
          translate_branch env type_parameters name arity
            { branch with name = name_rule }
        in
        (name_rule :: used, rule :: rules, helpers @ emitted))
      ([], [], []) branches
  in
  let rules : L.rule list = List.rev rules in
  L.Relation { name; type_parameters; argument_types; rules; notation } :: helpers

let rename_relation_declarations (env : env) (type_parameters : string list)
    (declarations : L.declaration list) : L.declaration list =
  (* Helpers in a mutual block must use exactly their parent's parameters,
     including renamings needed to avoid element-variable shadowing. *)
  let all_rules : L.rule list = List.concat_map
    (function L.Relation { rules; _ } -> rules | _ -> []) declarations
  in
  let (renamed, _, _) : string list * L.type_ref list * L.rule list =
    rename_type_parameters env type_parameters [] all_rules
  in
  let bindings : (string * L.type_ref) list =
    List.combine type_parameters (List.map (fun name -> L.TypeParameter name) renamed)
  in
  let substitute : L.type_ref -> L.type_ref = substitute_type_parameters bindings in
  List.map
    (function
      | L.Relation relation -> L.Relation
          { relation with type_parameters = renamed;
            argument_types = List.map substitute relation.argument_types;
            rules = List.map (fun (rule : L.rule) ->
              { rule with binders = List.map (fun (name, typ) -> name, substitute typ) rule.binders;
                premises = List.map (Traversal.map_premise_types substitute) rule.premises;
                conclusion = substitute_application bindings rule.conclusion }) relation.rules }
      | declaration -> declaration)
    declarations

let translate_relation (env : env) (name : string) (type_parameters : string list)
    (argument_types : L.type_ref list) (branches : branch list)
    (notation : L.notation_part list option) : L.declaration list =
  rename_relation_declarations env type_parameters
    (translate_relation_unrenamed env name type_parameters argument_types branches notation)

let translate_otherwise_relation (env : env) (name : string)
    (type_parameters : string list) (argument_types : L.type_ref list)
    (branches : branch list) (otherwise : branch) (inputs : Lang.Hints.Input.t)
    (notation : L.notation_part list option) : L.declaration list =
  let regular_name : string = name ^ ":regular" in
  let regular : L.declaration list =
    translate_relation_unrenamed env regular_name type_parameters argument_types branches None
  in
  let public : L.declaration list =
    translate_relation_unrenamed env name type_parameters argument_types [ otherwise ] notation
  in
  let binders : (string * L.type_ref) list =
    List.mapi (fun index typ -> "arg:" ^ string_of_int index, typ) argument_types
  in
  let application : L.application =
    { target = L.Global name;
      type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
      arguments = List.map (fun (name, typ) -> L.Variable (name, typ)) binders }
  in
  let wrapper : L.rule =
    { name = "regular"; binders;
      premises = [ L.Holds { application with target = L.Global regular_name } ];
      conclusion = application }
  in
  let guard (rule : L.rule) : L.rule =
    let (arguments, _) : L.term list * L.term list =
      Lang.Hints.Input.split inputs rule.conclusion.arguments
    in
    let (_, output_types) : L.type_ref list * L.type_ref list =
      Lang.Hints.Input.split inputs argument_types
    in
    let outputs : (string * L.type_ref) list =
      List.mapi (fun index typ -> "otherwise:" ^ string_of_int index, typ) output_types
    in
    let negative : L.application =
      { rule.conclusion with target = L.Global regular_name;
        arguments = Lang.Hints.Input.combine inputs arguments
          (List.map (fun (name, typ) -> L.Variable (name, typ)) outputs) }
    in
    { rule with premises = L.NotExists (outputs, negative, otherwise.at) :: rule.premises }
  in
  let public : L.declaration list = match public with
    | L.Relation relation :: helpers ->
        let rules : L.rule list = List.map guard relation.rules in
        let rec wrapper_name (index : int) : string =
          let candidate : string = if index = 0 then "regular" else "regular_" ^ string_of_int index in
          if List.exists (fun (rule : L.rule) -> rule.name = candidate) rules then
            wrapper_name (index + 1)
          else candidate
        in
        L.Relation { relation with rules = { wrapper with name = wrapper_name 0 } :: rules } :: helpers
    | _ -> unsupported otherwise.at ("missing otherwise relation " ^ name)
  in
  rename_relation_declarations env type_parameters (regular @ public)
let rec validate_names (at : region) (names : string list) : unit =
  match names with
  | [] -> ()
  | name :: rest ->
      if name = "" then unsupported at "unnamed rules";
      if List.mem name rest then
        unsupported at ("duplicate constructor name " ^ name);
      validate_names at rest

let reserved_structure_field (name : string) : bool =
  let numbered (prefix : string) : bool =
    if not (String.starts_with ~prefix name) then false
    else
      let suffix : string =
        String.sub name (String.length prefix)
          (String.length name - String.length prefix)
      in
      let suffix : string =
        if String.ends_with ~suffix:"_eq" suffix then
          String.sub suffix 0 (String.length suffix - 3)
        else suffix
      in
      suffix <> "" && String.for_all Identifier.is_digit suffix
  in
  List.mem name
    [ "mk"; "rec"; "recOn"; "casesOn"; "noConfusion";
      "noConfusionType"; "below"; "brecOn"; "ctorIdx"; "_sizeOf_inst" ]
  || List.exists numbered [ "rec_"; "below_"; "brecOn_"; "_sizeOf_" ]

let translate_structure_fields (env : env) (fields : structure_field list) :
    (string * L.type_ref) list =
  List.map
    (fun (field : structure_field) ->
      if Identifier.contains_closing_quote field.name then
        unsupported field.atom.at
          ("structure field name containing closing quote »: " ^ field.name);
      if List.length (List.filter (fun other -> other.name = field.name) fields) > 1
      then unsupported field.atom.at ("duplicate structure field name " ^ field.name);
      if reserved_structure_field field.name then
        unsupported field.atom.at
          ("structure field name reserved by Lean " ^ field.name);
      ( field.name,
        translate_type field.typ |> expand_generic_aliases env field.typ.at [] ))
    fields

let translate_declaration (env : env) (decl : S.def) : L.declaration list =
  let declarations : L.declaration list =
    match decl.it with
    | TypD (id, tparams, { it = VariantT cases; _ }, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let constructors : L.constructor list =
          List.map (translate_constructor env id.it type_parameters) cases
        in
        [ L.Datatype { name = id.it; type_parameters; constructors } ]
    | TypD (id, tparams, { it = PlainT typ; _ }, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        [ L.TypeAlias
             {
               name = id.it;
               type_parameters;
               body = translate_type_with_parameters type_parameters typ;
             } ]
    | TypD (id, tparams, { it = StructT _; _ }, _) ->
        if tparams <> [] then
          unsupported decl.at ("type parameters of structure " ^ id.it);
        [ L.Structure
             {
               name = id.it;
               fields =
                 translate_structure_fields env
                   (StringMap.find id.it env.structures);
             } ]
    | ExternTypD (id, _) ->
        unsupported decl.at ("external type declaration " ^ id.it)
    | VarD _ ->
        (* TODO: Translate metavariable declarations. *)
        []
    | ExternRelD (id, _, _, _) ->
        unsupported decl.at ("external relation declaration " ^ id.it)
    | RelD (id, _, _, _, Some otherwise, _)
      when List.mem id.it env.recursive_otherwise ->
        unsupported otherwise.at ("otherwise of recursive definition " ^ id.it)
    | RelD (id, nottyp, inputs, rulegroups, elsegroup, _) ->
        let argument_types : L.type_ref list =
          List.map translate_type (Mixfix.args nottyp.it)
        in
        let branches : branch list =
          List.concat_map
            (fun (group : S.rulegroup) ->
              List.map branch_of_rule (snd group.it))
            rulegroups
        in
        let notation : L.notation_part list = translate_notation nottyp.it in
        if
          not
            (List.exists
               (function L.Literal _ -> true | L.Hole -> false)
               notation)
        then unsupported nottyp.at "relation notation without a visible atom";
        (match elsegroup with
        | None -> translate_relation env id.it [] argument_types branches (Some notation)
        | Some group ->
            let otherwise : branch = branch_of_rule (snd group.it) in
            translate_otherwise_relation env id.it [] argument_types branches otherwise inputs
              (Some notation))
    | ExternDecD (id, _, _, _, _) ->
        unsupported decl.at ("external function declaration " ^ id.it)
    | BuiltinDecD (id, tparams, params, result, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let parameters : L.type_ref list =
          List.map
            (fun (parameter : S.param) ->
              match parameter.it with
              | ExpP typ -> translate_type_with_parameters type_parameters typ
              | DefP (id, _, _, _) ->
                  unsupported parameter.at ("builtin function parameter " ^ id.it))
            params
        in
        let result : L.type_ref =
          translate_type_with_parameters type_parameters result
        in
        (match Builtin.translate id.it type_parameters with
        | Ok expected ->
            if parameters <> expected.parameters || result <> expected.result then
              unsupported decl.at
                ("builtin function " ^ id.it
               ^ " because its signature differs from the SpecTec implementation");
            [ L.Builtin { expected with name = "$" ^ expected.name } ]
        (* A rule-less relation would claim that the builtin has no result. *)
        | Error reason -> unsupported decl.at ("builtin function " ^ reason))
    | TableDecD (id, _, _, _, _) ->
        unsupported decl.at ("table declaration " ^ id.it)
    | FuncDecD (id, _, _, _, _, Some otherwise, _)
      when List.mem ("$" ^ id.it) env.recursive_otherwise ->
        unsupported otherwise.at ("otherwise of recursive definition $" ^ id.it)
    | FuncDecD (id, tparams, params, result, clauses, elseclause, _) ->
        let type_parameters : string list =
          List.map (fun (parameter : S.tparam) -> parameter.it) tparams
        in
        let argument_types : L.type_ref list =
          List.map (translate_parameter_with_parameters type_parameters) params
          @ [ translate_type_with_parameters type_parameters result ]
        in
        let branches : branch list =
          List.mapi
            (fun index clause ->
              branch_of_clause type_parameters params (index + 1) clause)
            clauses
        in
        (match elseclause with
        | None -> translate_relation env ("$" ^ id.it) type_parameters argument_types branches None
        | Some clause ->
            let otherwise : branch =
              branch_of_clause type_parameters params (List.length clauses + 1) clause
            in
            translate_otherwise_relation env ("$" ^ id.it) type_parameters argument_types
              branches otherwise (List.init (List.length params) Fun.id) None)
  in
  List.iter
    (function
      | L.Datatype { constructors; _ } ->
          validate_names decl.at
            (List.map
               (fun (constructor : L.constructor) -> constructor.name)
               constructors)
      | L.Relation { rules; _ } ->
          validate_names decl.at
            (List.map (fun (rule : L.rule) -> rule.name) rules)
      | L.TypeAlias _ -> ()
      | L.Structure _ -> ()
      | L.Builtin _ -> ())
    declarations;
  declarations

let translate (program : S.spec) : (L.located_declaration list, Diagnostic.t) result =
  let env : env = build_env program in
  try
    Ok
      (List.concat_map
         (fun (declaration : S.def) ->
           List.map
             (fun (translated : L.declaration) ->
               { L.declaration = translated; at = declaration.at })
             (translate_declaration env declaration))
         program)
  with Unsupported_il diagnostic -> Error diagnostic

let translate_all (program : S.spec) :
    L.located_declaration list * Diagnostic.t list =
  let env : env = build_env program in
  let (declarations, diagnostics) :
      L.located_declaration list * Diagnostic.t list =
    List.fold_left
      (fun (declarations, diagnostics) (declaration : S.def) ->
        try
          let translated : L.located_declaration list = List.map
            (fun (translated : L.declaration) -> { L.declaration = translated; at = declaration.at })
            (translate_declaration env declaration)
          in
          (List.rev_append translated declarations, diagnostics)
        with Unsupported_il diagnostic ->
          (declarations, diagnostic :: diagnostics))
      ([], []) program
  in
  (List.rev declarations, List.rev diagnostics)

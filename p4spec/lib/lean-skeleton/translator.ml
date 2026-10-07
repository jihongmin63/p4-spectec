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

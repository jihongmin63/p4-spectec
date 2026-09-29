module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let defined_name (declaration : L.declaration) : string =
  match declaration with
  | Datatype { name; _ } | TypeAlias { name; _ } | Structure { name; _ }
  | Relation { name; _ } | Builtin { name; _ } | Coercion { name; _ }
  | Membership { name; _ } -> name

let unions (sets : StringSet.t list) : StringSet.t =
  List.fold_left StringSet.union StringSet.empty sets

let rec type_references (typ : L.type_ref) : StringSet.t =
  match typ with
  | Name name -> StringSet.singleton name
  | Applied (name, arguments) ->
      StringSet.add name (unions (List.map type_references arguments))
  | BuiltinType (_, arguments) -> unions (List.map type_references arguments)
  | TypeParameter _ -> StringSet.empty
  | Pair (left, right) ->
      StringSet.union (type_references left) (type_references right)
  | RelationType (arguments, result) ->
      unions (List.map type_references (result :: arguments))

let reference_names (reference : L.reference) : StringSet.t =
  match reference with Global name -> StringSet.singleton name | Local _ -> StringSet.empty

let rec term_references (term : L.term) : StringSet.t =
  let own : StringSet.t = match term with
    | Variable (_, typ) | Number (_, typ) | Typed (_, typ) | StructureLiteral (typ, _) -> type_references typ
    | Constructor (reference, _) ->
        StringSet.add reference.type_name (unions (List.map type_references reference.type_arguments))
    | FunctionReference reference -> reference_names reference
    | Apply application ->
        StringSet.union (reference_names application.target)
          (unions (List.map type_references application.type_arguments))
    | Coerce (name, source, target, _) ->
        StringSet.add name
          (StringSet.union (type_references source) (type_references target))
    | MembershipTest (name, source, target, _, _, _) ->
        StringSet.add name
          (StringSet.union (type_references source) (type_references target))
    | Lambda (_, typ, _) -> type_references typ
    | Projection (name, _, _) -> StringSet.singleton name
    | Boolean _ | Text _ | Native _ | Unary _ | Binary _ | Tuple _ | ListLiteral _ | Index _ | Decide _ -> StringSet.empty
  in
  StringSet.union own (unions (List.map term_references (Traversal.term_children term)))

let application_references (application : L.application) : StringSet.t =
  StringSet.union (reference_names application.target)
    (unions (List.map type_references application.type_arguments
       @ List.map term_references application.arguments))

let premise_references (premise : L.premise) : StringSet.t =
  match premise with
  | Holds application | NotHolds (application, _) -> application_references application
  | NotExists (binders, application, _) ->
      StringSet.union (application_references application)
        (unions (List.map (fun (_, typ) -> type_references typ) binders))
  | Prop prop -> unions (List.map term_references (Traversal.prop_terms prop))

let rule_references (rule : L.rule) : StringSet.t =
  unions
    (application_references rule.conclusion
    :: (List.map (fun (_, typ) -> type_references typ) rule.binders
    @ List.map premise_references rule.premises))

let references (declaration : L.declaration) : StringSet.t =
  match declaration with
  | Datatype { constructors; _ } ->
      unions
        (List.map
           (fun (constructor : L.constructor) ->
             unions
               (List.map type_references
                  (constructor.result :: constructor.arguments)))
           constructors)
  | TypeAlias { body; _ } -> type_references body
  | Structure { fields; _ } ->
      unions (List.map (fun (_, typ) -> type_references typ) fields)
  | Relation { argument_types; rules; _ } ->
      unions
        (List.map type_references argument_types @ List.map rule_references rules)
  | Builtin { parameters; result; _ } ->
      unions (List.map type_references (result :: parameters))
  | Coercion { source; target; _ } ->
      StringSet.union (type_references source) (type_references target)
  | Membership { source; _ } -> type_references source

type node = {
  source : L.located_declaration;
  dependencies : StringSet.t;
  index : int;
}

type graph = node StringMap.t

let make_graph (declarations : L.located_declaration list) : graph =
  List.mapi
    (fun (index : int) (source : L.located_declaration) ->
      (defined_name source.declaration,
       { source; dependencies = references source.declaration; index }))
    declarations
  |> List.to_seq |> StringMap.of_seq

let names_in_order (graph : graph) : string list =
  StringMap.bindings graph
  |> List.sort (fun (_, left) (_, right) -> Int.compare left.index right.index)
  |> List.map fst

(* Kosaraju's two depth-first traversals keep all state in their return values. *)
let components (graph : graph) : string list list =
  let rec visit (edges : StringSet.t StringMap.t) (name : string)
      ((seen, finished) : StringSet.t * string list) : StringSet.t * string list =
    if StringSet.mem name seen then (seen, finished)
    else
      let (seen, finished) : StringSet.t * string list =
        StringSet.fold
          (fun dependency state -> visit edges dependency state)
          (StringMap.find name edges) (StringSet.add name seen, finished)
      in
      (seen, name :: finished)
  in
  let edges : StringSet.t StringMap.t =
    StringMap.map
      (fun (node : node) ->
        StringSet.filter (fun name -> StringMap.mem name graph) node.dependencies)
      graph
  in
  let (_, finished) : StringSet.t * string list =
    List.fold_left (fun state name -> visit edges name state)
      (StringSet.empty, []) (names_in_order graph)
  in
  let reversed : StringSet.t StringMap.t =
    StringMap.fold
      (fun name dependencies reversed ->
        StringSet.fold
          (fun dependency reversed ->
            StringMap.add dependency
              (StringSet.add name (StringMap.find dependency reversed)) reversed)
          dependencies reversed)
      edges (StringMap.map (fun _ -> StringSet.empty) graph)
  in
  let (_, groups) : StringSet.t * string list list =
    List.fold_left
      (fun (seen, groups) name ->
        if StringSet.mem name seen then (seen, groups)
        else
          let (seen, group) : StringSet.t * string list =
            visit reversed name (seen, [])
          in
          let group : string list =
            List.sort
              (fun left right ->
                Int.compare (StringMap.find left graph).index
                  (StringMap.find right graph).index)
              group
          in
          (seen, group :: groups))
      (StringSet.empty, []) finished
  in
  List.sort
    (fun left right ->
      Int.compare (StringMap.find (List.hd left) graph).index
        (StringMap.find (List.hd right) graph).index)
    groups

let topological_components (graph : graph) : string list list =
  let rec emit (done_names : StringSet.t) (remaining : string list list) :
      string list list =
    match remaining with
    | [] -> []
    | _ ->
        let ready (group : string list) : bool =
          let available : StringSet.t =
            StringSet.union done_names (StringSet.of_list group)
          in
          List.for_all
            (fun name ->
              StringSet.for_all
                (fun dependency ->
                  not (StringMap.mem dependency graph)
                  || StringSet.mem dependency available)
                (StringMap.find name graph).dependencies)
            group
        in
        let group : string list = List.find ready remaining in
        group :: emit (StringSet.union done_names (StringSet.of_list group))
          (List.filter (( <> ) group) remaining)
  in
  emit StringSet.empty (components graph)

let expand_declaration (lookup : string -> L.type_alias option)
    (source : L.located_declaration) : L.declaration =
  let expand : L.type_ref -> L.type_ref =
    Translator.expand_type_aliases lookup source.at []
  in
  match source.declaration with
  | Datatype datatype ->
      L.Datatype
        { datatype with
          constructors =
            List.map
              (fun (constructor : L.constructor) ->
                { constructor with
                  arguments = List.map expand constructor.arguments;
                  result = expand constructor.result })
              datatype.constructors }
  | Structure structure ->
      L.Structure
        { structure with
          fields = List.map (fun (name, typ) -> name, expand typ) structure.fields }
  | Relation relation ->
      L.Relation
        { relation with
          argument_types = List.map expand relation.argument_types;
          rules =
            List.map
              (fun (rule : L.rule) ->
                { rule with
                  binders = List.map (fun (name, typ) -> name, expand typ) rule.binders;
                  premises = List.map (Traversal.map_premise_types expand) rule.premises;
                  conclusion = Traversal.map_application_types expand rule.conclusion })
              relation.rules }
  | TypeAlias _ | Builtin _ | Coercion _ | Membership _ -> source.declaration

let validate_relation_values (names : string list)
    (source : L.located_declaration) : unit =
  let rec validate_term (term : L.term) : unit =
    match term with
    | FunctionReference (Global name) when List.mem name names ->
        Translator.unsupported source.at
          ("recursive relation value " ^ name ^ " in declaration "
          ^ defined_name source.declaration
          ^ ": current-component relations must occur as direct premise heads")
    | _ -> List.iter validate_term (Traversal.term_children term)
  in
  match source.declaration with
  | Relation { rules; _ } ->
      List.iter
        (fun (rule : L.rule) ->
          List.iter validate_term
            (rule.conclusion.arguments
            @ List.concat_map Traversal.premise_terms rule.premises))
        rules
  | _ -> ()

let validate_negative_premises (names : string list)
    (source : L.located_declaration) : unit =
  match source.declaration with
  | Relation { rules; _ } ->
      List.iter
        (fun (rule : L.rule) -> List.iter
          (function
            | L.NotHolds ({ target = Global name; _ }, at) ->
                if List.mem name names then
                  Translator.unsupported at
                    ("IfNotHoldPr of same-SCC relation " ^ name)
            | L.NotHolds ({ target = Local name; _ }, at) ->
                Translator.unsupported at ("IfNotHoldPr of local relation " ^ name)
            | L.NotExists (_, { target = Global name; _ }, at) ->
                let definition : string = defined_name source.declaration in
                if List.mem name names then
                  Translator.unsupported at ("otherwise of recursive definition " ^ definition)
            | L.NotExists (_, { target = Local name; _ }, at) ->
                Translator.unsupported at ("otherwise of local relation " ^ name)
            | L.Holds _ | L.Prop _ -> ())
          rule.premises)
        rules
  | _ -> ()

type sort = Data | Proposition

let group_program (graph : graph) (names : string list) : L.program =
  let sources : L.located_declaration list =
    List.map (fun name -> (StringMap.find name graph).source) names
  in
  List.iter (validate_negative_premises names) sources;
  List.iter (validate_relation_values names) sources;
  let (aliases, inductives) :
      L.located_declaration list * L.located_declaration list =
    List.partition
      (fun (source : L.located_declaration) ->
        match source.declaration with TypeAlias _ -> true | _ -> false)
      sources
  in
  let lookup (name : string) : L.type_alias option =
    match StringMap.find_opt name graph with
    | Some { source = { declaration = TypeAlias alias; _ }; _ }
      when alias.type_parameters <> [] || List.mem name names -> Some alias
    | _ -> None
  in
  let at : Util.Source.region = (List.hd sources).at in
  if inductives = [] then
    List.iter
      (fun (source : L.located_declaration) ->
        match source.declaration with
        | TypeAlias alias ->
            ignore
              (Translator.expand_type_aliases lookup source.at [ alias.name ]
                 alias.body)
        | _ -> ())
      aliases;
  match sources with
  | [ source ] -> [ L.Single source.declaration ]
  | _ ->
      let signatures : (string list * sort) list =
        List.map
          (fun (source : L.located_declaration) ->
            match source.declaration with
            | Datatype { type_parameters; _ } -> type_parameters, Data
            | Structure _ -> [], Data
            | Relation { type_parameters; _ } -> type_parameters, Proposition
            | Builtin _ -> Translator.unsupported at "mutual builtin definitions"
            | Coercion _ -> Translator.unsupported at "mutual coercion definitions"
            | Membership _ -> Translator.unsupported at "mutual membership definitions"
            | TypeAlias _ ->
                Translator.unsupported at "unexpanded alias in mutual block")
          inductives
      in
      (match signatures with
      | [] ->
          Translator.unsupported at ("cyclic type aliases " ^ String.concat ", " names)
      | (parameters, sort) :: rest ->
          if List.exists (fun (other, _) -> other <> parameters) rest then
            Translator.unsupported at
              ("mutual declarations with different type parameters: "
              ^ String.concat ", " names);
          if List.exists (fun (_, other) -> other <> sort) rest then
            Translator.unsupported at
              ("mutual declarations mixing Prop and Type: " ^ String.concat ", " names));
      let declarations : L.declaration list =
        List.map (expand_declaration lookup) inductives
      in
      (* Public aliases follow their own dependencies after the mutual block. *)
      let alias_graph : graph = make_graph aliases in
      let ordered_aliases : L.declaration_group list =
        List.concat_map
          (fun group ->
            List.map
              (fun name -> L.Single (StringMap.find name alias_graph).source.declaration)
              group)
          (topological_components alias_graph)
      in
      L.Mutual declarations :: ordered_aliases

let order (declarations : L.located_declaration list) :
    (L.program, Diagnostic.t) result =
  let graph : graph = make_graph declarations in
  try Ok (List.concat_map (group_program graph) (topological_components graph))
  with Translator.Unsupported_il diagnostic -> Error diagnostic

(* Missing names retain the untranslated root through transitive removals. *)
let prune (graph : graph) (missing : string StringMap.t) :
    graph * Diagnostic.t list =
  let rec remove (remaining : graph) (missing : string StringMap.t)
      (diagnostics : Diagnostic.t list) : graph * Diagnostic.t list =
    let rejected : (string * string * string) list =
      List.filter_map
        (fun name ->
          let node : node = StringMap.find name remaining in
          StringSet.elements node.dependencies
          |> List.find_map (fun dependency ->
                 if StringMap.mem dependency remaining then None
                 else
                   Some
                     ( name, dependency,
                       Option.value ~default:dependency
                         (StringMap.find_opt dependency missing) )))
        (names_in_order remaining)
    in
    match rejected with
    | [] -> remaining, diagnostics
    | _ ->
        let messages : Diagnostic.t list =
          List.map
            (fun (name, dependency, root) ->
              let detail : string =
                if dependency = root then " (direct dependency)"
                else
                  " (transitive dependency via removed declaration " ^ dependency ^ ")"
              in
              Diagnostic.error ~source:"lean" (StringMap.find name remaining).source.at
                ("Lean declaration " ^ name ^ " depends on untranslated declaration "
                ^ root ^ detail))
            rejected
        in
        let remaining : graph =
          List.fold_left
            (fun graph (name, _, _) -> StringMap.remove name graph)
            remaining rejected
        in
        let missing : string StringMap.t =
          List.fold_left
            (fun missing (name, _, root) -> StringMap.add name root missing)
            missing rejected
        in
        remove remaining missing (diagnostics @ messages)
  in
  remove graph missing []

let order_all (declarations : L.located_declaration list) :
    L.program * Diagnostic.t list =
  let (graph, dependency_diagnostics) : graph * Diagnostic.t list =
    prune (make_graph declarations) StringMap.empty
  in
  let (invalid, scc_diagnostics) : string StringMap.t * Diagnostic.t list =
    List.fold_left
      (fun (invalid, diagnostics) names ->
        try
          ignore (group_program graph names);
          invalid, diagnostics
        with Translator.Unsupported_il diagnostic ->
          let messages : Diagnostic.t list =
            List.map
              (fun name ->
                Diagnostic.error ~source:"lean" diagnostic.region
                  ("Lean declaration " ^ name ^ " is in rejected group {"
                  ^ String.concat ", " names ^ "}: " ^ diagnostic.message))
              names
          in
          ( List.fold_left (fun invalid name -> StringMap.add name name invalid)
              invalid names,
            diagnostics @ messages ))
      (StringMap.empty, []) (topological_components graph)
  in
  let (graph, transitive_diagnostics) : graph * Diagnostic.t list =
    prune
      (StringMap.filter (fun name _ -> not (StringMap.mem name invalid)) graph)
      invalid
  in
  (* Helpers and regular relations share the region of their IL definition.
     Nothing outside that definition refers to them, so once any part of the
     definition is removed the remaining parts would only be orphans. *)
  let removed_regions : Util.Source.region list =
    List.filter_map
      (fun (source : L.located_declaration) ->
        if StringMap.mem (defined_name source.declaration) graph then None
        else match source.declaration with
        | Coercion _ | Membership _ -> None
        | _ -> Some source.at)
      declarations
  in
  let graph : graph =
    StringMap.filter
      (fun _ (node : node) -> not (List.mem node.source.at removed_regions))
      graph
  in
  let generated (declaration : L.declaration) : bool =
    match declaration with Coercion _ | Membership _ -> true | _ -> false
  in
  let used_generated : StringSet.t =
    StringMap.fold
      (fun _ (node : node) names ->
        if generated node.source.declaration then names
        else StringSet.union names node.dependencies)
      graph StringSet.empty
  in
  let graph : graph =
    StringMap.filter
      (fun name (node : node) ->
        not (generated node.source.declaration)
        || StringSet.mem name used_generated)
      graph
  in
  ( List.concat_map (group_program graph) (topological_components graph),
    dependency_diagnostics @ scc_diagnostics @ transitive_diagnostics )

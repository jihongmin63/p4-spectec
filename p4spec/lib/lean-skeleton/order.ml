module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let defined_name (declaration : L.declaration) : string =
  match declaration with
  | Datatype { name; _ } | ExternType name | TypeAlias { name; _ } | Structure { name; _ }
  | Relation { name; _ } | Builtin { name; _ } | Selector { name; _ }
  | Coercion { name; _ }
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
  | TupleType elements -> unions (List.map type_references elements)
  | RelationType (arguments, result) ->
      unions (List.map type_references (result :: arguments))

let reference_names (reference : L.reference) : StringSet.t =
  match reference with Global name -> StringSet.singleton name | Local _ -> StringSet.empty

let rec term_references (term : L.term) : StringSet.t =
  let own : StringSet.t = match term with
    | Variable (_, typ) | Number (_, typ) | Typed (_, typ)
    | StructureLiteral (typ, _) | StructureUpdate (typ, _, _, _) ->
        type_references typ
    | Constructor (reference, _) ->
        StringSet.add reference.type_name (unions (List.map type_references reference.type_arguments))
    | FunctionReference reference ->
        StringSet.union (reference_names reference.target)
          (type_references reference.signature)
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
    | Decide (types, _) -> unions (List.map type_references types)
    | Boolean _ | Text _ | Native _ | Unary _ | Binary _ | Tuple _
    | ListLiteral _ | Index _ -> StringSet.empty
  in
  StringSet.union own (unions (List.map term_references (Traversal.term_children term)))

let application_references (application : L.application) : StringSet.t =
  StringSet.union (reference_names application.target)
    (unions (List.map type_references
       (application.type_arguments @ application.instance_arguments
       @ application.print_instance_arguments)
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
  | ExternType _ -> StringSet.empty
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
  | Selector { parameters; _ } ->
      unions (List.map type_references parameters)
  | Coercion { source; target; _ } ->
      StringSet.union (type_references source) (type_references target)
  | Membership { source; _ } -> type_references source

let extern_dependent_types (declarations : L.declaration list) : StringSet.t =
  let dependencies : (string * StringSet.t) list =
    List.filter_map
      (function
        | L.Datatype _ | L.TypeAlias _ | L.Structure _ as declaration ->
            Some (defined_name declaration, references declaration)
        | _ -> None)
      declarations
  in
  let rec close (names : StringSet.t) : StringSet.t =
    let expanded : StringSet.t =
      List.fold_left
        (fun names (name, referenced) ->
          if StringSet.is_empty (StringSet.inter names referenced) then names
          else StringSet.add name names)
        names dependencies
    in
    if StringSet.equal expanded names then names else close expanded
  in
  let roots : StringSet.t =
    List.fold_left
      (fun names -> function
        | L.ExternType name -> StringSet.add name names
        | _ -> names)
      StringSet.empty declarations
  in
  close roots

type node = {
  source : L.located_declaration;
  dependencies : StringSet.t;
  index : int;
}

type graph = node StringMap.t

(* These names are aliases supplied by the generated Lean prelude rather than
   IL declarations.  Keep-going validation must treat them like builtin types;
   otherwise it prunes every lowered fresh declaration even though strict
   translation emits and compiles the same references successfully. *)
let lean_support_names : StringSet.t =
  StringSet.of_list [ "FreshSupply"; "FreshSite" ]

let make_graph (declarations : L.located_declaration list) : graph =
  List.mapi
    (fun (index : int) (source : L.located_declaration) ->
      (defined_name source.declaration,
       { source;
         dependencies =
           StringSet.diff (references source.declaration) lean_support_names;
         index }))
    declarations
  |> List.to_seq |> StringMap.of_seq

let print_roots (declarations : L.located_declaration list) :
    (L.type_ref * Util.Source.region) list =
  List.concat_map
    (fun (located : L.located_declaration) ->
      match located.declaration with
      | L.Relation { name = "$print_"; _ } -> []
      | L.Relation { rules; _ } ->
          Translator.relation_applications rules
          |> List.concat_map (fun (application : L.application) ->
                 let direct : L.type_ref list =
                   match application.target, application.type_arguments with
                   | L.Global "$print_", typ :: _ -> [ typ ]
                   | _ -> []
                 in
                 List.map
                   (fun typ -> typ, located.at)
                   (direct @ application.print_instance_arguments))
      | _ -> [])
    declarations
  |> List.sort_uniq (fun (left, _) (right, _) -> compare left right)

let reachable_printer_names (graph : graph)
    (roots : (L.type_ref * Util.Source.region) list) : StringSet.t =
  let rec visit_type (at : Util.Source.region) (seen : StringSet.t)
      (typ : L.type_ref) : StringSet.t =
    match typ with
    | TypeParameter _ -> seen
    | BuiltinType (_, arguments) | TupleType arguments ->
        List.fold_left (visit_type at) seen arguments
    | RelationType _ -> seen
    | Name name -> visit_named at seen name []
    | Applied (name, arguments) -> visit_named at seen name arguments
  and visit_named (at : Util.Source.region) (seen : StringSet.t)
      (name : string) (arguments : L.type_ref list) : StringSet.t =
    let seen : StringSet.t = List.fold_left (visit_type at) seen arguments in
    if StringSet.mem name seen then seen
    else
      match StringMap.find_opt name graph with
      | None -> seen
      | Some node -> (
          match node.source.declaration with
          | TypeAlias alias ->
              if List.length alias.type_parameters <> List.length arguments then
                Translator.unsupported at
                  (Printf.sprintf "print type arity in %s: expected %d, got %d"
                     name (List.length alias.type_parameters)
                     (List.length arguments));
              let bindings : (string * L.type_ref) list =
                List.combine alias.type_parameters arguments
              in
              visit_type node.source.at seen
                (Translator.substitute_type_parameters bindings alias.body)
          | Datatype datatype ->
              if List.length datatype.type_parameters <> List.length arguments
                 && arguments <> [] then
                Translator.unsupported at
                  (Printf.sprintf "print type arity in %s: expected %d, got %d"
                     name (List.length datatype.type_parameters)
                     (List.length arguments));
              let seen : StringSet.t = StringSet.add name seen in
              List.fold_left
                (fun seen (constructor : L.constructor) ->
                  let used : int list =
                    L.print_format_holes constructor.print_format in
                  List.fold_left (visit_type node.source.at) seen
                    (List.filteri
                       (fun index _ -> List.mem index used)
                       constructor.arguments))
                seen datatype.constructors
          | Structure _ -> StringSet.add name seen
          | _ -> seen)
  in
  List.fold_left
    (fun seen (typ, at) -> visit_type at seen typ)
    StringSet.empty roots

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
  | Selector selector ->
      L.Selector
        { selector with
          parameters = List.map expand selector.parameters;
          arms =
            List.map
              (fun (patterns, row) ->
                ( List.map
                    (function
                      | L.Wildcard -> L.Wildcard
                      | L.ConstructorPattern (reference, arity) ->
                          L.ConstructorPattern
                            ( { reference with
                                type_arguments =
                                  List.map expand reference.type_arguments },
                              arity ))
                    patterns,
                  row ))
              selector.arms }
  | ExternType _ | TypeAlias _ | Builtin _ | Coercion _ | Membership _ -> source.declaration

let expand_print_instance_arguments (graph : graph)
    (source : L.located_declaration) : L.located_declaration =
  let lookup (name : string) : L.type_alias option =
    match StringMap.find_opt name graph with
    | Some { source = { declaration = TypeAlias alias; _ }; _ } -> Some alias
    | _ -> None
  in
  let expand : L.type_ref -> L.type_ref =
    Translator.expand_type_aliases lookup source.at []
  in
  let normalize (application : L.application) : L.application =
    { application with
      print_instance_arguments =
        List.map expand application.print_instance_arguments }
  in
  let application (value : L.application) : L.application =
    normalize
      { value with
        arguments =
          List.map (Traversal.map_term_applications normalize) value.arguments }
  in
  let declaration : L.declaration =
    match source.declaration with
    | Relation relation ->
        L.Relation
          { relation with
            rules =
              List.map
                (fun (rule : L.rule) ->
                  { rule with
                    premises =
                      List.map
                        (Traversal.map_premise_applications normalize)
                        rule.premises;
                    conclusion = application rule.conclusion })
                relation.rules }
    | declaration -> declaration
  in
  { source with declaration }

type sort = Data | Proposition

let data_declaration (declaration : L.declaration) : bool =
  match declaration with L.Datatype _ | L.Structure _ -> true | _ -> false

let data_type_parameters (declaration : L.declaration) : string list =
  match declaration with
  | L.Datatype { type_parameters; _ } -> type_parameters
  | L.Structure _ -> []
  | _ -> assert false

let data_type (declaration : L.declaration) : L.type_ref =
  match declaration with
  | L.Datatype { name; type_parameters = []; _ } | L.Structure { name; _ } ->
      L.Name name
  | L.Datatype { name; type_parameters; _ } ->
      L.Applied (name, List.map (fun name -> L.TypeParameter name) type_parameters)
  | _ -> assert false

let rec contains_type_name (names : StringSet.t) (typ : L.type_ref) : bool =
  match typ with
  | Name name -> StringSet.mem name names
  | Applied (name, arguments) ->
      StringSet.mem name names || List.exists (contains_type_name names) arguments
  | BuiltinType (_, arguments) -> List.exists (contains_type_name names) arguments
  | TupleType elements -> List.exists (contains_type_name names) elements
  | RelationType (arguments, result) ->
      List.exists (contains_type_name names) (result :: arguments)
  | TypeParameter _ -> false

let direct_type_name (names : StringSet.t) (typ : L.type_ref) : bool =
  match typ with
  | Name name | Applied (name, _) -> StringSet.mem name names
  | _ -> false

let declaration_field_types (declaration : L.declaration) : L.type_ref list =
  match declaration with
  | Datatype { constructors; _ } ->
      List.concat_map (fun (constructor : L.constructor) -> constructor.arguments)
        constructors
  | Structure { fields; _ } -> List.map snd fields
  | _ -> []

let has_nested_recursion (names : StringSet.t) (declaration : L.declaration) : bool =
  List.exists
    (fun typ -> contains_type_name names typ && not (direct_type_name names typ))
    (declaration_field_types declaration)

let equality_function_name (root_names : StringSet.t) (typ : L.type_ref) : string =
  match typ with
  | Name name | Applied (name, _) when StringSet.mem name root_names ->
      "decEq_" ^ name
  | _ ->
      "decEq_shape_"
      ^ String.sub (Digest.to_hex (Digest.string (Translator.type_code typ))) 0 12

let instantiate_datatype (at : Util.Source.region) (typ : L.type_ref)
    (datatype : L.datatype) : L.constructor list =
  let arguments : L.type_ref list =
    match typ with
    | Name _ -> []
    | Applied (_, arguments) -> arguments
    | _ -> assert false
  in
  if List.length datatype.type_parameters <> List.length arguments then
    Translator.unsupported at
      (Printf.sprintf "DecidableEq type arity in %s: expected %d, got %d"
         datatype.name (List.length datatype.type_parameters) (List.length arguments));
  let bindings : (string * L.type_ref) list =
    List.combine datatype.type_parameters arguments
  in
  List.map
    (fun (constructor : L.constructor) ->
      { constructor with
        arguments =
          List.map (Translator.substitute_type_parameters bindings)
            constructor.arguments;
        result = Translator.substitute_type_parameters bindings constructor.result })
    datatype.constructors

let manual_equality (graph : graph) (at : Util.Source.region)
    (declarations : L.declaration list) : L.manual_equality =
  let root_names : StringSet.t =
    declarations |> List.map defined_name |> StringSet.of_list
  in
  let root_declarations : L.declaration StringMap.t =
    declarations
    |> List.map (fun declaration -> defined_name declaration, declaration)
    |> List.to_seq |> StringMap.of_seq
  in
  let type_parameters : string list =
    match declarations with
    | declaration :: _ -> data_type_parameters declaration
    | [] -> assert false
  in
  let rec collect (trail : (string * L.type_ref) list)
      (shapes : L.equality_shape list) (typ : L.type_ref) :
      L.equality_shape list =
    let trail : (string * L.type_ref) list =
      match typ with
      | Name name | Applied (name, _) -> (
          match List.assoc_opt name trail with
          | Some previous when previous <> typ ->
              Translator.unsupported at
                ("DecidableEq non-uniform recursive type "
                ^ Translator.type_code typ ^ " after "
                ^ Translator.type_code previous)
          | Some _ -> trail
          | None -> (name, typ) :: trail)
      | _ -> trail
    in
    if List.exists (fun (shape : L.equality_shape) -> shape.equality_type = typ) shapes
    then shapes
    else
      let kind : L.equality_shape_kind =
        match typ with
        | BuiltinType ("List", [ element ]) -> L.EqualityList element
        | BuiltinType ("Option", [ element ]) -> L.EqualityOption element
        | TupleType elements -> L.EqualityTuple elements
        | Name name | Applied (name, _) -> (
            let declaration : L.declaration option =
              match StringMap.find_opt name root_declarations with
              | Some declaration -> Some declaration
              | None ->
                  Option.map
                    (fun (node : node) -> node.source.declaration)
                    (StringMap.find_opt name graph)
            in
            match declaration with
            | Some (Datatype datatype) ->
                L.EqualityDatatype (instantiate_datatype at typ datatype)
            | Some (Structure { fields; _ }) when typ = L.Name name ->
                L.EqualityStructure fields
            | _ ->
                Translator.unsupported at
                  ("DecidableEq nested recursive type " ^ Translator.type_code typ))
        | _ ->
            Translator.unsupported at
              ("DecidableEq nested recursive shape " ^ Translator.type_code typ)
      in
      let shape : L.equality_shape =
        { equality_name = equality_function_name root_names typ;
          equality_type = typ; equality_kind = kind }
      in
      let shapes : L.equality_shape list = shapes @ [ shape ] in
      let children : L.type_ref list =
        match kind with
        | EqualityDatatype constructors ->
            List.concat_map
              (fun (constructor : L.constructor) -> constructor.arguments)
              constructors
        | EqualityStructure fields -> List.map snd fields
        | EqualityList element | EqualityOption element -> [ element ]
        | EqualityTuple elements -> elements
      in
      List.fold_left
        (fun shapes child ->
          if contains_type_name root_names child then collect trail shapes child
          else shapes)
        shapes children
  in
  let root_types : L.type_ref list = List.map data_type declarations in
  let shapes : L.equality_shape list =
    List.fold_left (collect []) [] root_types
  in
  { equality_type_parameters = type_parameters;
    equality_shapes = shapes;
    equality_instances =
      List.map
        (fun typ -> typ, equality_function_name root_names typ)
        root_types }

let print_function_name (root_names : StringSet.t) (typ : L.type_ref) : string =
  match typ with
  | Name name | Applied (name, _) when StringSet.mem name root_names ->
      "print_" ^ name
  | _ ->
      let owner : string = String.concat "," (StringSet.elements root_names) in
      "print_shape_"
      ^ String.sub
          (Digest.to_hex
             (Digest.string (owner ^ ":" ^ Translator.type_code typ)))
          0 12

let manual_printer (graph : graph) (at : Util.Source.region)
    (declarations : L.declaration list) : L.manual_printer =
  let root_names : StringSet.t =
    declarations |> List.map defined_name |> StringSet.of_list
  in
  let root_declarations : L.declaration StringMap.t =
    declarations
    |> List.map (fun declaration -> defined_name declaration, declaration)
    |> List.to_seq |> StringMap.of_seq
  in
  let type_parameters : string list =
    match declarations with
    | declaration :: _ -> data_type_parameters declaration
    | [] -> assert false
  in
  let alias (name : string) : L.type_alias option =
    match StringMap.find_opt name graph with
    | Some { source = { declaration = TypeAlias alias; _ }; _ } -> Some alias
    | _ -> None
  in
  let expand (typ : L.type_ref) : L.type_ref =
    Translator.expand_type_aliases alias at [] typ
  in
  let rec collect (trail : (string * L.type_ref) list)
      (shapes : L.print_shape list) (typ : L.type_ref) : L.print_shape list =
    let typ : L.type_ref = expand typ in
    let trail : (string * L.type_ref) list =
      match typ with
      | Name name | Applied (name, _) -> (
          match List.assoc_opt name trail with
          | Some previous when previous <> typ ->
              Translator.unsupported at
                ("SpecTecPrint non-uniform recursive type "
                ^ Translator.type_code typ ^ " after "
                ^ Translator.type_code previous)
          | Some _ -> trail
          | None -> (name, typ) :: trail)
      | _ -> trail
    in
    if List.exists (fun (shape : L.print_shape) -> shape.print_type = typ) shapes
    then shapes
    else
      let kind : L.print_shape_kind =
        match typ with
        | BuiltinType ("List", [ element ]) -> L.PrintList (expand element)
        | BuiltinType ("Option", [ element ]) -> L.PrintOption (expand element)
        | TupleType elements -> L.PrintTuple (List.map expand elements)
        | RelationType _ -> L.PrintFailure
        | Name name | Applied (name, _) -> (
            let declaration : L.declaration option =
              match StringMap.find_opt name root_declarations with
              | Some declaration -> Some declaration
              | None ->
                  Option.map
                    (fun (node : node) -> node.source.declaration)
                    (StringMap.find_opt name graph)
            in
            match declaration with
            | Some (Datatype datatype) ->
                let constructors : L.constructor list =
                  instantiate_datatype at typ datatype
                  |> List.map (fun (constructor : L.constructor) ->
                         { constructor with
                           arguments = List.map expand constructor.arguments })
                in
                L.PrintDatatype constructors
            | Some (Structure _) when typ = L.Name name -> L.PrintStructure
            | _ ->
                Translator.unsupported at
                  ("SpecTecPrint nested recursive type "
                  ^ Translator.type_code typ))
        | _ ->
            Translator.unsupported at
              ("SpecTecPrint nested shape " ^ Translator.type_code typ)
      in
      let shape : L.print_shape =
        { print_name = print_function_name root_names typ;
          print_type = typ; print_kind = kind }
      in
      let shapes : L.print_shape list = shapes @ [ shape ] in
      let children : L.type_ref list =
        match kind with
        | PrintDatatype constructors ->
            List.concat_map
              (fun (constructor : L.constructor) ->
                let used : int list =
                  L.print_format_holes constructor.print_format in
                List.filteri
                  (fun index _ -> List.mem index used)
                  constructor.arguments)
              constructors
        | PrintList element | PrintOption element -> [ element ]
        | PrintTuple elements -> elements
        | PrintStructure | PrintFailure -> []
      in
      List.fold_left
        (fun shapes child ->
          let child : L.type_ref = expand child in
          let needs_shape : bool =
            match child with
            | BuiltinType (("List" | "Option"), [ _ ]) | TupleType _
            | RelationType _ -> true
            | Name _ | Applied _ -> contains_type_name root_names child
            | _ -> false
          in
          if needs_shape then collect trail shapes child else shapes)
        shapes children
  in
  let root_types : L.type_ref list = List.map data_type declarations in
  let shapes : L.print_shape list = List.fold_left (collect []) [] root_types in
  { printer_type_parameters = type_parameters;
    printer_shapes = shapes;
    printer_instances =
      List.map
        (fun typ -> typ, print_function_name root_names typ)
        root_types }

let data_groups (graph : graph) (print_names : StringSet.t)
    (at : Util.Source.region) (declarations : L.declaration list)
    (group : L.declaration_group) :
    L.declaration_group list =
  let names : StringSet.t =
    declarations |> List.map defined_name |> StringSet.of_list
  in
  let equality : L.declaration_group list =
    if List.exists (has_nested_recursion names) declarations then
      [ group; L.ManualDecidableEq (manual_equality graph at declarations) ]
    else [ L.DerivingDecidableEq group ]
  in
  if StringSet.disjoint names print_names then equality
  else equality @ [ L.ManualPrinter (manual_printer graph at declarations) ]

let group_program (graph : graph) (print_names : StringSet.t)
    (names : string list) : L.program =
  let sources : L.located_declaration list =
    List.map (fun name -> (StringMap.find name graph).source) names
  in
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
  | [ source ] when data_declaration source.declaration ->
      data_groups graph print_names source.at [ source.declaration ]
        (L.Single source.declaration)
  | [ source ] -> [ L.Single source.declaration ]
  | _ ->
      let signatures : (string list * sort) list =
        List.map
          (fun (source : L.located_declaration) ->
            match source.declaration with
            | Datatype { type_parameters; _ } -> type_parameters, Data
            | Structure _ -> [], Data
            | Relation { type_parameters; _ } -> type_parameters, Proposition
            | ExternType _ -> Translator.unsupported at "mutual external type definitions"
            | Builtin _ -> Translator.unsupported at "mutual builtin definitions"
            | Selector _ ->
                Translator.unsupported at "mutual selector definitions"
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
          if sort = Data
             && List.exists (fun (other, _) -> other <> parameters) rest then
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
      (if List.for_all data_declaration declarations then
         data_groups graph print_names at declarations (L.Mutual declarations)
       else [ L.Mutual declarations ])
      @ ordered_aliases

let order (declarations : L.located_declaration list) :
    (L.program, Diagnostic.t) result =
  try
    let declarations : L.located_declaration list =
      let graph : graph = make_graph declarations in
      List.map (expand_print_instance_arguments graph) declarations
    in
    let graph : graph = make_graph declarations in
    let print_names : StringSet.t =
      reachable_printer_names graph (print_roots declarations) in
    Ok
      (List.concat_map (group_program graph print_names)
         (topological_components graph))
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
  let declarations : L.located_declaration list =
    let graph : graph = make_graph declarations in
    List.map (expand_print_instance_arguments graph) declarations
  in
  let (graph, dependency_diagnostics) : graph * Diagnostic.t list =
    prune (make_graph declarations) StringMap.empty
  in
  let print_names : StringSet.t =
    reachable_printer_names graph (print_roots declarations) in
  let (invalid, scc_diagnostics) : string StringMap.t * Diagnostic.t list =
    List.fold_left
      (fun (invalid, diagnostics) names ->
        try
          ignore (group_program graph print_names names);
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
  ( List.concat_map (group_program graph print_names)
      (topological_components graph),
    dependency_diagnostics @ scc_diagnostics @ transitive_diagnostics )

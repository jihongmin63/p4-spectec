module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)
module IntSet = Set.Make (Int)

let supply_type = L.Name "FreshSupply"
let string_type = L.BuiltinType ("String", [])
let nat_type = L.BuiltinType ("Nat", [])

let starts_with prefix value =
  String.length value >= String.length prefix
  && String.sub value 0 (String.length prefix) = prefix

let ends_with suffix value =
  String.length value >= String.length suffix
  && String.sub value (String.length value - String.length suffix)
       (String.length suffix) = suffix

let drop_suffix suffix value =
  String.sub value 0 (String.length value - String.length suffix)

let state_variable name =
  starts_with "fresh:counter:" name || starts_with "fresh:entry" name
  || starts_with "fresh:final" name || starts_with "fresh:return:" name
  || starts_with "fresh:derived:" name || starts_with "fresh:supply:" name

let rename_variable name =
  if starts_with "fresh:counter:" name then
    "fresh:supply:" ^ String.sub name (String.length "fresh:counter:")
      (String.length name - String.length "fresh:counter:")
  else if starts_with "fresh:entry" name then
    "fresh:supply:entry" ^ String.sub name (String.length "fresh:entry")
      (String.length name - String.length "fresh:entry")
  else if starts_with "fresh:final" name then
    "fresh:supply:final" ^ String.sub name (String.length "fresh:final")
      (String.length name - String.length "fresh:final")
  else name

let rename_reference = function
  | L.Global name when ends_with ":state" name ->
      L.Global (drop_suffix ":state" name ^ ":supply")
  | reference -> reference

let rec rename_term = function
  | L.Variable (name, typ) ->
      let renamed = rename_variable name in
      L.Variable (renamed, if state_variable name then supply_type else typ)
  | L.Constructor (reference, arguments) ->
      L.Constructor (reference, List.map rename_term arguments)
  | L.FunctionReference reference ->
      L.FunctionReference { reference with target = rename_reference reference.target }
  | L.Apply application -> L.Apply (rename_application application)
  | L.Coerce (name, source, target, value) ->
      L.Coerce (name, source, target, rename_term value)
  | L.MembershipTest (name, source, target, cases, exhaustive, value) ->
      L.MembershipTest (name, source, target, cases, exhaustive, rename_term value)
  | L.Lambda (name, typ, body) ->
      L.Lambda (rename_variable name,
        (if state_variable name then supply_type else typ), rename_term body)
  | L.Native (name, arguments) -> L.Native (name, List.map rename_term arguments)
  | L.Unary (operator, value) -> L.Unary (operator, rename_term value)
  | L.Binary (operator, left, right) ->
      L.Binary (operator, rename_term left, rename_term right)
  | L.Typed (value, typ) -> L.Typed (rename_term value, typ)
  | L.Tuple (left, right) -> L.Tuple (rename_term left, rename_term right)
  | L.ListLiteral values -> L.ListLiteral (List.map rename_term values)
  | L.StructureLiteral (typ, fields) ->
      L.StructureLiteral (typ,
        List.map (fun (name, value) -> name, rename_term value) fields)
  | L.StructureUpdate (typ, base, field, value) ->
      L.StructureUpdate (typ, rename_term base, field, rename_term value)
  | L.Projection (name, field, value) ->
      L.Projection (name, field, rename_term value)
  | L.Index (base, index) -> L.Index (rename_term base, rename_term index)
  | L.Decide (types, proposition) -> L.Decide (types, rename_prop proposition)
  | (L.Boolean _ | L.Number _ | L.Text _) as term -> term

and rename_prop = function
  | L.Comparison (operator, left, right) ->
      L.Comparison (operator, rename_term left, rename_term right)
  | L.Membership (element, collection) ->
      L.Membership (rename_term element, rename_term collection)
  | L.IsTrue term -> L.IsTrue (rename_term term)
  | L.Predicate term -> L.Predicate (rename_term term)
  | L.Not proposition -> L.Not (rename_prop proposition)
  | L.And (left, right) -> L.And (rename_prop left, rename_prop right)
  | L.Or (left, right) -> L.Or (rename_prop left, rename_prop right)
  | L.Implies (left, right) -> L.Implies (rename_prop left, rename_prop right)
  | L.Iff (left, right) -> L.Iff (rename_prop left, rename_prop right)
  | L.Forall (name, typ, body) ->
      L.Forall (rename_variable name,
        (if state_variable name then supply_type else typ), rename_prop body)

and rename_application application =
  { application with target = rename_reference application.target;
    arguments = List.map rename_term application.arguments }

let rename_premise = function
  | L.Holds application -> L.Holds (rename_application application)
  | L.NotHolds (application, at) ->
      L.NotHolds (rename_application application, at)
  | L.NotExists (binders, application, at) ->
      L.NotExists
        (List.map (fun (name, typ) -> rename_variable name,
           if state_variable name then supply_type else typ) binders,
         rename_application application, at)
  | L.Prop proposition -> L.Prop (rename_prop proposition)

let variable_name = function L.Variable (name, _) -> Some name | _ -> None

let state_argument_positions (rules : L.rule list) =
  List.fold_left (fun positions (rule : L.rule) ->
    List.fold_left (fun positions (index, argument) ->
      match variable_name argument with
      | Some name when state_variable name -> IntSet.add index positions
      | _ -> positions)
      positions (List.mapi (fun index argument -> index, argument)
        rule.conclusion.arguments))
    IntSet.empty rules

let resolve substitutions = function
  | L.Variable (name, typ) ->
      let rec find name = match StringMap.find_opt name substitutions with
        | Some next when next <> name -> find next
        | _ -> name in
      L.Variable (find name, typ)
  | term -> term

let variables term =
  let rec collect result = function
    | L.Variable (name, typ) -> (name, typ) :: result
    | term -> List.fold_left collect result (Traversal.term_children term)
  in collect [] term

let add_term_variables set term =
  List.fold_left (fun result (name, _) -> StringSet.add name result)
    set (variables term)

let term_is_tainted tainted term =
  List.exists (fun (name, _) -> StringSet.mem name tainted) (variables term)

let propagate_equality tainted = function
  | L.Comparison (L.Eq, left, right) ->
      let left_tainted = term_is_tainted tainted left in
      let right_tainted = term_is_tainted tainted right in
      let tainted = if left_tainted then add_term_variables tainted right else tainted in
      if right_tainted then add_term_variables tainted left else tainted
  | _ -> tainted

let site relation rule premise =
  L.StructureLiteral (L.Name "FreshSite",
    [ "relation", L.Text relation;
      "rule", L.Number (string_of_int rule, nat_type);
      "premise", L.Number (string_of_int premise, nat_type) ])

let predicate name arguments =
  L.Prop (L.Predicate (L.Native (name, arguments)))

let equality left right = L.Prop (L.Comparison (L.Eq, left, right))

let application_name application = match application.L.target with
  | L.Global name -> Some name
  | L.Local _ -> None

let original_supply_target application =
  match application_name application with
  | Some name when ends_with ":supply" name ->
      Some (drop_suffix ":supply" name)
  | _ -> None

let split_state_arguments (application : L.application) =
  match application.L.arguments with
  | before :: rest ->
      (match List.rev rest with
      | after :: reversed -> Some (before, List.rev reversed, after)
      | [] -> None)
  | [] -> None

let input_positions declarations =
  List.fold_left (fun positions located ->
    match located.L.declaration with
    | L.Relation { name; input_positions = Some inputs; _ } ->
        StringMap.add name inputs positions
    | _ -> positions) StringMap.empty declarations

let outputs positions target arguments =
  let inputs = Option.value (StringMap.find_opt target positions)
    ~default:(List.init (max 0 (List.length arguments - 1)) Fun.id) in
  List.filteri (fun index _ -> not (List.mem index inputs)) arguments

let protected_name relation =
  "FreshProtectedRelation_" ^ Digest.to_hex (Digest.string relation)

let fresh_source tainted arguments =
  arguments |> List.concat_map variables
  |> List.filter (fun (name, _) -> StringSet.mem name tainted)
  |> List.sort_uniq (fun (left, _) (right, _) -> String.compare left right)
  |> function [ source ] -> Some source | _ -> None

let root_supply positions relation middle =
  let inputs = Option.value (StringMap.find_opt relation positions)
    ~default:(List.init (max 0 (List.length middle - 1)) Fun.id) in
  let protected = L.Native
    ("SpecTec." ^ protected_name relation,
     List.filteri (fun index _ -> List.mem index inputs) middle) in
  L.Native ("SpecTecFresh.Supply.root", [ protected ])

let transform_wrapper positions relation (rule : L.rule) =
  let premises = List.map rename_premise rule.premises in
  let premises = List.map (function
    | L.Holds application ->
        (match original_supply_target application,
               split_state_arguments application with
        | Some _, Some (_, middle, after) ->
            L.Holds { application with
              arguments = root_supply positions relation middle :: middle @ [ after ] }
        | _ -> L.Holds application)
    | premise -> premise) premises in
  { rule with
    name = "from_root_supply";
    binders = List.map (fun (name, typ) ->
      rename_variable name, if state_variable name then supply_type else typ)
      rule.binders;
    premises;
    conclusion = rename_application rule.conclusion }

let transform_rule positions relation rule_index (rule : L.rule) =
  let binders = ref (List.map (fun (name, typ) ->
    rename_variable name, if state_variable name then supply_type else typ)
      rule.binders) in
  let conclusion = rename_application rule.conclusion in
  let initial = match conclusion.arguments with
    | first :: _ -> first
    | [] -> L.Native ("SpecTecFresh.Supply.root", [ L.ListLiteral [] ]) in
  let current = ref initial in
  let substitutions = ref StringMap.empty in
  let tainted = ref StringSet.empty in
  let translated = ref [] in
  let add premise = translated := !translated @ [ premise ] in
  List.iteri (fun premise_index original ->
    let premise = rename_premise original in
    match premise with
    | L.Holds application ->
        (match original_supply_target application,
               split_state_arguments application with
        | Some "$fresh_typeId", Some (before, middle, after) ->
            let before = resolve !substitutions before in
            let after = resolve !substitutions after in
            let output = match middle with
              | [ output ] -> output
              | _ -> invalid_arg "fresh supply: fresh_typeId arity" in
            add (predicate "SpecTecFresh.Allocates"
              [ site relation rule_index premise_index; before; output; after ]);
            current := after;
            tainted := add_term_variables !tainted output
        | Some target, Some (before, middle, after) ->
            let before = resolve !substitutions before in
            let after = resolve !substitutions after in
            let returned_name = "fresh:return:" ^ string_of_int rule_index
              ^ ":" ^ string_of_int premise_index in
            let returned = L.Variable (returned_name, supply_type) in
            binders := !binders @ [ returned_name, supply_type ];
            let entered = L.Native ("SpecTecFresh.Supply.enter",
              [ L.Number (string_of_int premise_index, nat_type); before ]) in
            add (L.Holds { application with
              arguments = entered :: middle @ [ returned ] });
            add (equality after
              (L.Native ("SpecTecFresh.Supply.leave", [ before; returned ])));
            current := after;
            List.iter (fun output ->
              tainted := add_term_variables !tainted output)
              (outputs positions target middle)
        | _ ->
            add premise;
            (match application_name application with
            | Some "$concat_text" ->
                let target = "$concat_text" in
                let call_outputs = outputs positions target application.arguments in
                let input_positions = Option.value
                  (StringMap.find_opt target positions)
                  ~default:(List.init
                    (max 0 (List.length application.arguments - 1)) Fun.id) in
                let call_inputs = List.filteri (fun index _ ->
                  List.mem index input_positions) application.arguments in
                (match fresh_source !tainted call_inputs, call_outputs with
                | Some (source_name, source_type), [ output ] ->
                    let before = resolve !substitutions !current in
                    let next_name = "fresh:derived:" ^ string_of_int rule_index
                      ^ ":" ^ string_of_int premise_index in
                    let next = L.Variable (next_name, supply_type) in
                    binders := !binders @ [ next_name, supply_type ];
                    add (predicate "SpecTecFresh.Derives"
                      [ before; L.Variable (source_name, source_type); output; next ]);
                    (match variable_name before with
                    | Some name ->
                        substitutions := StringMap.add name next_name !substitutions
                    | None -> ());
                    current := next;
                    tainted := add_term_variables !tainted output
                | _ -> ())
            | Some _ -> ()
            | None -> ()))
    | L.Prop proposition ->
        add premise;
        tainted := propagate_equality !tainted proposition
    | L.NotHolds _ | L.NotExists _ -> add premise) rule.premises;
  let conclusion = match List.rev conclusion.arguments with
    | last :: rest when state_variable
        (Option.value (variable_name last) ~default:"") ->
        { conclusion with arguments = List.rev (resolve !substitutions last :: rest) }
    | _ -> conclusion in
  { rule with binders = !binders; premises = !translated; conclusion }

let transform_fresh_state relation =
  match relation with
  | L.Relation ({ name; argument_types; _ } as declaration)
    when ends_with ":state" name ->
      let output_type = match argument_types with
        | _before :: output :: [ _after ] -> output
        | _ -> string_type in
      let before = L.Variable ("fresh:supply:0", supply_type) in
      let output = L.Variable ("fresh:output", output_type) in
      let after = L.Variable ("fresh:supply:1", supply_type) in
      let allocation_site = site "$fresh_typeId" 0 0 in
      L.Relation { declaration with
        name = "$fresh_typeId:supply";
        argument_types = [ supply_type; output_type; supply_type ];
        input_positions = Some [ 0 ];
        rules = [{ L.name = "allocate";
          binders = [ "fresh:supply:0", supply_type;
            "fresh:output", output_type; "fresh:supply:1", supply_type ];
          premises = [ predicate "SpecTecFresh.Allocates"
            [ allocation_site; before; output; after ] ];
          catchable = [];
          conclusion = { target = L.Global "$fresh_typeId:supply";
            type_arguments = []; instance_arguments = [];
            print_instance_arguments = [];
            arguments = [ before; output; after ] } }] }
  | _ -> relation

let transform_relation positions stateful located =
  match located.L.declaration with
  | L.Relation ({ name; argument_types; rules; input_positions; _ } as relation) ->
      if name = "$fresh_typeId:state" then
        { located with declaration = transform_fresh_state located.declaration }
      else
        let is_state = ends_with ":state" name in
        let is_failure =
          (match argument_types with typ :: _ -> typ = nat_type | [] -> false)
          && String.contains name ':'
          && (ends_with ":fail" name ||
              let marker = ":fail:" in
              let rec contains index =
                index + String.length marker <= String.length name
                && (String.sub name index (String.length marker) = marker
                    || contains (index + 1)) in
              contains 0) in
        let base = if is_state then drop_suffix ":state" name else name in
        let state_positions = state_argument_positions rules in
        let state_positions =
          if is_state then
            let positions = IntSet.add 0 state_positions in
            if argument_types = [] then positions
            else IntSet.add (List.length argument_types - 1) positions
          else if is_failure then IntSet.add 0 state_positions
          else state_positions in
        let argument_types = List.mapi (fun index typ ->
          if IntSet.mem index state_positions then supply_type else typ)
          argument_types in
        let input_positions =
          if is_state then Some (0 :: List.map (( + ) 1)
            (Option.value (StringMap.find_opt base positions) ~default:[]))
          else if is_failure then Some (List.init (List.length argument_types) Fun.id)
          else input_positions in
        let rules =
          if name = "$fresh_typeId:fail" then []
          else List.mapi (fun index (rule : L.rule) ->
            if rule.L.name = "from_initial_counter" && StringSet.mem name stateful
            then transform_wrapper positions name rule
            else transform_rule positions base index rule) rules in
        { located with declaration = L.Relation { relation with
          name = if is_state then base ^ ":supply" else name;
          argument_types; input_positions; rules } }
  | _ -> located

let lower declarations =
  if not (List.exists (function
    | { L.declaration = L.Relation { name = "$fresh_typeId"; _ }; _ } -> true
    | _ -> false) declarations)
  then declarations
  else
    let positions = input_positions declarations in
    let stateful = Translator.Fresh_state.effectful declarations in
    Translator.Fresh_state.lower ~rollback:true declarations
    |> List.map (transform_relation positions stateful)

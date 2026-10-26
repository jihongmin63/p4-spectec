module L = Ast.Lean

let print_identifier (name : string) : string = Identifier.print_identifier name

let print_global_name (bound : string list) (name : string) : string =
  let printed : string = print_identifier name in
  if List.mem name bound then "SpecTec." ^ printed else printed

let print_constructor_ref (bound : string list) (reference : L.constructor_ref) :
    string =
  print_global_name bound reference.type_name ^ "."
  ^ print_identifier reference.constructor_name

let rec print_type (bound : string list) (typ : L.type_ref) : string =
  match typ with
  | TypeParameter name -> print_identifier name
  | BuiltinType (name, []) -> "_root_." ^ print_identifier name
  | BuiltinType (name, arguments) ->
      "(" ^ String.concat " "
        (("_root_." ^ print_identifier name)
        :: List.map (print_type bound) arguments)
      ^ ")"
  | Name name -> print_global_name bound name
  | Applied (name, arguments) ->
      "(" ^ String.concat " "
        (print_global_name bound name :: List.map (print_type bound) arguments)
      ^ ")"
  | Pair (left, right) ->
      "(" ^ print_type bound left ^ " × " ^ print_type bound right ^ ")"
  | RelationType (arguments, result) ->
      "(" ^ String.concat " → "
        (List.map (print_type bound) (arguments @ [ result ]) @ [ "Prop" ])
      ^ ")"

let escape_string (value : string) : string =
  let buffer : Buffer.t = Buffer.create (String.length value) in
  String.iter
    (fun character ->
      match character with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | '\r' -> Buffer.add_string buffer "\\r"
      | _ when Char.code character < 32 || Char.code character = 127 ->
          Buffer.add_string buffer (Printf.sprintf "\\x%02X" (Char.code character))
      | _ -> Buffer.add_char buffer character)
    value;
  Buffer.contents buffer

let print_reference (bound : string list) (reference : L.reference) : string =
  match reference with
  | Global name -> print_global_name bound name
  | Local name -> print_identifier name

let rec print_term (bound : string list) (term : L.term) : string =
  let print : L.term -> string = print_term bound in
  match term with
  | Variable (name, _) -> print_identifier name
  | Constructor (reference, arguments) ->
      "(" ^ String.concat " "
        (("@" ^ print_constructor_ref bound reference)
        :: (List.map (print_type bound) reference.type_arguments
           @ List.map print arguments)) ^ ")"
  | Boolean value -> string_of_bool value
  | Number (value, typ) -> "(" ^ value ^ " : " ^ print_type bound typ ^ ")"
  | Text value -> "\"" ^ escape_string value ^ "\""
  | FunctionReference reference -> print_reference bound reference
  | Apply application -> print_application bound application
  | Coerce (name, _, _, value) ->
      "(" ^ print_global_name bound name ^ " " ^ print value ^ ")"
  | MembershipTest (name, _, _, _, _, value) ->
      "(" ^ print_global_name bound name ^ " " ^ print value ^ ")"
  | Lambda (name, typ, body) ->
      "(fun (" ^ print_identifier name ^ " : " ^ print_type bound typ
      ^ ") => " ^ print_term (name :: bound) body ^ ")"
  | Native (name, arguments) ->
      "(" ^ String.concat " " (("_root_." ^ name) :: List.map print arguments) ^ ")"
  | Unary (operator, value) -> "(" ^ operator ^ print value ^ ")"
  | Binary (operator, left, right) -> "(" ^ print left ^ " " ^ operator ^ " " ^ print right ^ ")"
  | Typed (value, typ) -> "(" ^ print value ^ " : " ^ print_type bound typ ^ ")"
  | Tuple (left, right) -> "(" ^ print left ^ ", " ^ print right ^ ")"
  | ListLiteral values -> "[" ^ String.concat ", " (List.map print values) ^ "]"
  | StructureLiteral (typ, fields) ->
      "({ " ^ String.concat ", " (List.map (fun (name, value) -> print_identifier name ^ " := " ^ print value) fields)
      ^ " } : " ^ print_type bound typ ^ ")"
  | StructureUpdate (typ, base, field, value) ->
      "({ " ^ print base ^ " with " ^ print_identifier field ^ " := "
      ^ print value ^ " } : " ^ print_type bound typ ^ ")"
  | Projection (name, field, value) ->
      "(" ^ print_global_name bound name ^ "." ^ print_identifier field ^ " " ^ print value ^ ")"
  | Index (base, index) -> "(" ^ print base ^ "[" ^ print index ^ "]?)"
  | Decide (_, prop) ->
      "(_root_.Decidable.decide " ^ print_prop bound prop ^ ")"

and print_prop (bound : string list) (prop : L.prop) : string =
  match prop with
  | Comparison (operator, left, right) ->
      let operator : string = match operator with
        | Eq -> "=" | Ne -> "≠" | Lt -> "<" | Le -> "≤" | Gt -> ">" | Ge -> "≥"
      in
      "(" ^ print_term bound left ^ " " ^ operator ^ " " ^ print_term bound right ^ ")"
  | Membership (element, collection) ->
      "(" ^ print_term bound element ^ " ∈ " ^ print_term bound collection ^ ")"

  | IsTrue term -> "(" ^ print_term bound term ^ " = true)"
  | Predicate term -> print_term bound term
  | Not prop -> "(¬ " ^ print_prop bound prop ^ ")"
  | And (left, right) -> print_connective bound "∧" left right
  | Or (left, right) -> print_connective bound "∨" left right
  | Implies (left, right) -> print_connective bound "→" left right
  | Iff (left, right) -> print_connective bound "↔" left right

and print_connective (bound : string list) (operator : string)
    (left : L.prop) (right : L.prop) : string =
  "(" ^ print_prop bound left ^ " " ^ operator ^ " " ^ print_prop bound right ^ ")"

and print_application (bound : string list) (application : L.application) : string =
  let name : string = print_reference bound application.target in
  let name : string =
    match application.type_arguments with [] -> name | _ -> "@" ^ name
  in
  let arguments : string list =
    List.map (print_type bound) application.type_arguments
    @ List.map (fun _ -> "_") application.instance_arguments
    @ List.map (print_term bound) application.arguments
  in
  match arguments with
  | [] -> name
  | _ -> "(" ^ String.concat " " (name :: arguments) ^ ")"

let print_premise (bound : string list) (premise : L.premise) : string =
  match premise with
  | Holds application -> print_application bound application
  | NotHolds (application, _) -> "(¬ " ^ print_application bound application ^ ")"
  | NotExists (binders, application, _) ->
      let bound : string list = bound @ List.map fst binders in
      let body : string = print_application bound application in
      let quantified : string = List.fold_right
        (fun (name, typ) body ->
          "∃ (" ^ print_identifier name ^ " : " ^ print_type bound typ ^ "), " ^ body)
        binders body
      in
      "(¬ " ^ quantified ^ ")"
  | Prop prop -> print_prop bound prop

let print_constructor (type_parameters : string list) (constructor : L.constructor) :
    string =
  let signature : string =
    String.concat " → "
      (List.map (print_type type_parameters)
         (constructor.arguments @ [ constructor.result ]))
  in
  Printf.sprintf "  | %s : %s" (print_identifier constructor.name) signature

let print_rule (type_parameters : string list) (rule : L.rule) : string =
  let bound : string list = type_parameters @ List.map fst rule.binders in
  let binders : string list =
    List.map
      (fun (name, typ) ->
        "(" ^ print_identifier name ^ " : " ^ print_type bound typ ^ ")")
      rule.binders
  in
  let premises : string list = List.map (print_premise bound) rule.premises in
  let result : string = print_application bound rule.conclusion in
  let signature : string =
    let body : string = String.concat " → " (premises @ [ result ]) in
    match binders with
    | [] -> body
    | _ -> "∀ " ^ String.concat " " binders ^ ", " ^ body
  in
  Printf.sprintf "  | %s : %s" (print_identifier rule.name) signature

let print_builtin (builtin : L.builtin) : string =
  let type_parameters : string list =
    List.map
      (fun name -> "{" ^ print_identifier name ^ " : Type}")
      builtin.type_parameters
  in
  let equality_parameters : string list =
    List.map
      (fun name -> "[_root_.DecidableEq " ^ print_identifier name ^ "]")
      builtin.equality_parameters
  in
  let parameters : string list =
    List.mapi
      (fun index typ ->
        "(arg" ^ string_of_int index ^ " : " ^ print_type [] typ ^ ")")
      builtin.parameters
  in
  let binders : string list = type_parameters @ equality_parameters @ parameters in
  let binders : string =
    match binders with [] -> "" | _ -> " " ^ String.concat " " binders
  in
  Printf.sprintf "def %s%s : %s := %s" (print_identifier builtin.name)
    binders (print_type [] builtin.result) builtin.body

let quote_notation_literal (literal : string) : string =
  "\"" ^ escape_string literal ^ "\""

let print_notation (name : string) (parts : L.notation_part list) : string =
  let (_, pattern, arguments) : int * string list * string list =
    List.fold_left
      (fun (index, pattern, arguments) part ->
        match part with
        | L.Hole ->
            let argument : string = "x" ^ string_of_int index in
            (index + 1, pattern @ [ argument ^ ":arg" ], arguments @ [ argument ])
        | L.Literal literal ->
            (index, pattern @ [ quote_notation_literal literal ], arguments))
      (0, [], []) parts
  in
  Printf.sprintf "notation:50 %s => %s" (String.concat " " pattern)
    (String.concat " " (print_global_name [] name :: arguments))

let print_type_parameters (parameters : string list) : string =
  match parameters with
  | [] -> ""
  | _ -> " (" ^ String.concat " " (List.map print_identifier parameters) ^ " : Type)"

let print_declaration ?(derive_decidable_eq = false)
    (declaration : L.declaration) : string =
  let deriving (printed : string) : string =
    if derive_decidable_eq then printed ^ "\nderiving _root_.DecidableEq"
    else printed
  in
  match declaration with
  | Datatype { name; type_parameters; constructors } ->
      deriving
        (String.concat "\n"
          (Printf.sprintf "inductive %s%s : Type where" (print_identifier name)
            (print_type_parameters type_parameters)
          :: List.map (print_constructor type_parameters) constructors))
  | TypeAlias { name; type_parameters; body } ->
      Printf.sprintf "abbrev %s%s : Type := %s" (print_identifier name)
        (print_type_parameters type_parameters) (print_type type_parameters body)
  | Structure { name; fields } ->
      let bound : string list = List.map fst fields in
      deriving
        (String.concat "\n"
          (Printf.sprintf "structure %s : Type where" (print_identifier name)
          :: List.map
               (fun (field_name, typ) ->
                 let printed : string = print_identifier field_name in
                 let quoted : string =
                   if String.starts_with ~prefix:"«" printed then printed
                   else "«" ^ printed ^ "»"
                 in
                 "  (" ^ quoted ^ " : " ^ print_type bound typ ^ ")")
               fields))
  | Relation
      { name; type_parameters; equality_parameters; argument_types; rules;
        notation = _ } ->
      let signature : string =
        String.concat " → "
          (List.map (print_type type_parameters) argument_types @ [ "Prop" ])
      in
      let parameters : string =
        String.concat ""
          (List.map
             (fun name -> " {" ^ print_identifier name ^ " : Type}")
             type_parameters
          @ List.map
              (fun name -> " [_root_.DecidableEq " ^ print_identifier name ^ "]")
              equality_parameters)
      in
      let declaration : string =
        String.concat "\n"
          (Printf.sprintf "inductive %s%s : %s where"
             (print_identifier name) parameters signature
          :: List.map (print_rule type_parameters) rules)
      in
      declaration
  | Builtin builtin -> print_builtin builtin
  | Coercion { name; source; target; type_parameters; cases } ->
      let parameters : string = String.concat ""
        (List.map (fun parameter ->
           " {" ^ print_identifier parameter ^ " : Type}") type_parameters)
      in
      let clauses : string list = List.map
        (fun (source_name, target_name, arity) ->
          let arguments : string list = List.init arity (fun index -> "a" ^ string_of_int index) in
          "  | ." ^ print_identifier source_name ^ " " ^ String.concat " " arguments
          ^ " => (." ^ print_identifier target_name ^ " "
          ^ String.concat " " arguments ^ ")")
        cases
      in
      String.concat "\n"
        (Printf.sprintf "def %s%s : %s → %s" (print_identifier name)
           parameters (print_type type_parameters source)
           (print_type type_parameters target) :: clauses)
  | Membership { name; source; target = _; type_parameters; cases; exhaustive } ->
      let parameters : string = String.concat ""
        (List.map (fun parameter ->
           " {" ^ print_identifier parameter ^ " : Type}") type_parameters)
      in
      let clauses : string list = List.map
        (fun (constructor, arity) ->
          "  | ." ^ print_identifier constructor
          ^ String.concat "" (List.init arity (fun _ -> " _")) ^ " => true")
        cases
      in
      let clauses : string list =
        if exhaustive then clauses else clauses @ [ "  | _ => false" ]
      in
      String.concat "\n"
        (Printf.sprintf "def %s%s : %s → Bool" (print_identifier name)
           parameters (print_type type_parameters source) :: clauses)

let declaration_notation (declaration : L.declaration) : string list =
  match declaration with
  | Relation { name; notation = Some parts; _ } -> [ print_notation name parts ]
  | _ -> []

let print_equality_parameters (parameters : string list) : string =
  String.concat ""
    (List.map
       (fun parameter ->
         " {" ^ print_identifier parameter ^ " : Type} [_root_.DecidableEq "
         ^ print_identifier parameter ^ "]")
       parameters)

let equality_call (shapes : L.equality_shape list) (typ : L.type_ref)
    (left : string) (right : string) : string =
  match
    List.find_opt
      (fun (shape : L.equality_shape) -> shape.equality_type = typ)
      shapes
  with
  | Some shape ->
      print_identifier shape.equality_name ^ " " ^ left ^ " " ^ right
  | None -> "_root_.decEq " ^ left ^ " " ^ right

let equality_result (shapes : L.equality_shape list)
    (indent : string) (fields : L.type_ref list) : string =
  match fields with
  | [] -> "_root_.Decidable.isTrue rfl"
  | _ ->
      let hypotheses : string list =
        List.mapi (fun index _ -> "h" ^ string_of_int index) fields
      in
      let true_proof : string =
        "_root_.Decidable.isTrue (by "
        ^ String.concat "; " (List.map (fun name -> "cases " ^ name) hypotheses)
        ^ "; rfl)"
      in
      let rec nested (index : int) (indent : string)
          (remaining : L.type_ref list) : string =
        match remaining with
        | [] -> true_proof
        | typ :: rest ->
            let name : string = "h" ^ string_of_int index in
            "match "
            ^ equality_call shapes typ ("x" ^ string_of_int index)
                ("y" ^ string_of_int index)
            ^ " with\n" ^ indent ^ "| _root_.Decidable.isTrue " ^ name ^ " =>\n"
            ^ indent ^ "  " ^ nested (index + 1) (indent ^ "  ") rest
            ^ "\n" ^ indent ^ "| _root_.Decidable.isFalse " ^ name
            ^ " => _root_.Decidable.isFalse (by intro e; injection e; contradiction)"
      in
      nested 0 indent fields

let constructor_pattern (constructor : L.constructor) (prefix : string) : string =
  let arguments : string list =
    List.mapi (fun index _ -> prefix ^ string_of_int index) constructor.arguments
  in
  "." ^ print_identifier constructor.name
  ^ match arguments with [] -> "" | _ -> " " ^ String.concat " " arguments

let constructor_wildcard (constructor : L.constructor) : string =
  "." ^ print_identifier constructor.name
  ^ String.concat "" (List.map (fun _ -> " _") constructor.arguments)

let print_datatype_equality (shapes : L.equality_shape list)
    (constructors : L.constructor list) : string =
  let cases : string list =
    List.map
      (fun (constructor : L.constructor) ->
        "    | " ^ constructor_pattern constructor "x" ^ ", "
        ^ constructor_pattern constructor "y" ^ " =>\n      "
        ^ equality_result shapes "      " constructor.arguments)
      constructors
  in
  match constructors with
  | [] -> "nomatch a"
  | [ _ ] -> "match a, b with\n" ^ String.concat "\n" cases
  | _ ->
      let mismatches : string list =
        List.concat_map
          (fun (left : L.constructor) ->
            List.filter_map
              (fun (right : L.constructor) ->
                if left.name = right.name then None
                else
                  Some
                    ("    | " ^ constructor_wildcard left ^ ", "
                    ^ constructor_wildcard right ^ " => nomatch hc"))
              constructors)
          constructors
      in
      "if hc : a.ctorIdx = b.ctorIdx then\n"
      ^ "    match a, b with\n"
      ^ String.concat "\n" (cases @ mismatches)
      ^ "\n  else _root_.Decidable.isFalse (fun e => hc (e ▸ rfl))"

let print_structure_equality (shapes : L.equality_shape list)
    (fields : (string * L.type_ref) list) : string =
  let variables (prefix : string) : string =
    "⟨" ^ String.concat ", "
      (List.mapi (fun index _ -> prefix ^ string_of_int index) fields) ^ "⟩"
  in
  "match a, b with\n  | " ^ variables "x" ^ ", " ^ variables "y" ^ " =>\n    "
  ^ equality_result shapes "    " (List.map snd fields)

let print_list_equality (shapes : L.equality_shape list)
    (element : L.type_ref) : string =
  "match a, b with\n"
  ^ "  | [], [] => _root_.Decidable.isTrue rfl\n"
  ^ "  | x0 :: x1, y0 :: y1 =>\n    "
  ^ equality_result shapes "    "
      [ element; L.BuiltinType ("List", [ element ]) ]
  ^ "\n  | [], _ :: _ => _root_.Decidable.isFalse (by intro e; cases e)\n"
  ^ "  | _ :: _, [] => _root_.Decidable.isFalse (by intro e; cases e)"

let print_option_equality (shapes : L.equality_shape list)
    (element : L.type_ref) : string =
  "match a, b with\n"
  ^ "  | _root_.Option.none, _root_.Option.none => _root_.Decidable.isTrue rfl\n"
  ^ "  | _root_.Option.some x0, _root_.Option.some y0 =>\n    "
  ^ equality_result shapes "    " [ element ]
  ^ "\n  | _root_.Option.none, _root_.Option.some _ => _root_.Decidable.isFalse (by intro e; cases e)\n"
  ^ "  | _root_.Option.some _, _root_.Option.none => _root_.Decidable.isFalse (by intro e; cases e)"

let print_pair_equality (shapes : L.equality_shape list)
    (left : L.type_ref) (right : L.type_ref) : string =
  "match a, b with\n  | (x0, x1), (y0, y1) =>\n    "
  ^ equality_result shapes "    " [ left; right ]

let print_equality_shape (equality : L.manual_equality)
    (shape : L.equality_shape) : string =
  let parameters : string =
    print_equality_parameters equality.equality_type_parameters
  in
  let bound : string list = equality.equality_type_parameters in
  let body : string =
    match shape.equality_kind with
    | EqualityDatatype constructors ->
        print_datatype_equality equality.equality_shapes constructors
    | EqualityStructure fields ->
        print_structure_equality equality.equality_shapes fields
    | EqualityList element ->
        print_list_equality equality.equality_shapes element
    | EqualityOption element ->
        print_option_equality equality.equality_shapes element
    | EqualityPair (left, right) ->
        print_pair_equality equality.equality_shapes left right
  in
  Printf.sprintf "def %s%s (a b : %s) : _root_.Decidable (a = b) :=\n  %s\ntermination_by structural a"
    (print_identifier shape.equality_name) parameters
    (print_type bound shape.equality_type) body

let print_manual_equality (equality : L.manual_equality) : string =
  let functions : string =
    "mutual\n\n"
    ^ String.concat "\n\n"
        (List.map (print_equality_shape equality) equality.equality_shapes)
    ^ "\n\nend"
  in
  let parameters : string =
    print_equality_parameters equality.equality_type_parameters
  in
  let bound : string list = equality.equality_type_parameters in
  let instances : string list =
    List.map
      (fun (typ, name) ->
        Printf.sprintf "instance%s : _root_.DecidableEq %s := %s" parameters
          (print_type bound typ) (print_identifier name))
      equality.equality_instances
  in
  String.concat "\n\n" (functions :: instances)

let rec print_group (group : L.declaration_group) : string =
  match group with
  | Single declaration ->
      String.concat "\n\n"
        (print_declaration declaration :: declaration_notation declaration)
  | Mutual declarations ->
      String.concat "\n\n"
        (("mutual\n\n"
         ^ String.concat "\n\n" (List.map print_declaration declarations)
         ^ "\n\nend")
        :: List.concat_map declaration_notation declarations)
  | DerivingDecidableEq (Single declaration) ->
      String.concat "\n\n"
        (print_declaration ~derive_decidable_eq:true declaration
         :: declaration_notation declaration)
  | DerivingDecidableEq (Mutual declarations) ->
      String.concat "\n\n"
        (("mutual\n\n"
         ^ String.concat "\n\n"
             (List.map (print_declaration ~derive_decidable_eq:true) declarations)
         ^ "\n\nend")
        :: List.concat_map declaration_notation declarations)
  | DerivingDecidableEq group -> print_group group
  | ManualDecidableEq equality -> print_manual_equality equality

let print (program : L.program) : string =
  "set_option autoImplicit false\nset_option linter.unusedVariables false\n\nnamespace SpecTec\n\n"
  ^ String.concat "\n\n" (List.map print_group program)
  ^ "\n\nend SpecTec"

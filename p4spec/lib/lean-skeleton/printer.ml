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
  | Projection (name, field, value) ->
      "(" ^ print_global_name bound name ^ "." ^ print_identifier field ^ " " ^ print value ^ ")"
  | Index (base, index) -> "(" ^ print base ^ "[" ^ print index ^ "]?)"
  | Decide prop -> "(_root_.Decidable.decide " ^ print_prop bound prop ^ ")"

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
  let parameters : string list =
    List.mapi
      (fun index typ ->
        "(arg" ^ string_of_int index ^ " : " ^ print_type [] typ ^ ")")
      builtin.parameters
  in
  let binders : string list = type_parameters @ parameters in
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

let print_declaration (declaration : L.declaration) : string =
  match declaration with
  | Datatype { name; type_parameters; constructors } ->
      String.concat "\n"
        (Printf.sprintf "inductive %s%s : Type where" (print_identifier name)
          (print_type_parameters type_parameters)
        :: List.map (print_constructor type_parameters) constructors)
  | TypeAlias { name; type_parameters; body } ->
      Printf.sprintf "abbrev %s%s : Type := %s" (print_identifier name)
        (print_type_parameters type_parameters) (print_type type_parameters body)
  | Structure { name; fields } ->
      let bound : string list = List.map fst fields in
      String.concat "\n"
        (Printf.sprintf "structure %s : Type where" (print_identifier name)
        :: List.map
             (fun (field_name, typ) ->
               let printed : string = print_identifier field_name in
               let quoted : string =
                 if String.starts_with ~prefix:"«" printed then printed
                 else "«" ^ printed ^ "»"
               in
               "  (" ^ quoted ^ " : " ^ print_type bound typ ^ ")")
             fields)
  | Relation { name; type_parameters; argument_types; rules; notation = _ } ->
      let signature : string =
        String.concat " → "
          (List.map (print_type type_parameters) argument_types @ [ "Prop" ])
      in
      let parameters : string =
        String.concat ""
          (List.map
             (fun name -> " {" ^ print_identifier name ^ " : Type}")
             type_parameters)
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

let declaration_notation (declaration : L.declaration) : string list =
  match declaration with
  | Relation { name; notation = Some parts; _ } -> [ print_notation name parts ]
  | _ -> []

let print_group (group : L.declaration_group) : string =
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

let print (program : L.program) : string =
  "set_option autoImplicit false\nset_option linter.unusedVariables false\n\nnamespace SpecTec\n\n"
  ^ String.concat "\n\n" (List.map print_group program)
  ^ "\n\nend SpecTec"

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
  | TupleType elements -> print_tuple_type bound elements
  | RelationType (arguments, result) ->
      "(" ^ String.concat " → "
        (List.map (print_type bound) (arguments @ [ result ]) @ [ "Prop" ])
      ^ ")"

and print_tuple_type (bound : string list) (elements : L.type_ref list) : string =
  match elements with
  | [] -> invalid_arg "cannot print an empty tuple type"
  | [ element ] -> print_type bound element
  | first :: rest ->
      "(" ^ print_type bound first ^ " × " ^ print_tuple_type bound rest ^ ")"

let tuple_pattern (prefix : string) (elements : L.type_ref list) : string =
  let rec nest (index : int) (remaining : L.type_ref list) : string =
    match remaining with
    | [] -> invalid_arg "cannot print an empty tuple pattern"
    | [ _ ] -> prefix ^ string_of_int index
    | _ :: rest ->
        "(" ^ prefix ^ string_of_int index ^ ", " ^ nest (index + 1) rest
        ^ ")"
  in
  nest 0 elements

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

let print_prelude : string =
  {lean|class SpecTecPrint (α : Type) where
  print? : α → Option String

def specTecPrintFiltered (parts : List (Option String)) : Option String :=
  match parts.filterMap id with
  | [] => none
  | present => some (" ".intercalate present)

def specTecPrintSequence (parts : List (Option String)) : Option String :=
  some (" ".intercalate (parts.map (fun part => part.getD "")))

def specTecPrintFuse (left right : Option String) : Option String :=
  some (left.getD "" ++ right.getD "")

def specTecPrintFinish (fragment : Option String) : String :=
  fragment.getD ""

def specTecPrintDecimalByte (value : Nat) : String :=
  String.ofList
    [ Char.ofNat (48 + value / 100),
      Char.ofNat (48 + (value / 10) % 10),
      Char.ofNat (48 + value % 10) ]

def specTecPrintEscapeByte (byte : UInt8) : String :=
  let value := byte.toNat
  match value with
  | 34 => "\\\""
  | 92 => "\\\\"
  | 10 => "\\n"
  | 9 => "\\t"
  | 13 => "\\r"
  | 8 => "\\b"
  | value =>
      if 32 ≤ value ∧ value ≤ 126 then String.singleton (Char.ofNat value)
      else "\\" ++ specTecPrintDecimalByte value

def specTecPrintEscapeText (value : String) : String :=
  value.toUTF8.foldl (fun result byte => result ++ specTecPrintEscapeByte byte) ""

instance : SpecTecPrint Bool :=
  ⟨fun value => some (if value then "true" else "false")⟩

instance : SpecTecPrint Nat := ⟨fun value => some (toString value)⟩

instance : SpecTecPrint Int := ⟨fun value => some (toString value)⟩

instance : SpecTecPrint String :=
  ⟨fun value => some (specTecPrintEscapeText value)⟩

def specTecPrintList {α : Type} [SpecTecPrint α]
    (value : List α) : Option String :=
  match value with
  | [] => some ""
  | head :: tail => do
      let printedHead ← SpecTecPrint.print? head
      let printedTail ← specTecPrintList tail
      return match tail with
        | [] => printedHead
        | _ => printedHead ++ " " ++ printedTail
termination_by structural value

instance {α : Type} [SpecTecPrint α] : SpecTecPrint (List α) :=
  ⟨specTecPrintList⟩

def specTecPrintOption {α : Type} [SpecTecPrint α]
    (value : Option α) : Option String :=
  match value with
  | none => some ""
  | some item => SpecTecPrint.print? item

instance {α : Type} [SpecTecPrint α] : SpecTecPrint (Option α) :=
  ⟨specTecPrintOption⟩

instance {α β : Type} [SpecTecPrint α] [SpecTecPrint β] :
    SpecTecPrint (α × β) :=
  ⟨fun value => do
    let left ← SpecTecPrint.print? value.1
    let right ← SpecTecPrint.print? value.2
    return "(" ++ left ++ ", " ++ right ++ ")"⟩|lean}

let print_reference (bound : string list) (reference : L.reference) : string =
  match reference with
  | Global name -> print_global_name bound name
  | Local name -> print_identifier name

let rec print_instance (bound : string list) (typ : L.type_ref) : string =
  let annotated (body : string) : string =
    "({ print? := " ^ body ^ " } : _root_.SpecTecPrint "
    ^ print_type bound typ ^ ")"
  in
  match typ with
  | TypeParameter _ | BuiltinType (_, []) -> "_"
  | BuiltinType ("List", [ element ]) ->
      annotated
        ("@_root_.specTecPrintList " ^ print_type bound element ^ " "
        ^ print_instance bound element)
  | BuiltinType ("Option", [ element ]) ->
      annotated
        ("@_root_.specTecPrintOption " ^ print_type bound element ^ " "
        ^ print_instance bound element)
  | TupleType elements ->
      let bindings : string list =
        List.mapi
          (fun index element ->
            "      let s" ^ string_of_int index
            ^ " ← @_root_.SpecTecPrint.print? " ^ print_type bound element
            ^ " " ^ print_instance bound element ^ " x" ^ string_of_int index)
          elements
      in
      annotated
        ("fun value => match value with\n"
        ^ "    | " ^ tuple_pattern "x" elements ^ " => do\n"
        ^ String.concat "\n" bindings ^ "\n"
        ^ "      return \"(\" ++ \", \".intercalate ["
        ^ String.concat ", "
            (List.mapi (fun index _ -> "s" ^ string_of_int index) elements)
        ^ "] ++ \")\"")
  | RelationType _ -> annotated "fun _ => _root_.Option.none"
  | Name name -> annotated (print_identifier ("print_" ^ name))
  | Applied (name, arguments) ->
      let parameters : string list =
        List.map (print_type bound) arguments
        @ List.map (print_instance bound) arguments
      in
      annotated
        ("@" ^ print_identifier ("print_" ^ name) ^ " "
        ^ String.concat " " parameters)
  | BuiltinType _ -> "_"

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
    @ List.map (print_instance bound) application.print_instance_arguments
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
  let print_parameters : string list =
    List.map
      (fun name -> "[_root_.SpecTecPrint " ^ print_identifier name ^ "]")
      builtin.print_parameters
  in
  let parameters : string list =
    List.mapi
      (fun index typ ->
        "(arg" ^ string_of_int index ^ " : " ^ print_type [] typ ^ ")")
      builtin.parameters
  in
  let binders : string list =
    type_parameters @ equality_parameters @ print_parameters @ parameters in
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
      { name; type_parameters; equality_parameters; print_parameters;
        argument_types; rules; notation = _ } ->
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
              equality_parameters
          @ List.map
              (fun name ->
                " [_root_.SpecTecPrint " ^ print_identifier name ^ "]")
              print_parameters)
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

let equality_result ?(flat_tuple = false) (shapes : L.equality_shape list)
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
            ^ " => _root_.Decidable.isFalse "
            ^ (if flat_tuple then
                 "(by intro e; cases e; exact " ^ name ^ " rfl)"
               else "(by intro e; injection e; contradiction)")
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

let print_tuple_equality (shapes : L.equality_shape list)
    (elements : L.type_ref list) : string =
  "match a, b with\n  | " ^ tuple_pattern "x" elements ^ ", "
  ^ tuple_pattern "y" elements ^ " =>\n    "
  ^ equality_result ~flat_tuple:true shapes "    " elements

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
    | EqualityTuple elements ->
        print_tuple_equality equality.equality_shapes elements
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

let print_printer_parameters (parameters : string list) : string =
  String.concat ""
    (List.map
       (fun parameter ->
         " {" ^ print_identifier parameter ^ " : Type} [_root_.SpecTecPrint "
         ^ print_identifier parameter ^ "]")
       parameters)

let rec contains_flat_tuple (typ : L.type_ref) : bool =
  match typ with
  | TupleType (_ :: _ :: _ :: _) -> true
  | TupleType arguments | BuiltinType (_, arguments) | Applied (_, arguments) ->
      List.exists contains_flat_tuple arguments
  | RelationType (arguments, result) ->
      List.exists contains_flat_tuple (result :: arguments)
  | Name _ | TypeParameter _ -> false

(* Instance search would print a flat tuple of three or more elements with
   the binary product instance, which nests the parentheses. *)
let printer_call (bound : string list) (shapes : L.print_shape list)
    (typ : L.type_ref) (value : string) : string =
  match
    List.find_opt (fun (shape : L.print_shape) -> shape.print_type = typ) shapes
  with
  | Some shape -> print_identifier shape.print_name ^ " " ^ value
  | None when contains_flat_tuple typ ->
      "@_root_.SpecTecPrint.print? " ^ print_type bound typ ^ " "
      ^ print_instance bound typ ^ " " ^ value
  | None -> "_root_.SpecTecPrint.print? " ^ value

let rec print_format (format : L.print_format) : string =
  match format with
  | PrintAbsent -> "_root_.Option.none"
  | PrintLiteral value ->
      "_root_.Option.some \"" ^ escape_string value ^ "\""
  | PrintHole index -> "_root_.Option.some s" ^ string_of_int index
  | PrintFilteredJoin parts ->
      "_root_.specTecPrintFiltered ["
      ^ String.concat ", " (List.map print_format parts) ^ "]"
  | PrintSequence parts ->
      "_root_.specTecPrintSequence ["
      ^ String.concat ", " (List.map print_format parts) ^ "]"
  | PrintFuse (left, right) ->
      "_root_.specTecPrintFuse (" ^ print_format left ^ ") ("
      ^ print_format right ^ ")"

let print_do (bound : string list) (shapes : L.print_shape list)
    (fields : (L.type_ref * string) list) (used : int list)
    (result : string) : string =
  let bindings : string list =
    List.mapi
      (fun index (typ, value) ->
        if List.mem index used then
          Some
            ("      let s" ^ string_of_int index ^ " ← "
            ^ printer_call bound shapes typ value)
        else None)
      fields
    |> List.filter_map Fun.id
  in
  "do\n" ^ String.concat "\n" bindings ^
  (if bindings = [] then "" else "\n") ^ "      return " ^ result

let print_datatype_printer (bound : string list) (shapes : L.print_shape list)
    (constructors : L.constructor list) : string =
  match constructors with
  | [] -> "nomatch value"
  | _ ->
      "match value with\n"
      ^ String.concat "\n"
          (List.map
             (fun (constructor : L.constructor) ->
               let fields : (L.type_ref * string) list =
                 List.mapi
                   (fun index typ -> typ, "x" ^ string_of_int index)
                   constructor.arguments
               in
               "  | " ^ constructor_pattern constructor "x" ^ " => "
               ^ print_do bound shapes fields
                   (L.print_format_holes constructor.print_format)
                   ("_root_.specTecPrintFinish ("
                   ^ print_format constructor.print_format ^ ")"))
             constructors)

let print_list_printer (bound : string list) (shapes : L.print_shape list)
    (typ : L.type_ref)
    (element : L.type_ref) : string =
  "match value with\n"
  ^ "  | [] => _root_.Option.some \"\"\n"
  ^ "  | head :: tail => do\n"
  ^ "      let printedHead ← " ^ printer_call bound shapes element "head" ^ "\n"
  ^ "      let printedTail ← " ^ printer_call bound shapes typ "tail" ^ "\n"
  ^ "      return match tail with\n"
  ^ "        | [] => printedHead\n"
  ^ "        | _ => printedHead ++ \" \" ++ printedTail"

let print_option_printer (bound : string list) (shapes : L.print_shape list)
    (element : L.type_ref) : string =
  "match value with\n"
  ^ "  | _root_.Option.none => _root_.Option.some \"\"\n"
  ^ "  | _root_.Option.some item => " ^ printer_call bound shapes element "item"

let print_tuple_printer (bound : string list) (shapes : L.print_shape list)
    (elements : L.type_ref list) : string =
  let fields : (L.type_ref * string) list =
    List.mapi (fun index typ -> typ, "x" ^ string_of_int index) elements
  in
  "match value with\n  | " ^ tuple_pattern "x" elements ^ " => "
  ^ print_do bound shapes fields (List.init (List.length fields) Fun.id)
      ("\"(\" ++ \", \".intercalate ["
      ^ String.concat ", "
          (List.mapi (fun index _ -> "s" ^ string_of_int index) elements)
      ^ "] ++ \")\"")

let print_shape_children (shape : L.print_shape) : L.type_ref list =
  match shape.print_kind with
  | PrintDatatype constructors ->
      List.concat_map
        (fun (constructor : L.constructor) ->
          let used : int list =
            L.print_format_holes constructor.print_format in
          List.filteri
            (fun index _ -> List.mem index used)
            constructor.arguments)
        constructors
  | PrintList element -> [ shape.print_type; element ]
  | PrintOption element -> [ element ]
  | PrintTuple elements -> elements
  | PrintStructure | PrintFailure -> []

let recursive_print_shape (shapes : L.print_shape list)
    (start : L.print_shape) : bool =
  let rec reaches_start (seen : L.type_ref list) (shape : L.print_shape) : bool =
    List.exists
      (fun typ ->
        if typ = start.print_type then true
        else if List.mem typ seen then false
        else
          match
            List.find_opt
              (fun (candidate : L.print_shape) ->
                candidate.print_type = typ)
              shapes
          with
          | None -> false
          | Some next -> reaches_start (typ :: seen) next)
      (print_shape_children shape)
  in
  reaches_start [ start.print_type ] start

let print_printer_shape (printer : L.manual_printer)
    (shape : L.print_shape) : string =
  let parameters : string =
    print_printer_parameters printer.printer_type_parameters in
  let bound : string list = printer.printer_type_parameters in
  let body : string =
    match shape.print_kind with
    | PrintDatatype constructors ->
        print_datatype_printer bound printer.printer_shapes constructors
    | PrintStructure | PrintFailure -> "_root_.Option.none"
    | PrintList element ->
        print_list_printer bound printer.printer_shapes shape.print_type element
    | PrintOption element ->
        print_option_printer bound printer.printer_shapes element
    | PrintTuple elements ->
        print_tuple_printer bound printer.printer_shapes elements
  in
  Printf.sprintf
    "def %s%s (value : %s) : _root_.Option _root_.String :=\n  %s%s"
    (print_identifier shape.print_name) parameters
    (print_type bound shape.print_type) body
    (if recursive_print_shape printer.printer_shapes shape then
       "\ntermination_by structural value"
     else "")

let print_manual_printer (printer : L.manual_printer) : string =
  let functions : string =
    "mutual\n\n"
    ^ String.concat "\n\n"
        (List.map (print_printer_shape printer) printer.printer_shapes)
    ^ "\n\nend"
  in
  let parameters : string =
    print_printer_parameters printer.printer_type_parameters in
  let bound : string list = printer.printer_type_parameters in
  let instances : string list =
    List.map
      (fun (typ, name) ->
        Printf.sprintf "instance%s : _root_.SpecTecPrint %s := ⟨%s⟩"
          parameters (print_type bound typ) (print_identifier name))
      printer.printer_instances
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
  | ManualPrinter printer -> print_manual_printer printer

let print (program : L.program) : string =
  "set_option autoImplicit false\nset_option linter.unusedVariables false\n\n"
  ^ print_prelude ^ "\n\nnamespace SpecTec\n\n"
  ^ String.concat "\n\n" (List.map print_group program)
  ^ "\n\nend SpecTec"

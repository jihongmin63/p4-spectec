module L = Ast.Lean
module StringMap = Map.Make (String)
module StringSet = Set.Make (String)

let extern_types_active = ref false
let atom_has_extern_types = ref false
let program_has_p4_extern_model = ref false
let program_has_extern_types = ref false
let extern_relation_names : StringSet.t ref = ref StringSet.empty
let model_relation_names : StringSet.t ref = ref StringSet.empty

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
      "(_root_.SpecTecRelationRef "
      ^ (match arguments with
        | [] -> "_root_.Unit"
        | _ -> print_tuple_type bound arguments)
      ^ " " ^ print_type bound result ^ ")"

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

def specTecTextSetInsert (value : String) : List String → List String
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail
      else if head < value then head :: specTecTextSetInsert value tail
      else head :: tail

def specTecTextSetNormalize (values : List String) : List String :=
  values.foldr specTecTextSetInsert []

def specTecTextSetUnion (left right : List String) : List String :=
  specTecTextSetNormalize (left ++ right)

def specTecTextSetDiff (left right : List String) : List String :=
  let normalizedRight := specTecTextSetNormalize right
  (specTecTextSetNormalize left).filter (fun value => !normalizedRight.contains value)

def specTecTextSetIntersect (left right : List String) : List String :=
  let normalizedRight := specTecTextSetNormalize right
  (specTecTextSetNormalize left).filter (fun value => normalizedRight.contains value)

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
    return "(" ++ left ++ ", " ++ right ++ ")"⟩

inductive SpecTecRelationRef (α β : Type) : Type where
  | named : String → SpecTecRelationRef α β
  | external : (α → β → Prop) → SpecTecRelationRef α β|lean}

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
      if !extern_types_active then
        let result_type : L.type_ref =
          match reference.type_arguments with
          | [] -> L.Name reference.type_name
          | arguments -> L.Applied (reference.type_name, arguments)
        in
        "((" ^ String.concat " "
          (print_constructor_ref bound reference :: List.map print arguments)
        ^ ") : " ^ print_type bound result_type ^ ")"
      else
        "(" ^ String.concat " "
          (("@" ^ print_constructor_ref bound reference)
          :: (List.map (print_type bound) reference.type_arguments
             @ List.map print arguments)) ^ ")"
  | Boolean value ->
      let name = string_of_bool value in
      if List.mem name bound then "_root_.Bool." ^ name else name
  | Number (value, typ) -> "(" ^ value ^ " : " ^ print_type bound typ ^ ")"
  | Text value -> "\"" ^ escape_string value ^ "\""
  | FunctionReference { target = Global name; _ } ->
      "(_root_.SpecTecRelationRef.named \"" ^ escape_string name ^ "\")"
  | FunctionReference { target = Local name; _ } -> print_identifier name
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

  | IsTrue term -> "(" ^ print_term bound term ^ " = "
      ^ print_term bound (L.Boolean true) ^ ")"
  | Predicate term -> print_term bound term
  | Not prop -> "(¬ " ^ print_prop bound prop ^ ")"
  | And (left, right) -> print_connective bound "∧" left right
  | Or (left, right) -> print_connective bound "∨" left right
  | Implies (left, right) -> print_connective bound "→" left right
  | Iff (left, right) -> print_connective bound "↔" left right
  | Forall (name, typ, body) ->
      let printed_type : string = print_type bound typ in
      let body_bound : string list = name :: bound in
      "(∀ (" ^ print_identifier name ^ " : " ^ printed_type ^ "), "
      ^ print_prop body_bound body ^ ")"

and print_connective (bound : string list) (operator : string)
    (left : L.prop) (right : L.prop) : string =
  "(" ^ print_prop bound left ^ " " ^ operator ^ " " ^ print_prop bound right ^ ")"

and print_application (bound : string list) (application : L.application) : string =
  let name : string = print_reference bound application.target in
  let name : string =
    match application.type_arguments with
    | [] -> name
    | _ ->
        "@" ^ name
        ^ (match application.target with
           | L.Global relation ->
               (if StringSet.mem relation !extern_relation_names then
                  " (inferInstance : _root_.SpecTecExternTypes)" else "")
               ^ (if StringSet.mem relation !model_relation_names then
                    " (inferInstance : _root_.SpecTec.SpecTecP4ExternModel)" else "")
           | _ -> "")
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

let notation_priority (remaining : L.notation_part list) : string =
  match remaining with
  | L.Hole :: _
  | L.Literal "(" :: _
  | L.Literal "@" :: _
  | L.Literal "." :: _ ->
      "arg"
  | _ -> "51"

let print_simple_notation (printed_name : string)
    (parts : L.notation_part list) : string =
  let rec print_parts (index : int) (pattern : string list)
      (arguments : string list) (remaining : L.notation_part list) :
      string list * string list =
    match remaining with
    | [] -> (pattern, arguments)
    | L.Hole :: rest ->
        let argument : string = "x" ^ string_of_int index in
        print_parts (index + 1)
          (pattern @ [ argument ^ ":" ^ notation_priority rest ])
          (arguments @ [ argument ]) rest
    | L.Literal literal :: rest ->
        print_parts index
          (pattern @ [ quote_notation_literal (" " ^ literal ^ " ") ])
          arguments rest
  in
  let (pattern, arguments) : string list * string list =
    print_parts 0 [] [] parts
  in
  Printf.sprintf "scoped notation:50 %s => %s"
    (String.concat " " pattern)
    (String.concat " " (("_root_.SpecTec." ^ printed_name) :: arguments))

let print_syntax_notation (printed_name : string)
    (parts : L.notation_part list) : string =
  let rec print_parts (hole_index : int) (child_index : int)
      (pattern : string list) (macro_arguments : string list)
      (unexpander_arguments : string list) (remaining : L.notation_part list) :
      string list * string list * string list * int =
    match remaining with
    | [] -> (pattern, macro_arguments, unexpander_arguments, hole_index)
    | L.Hole :: rest ->
        let argument : string = "x" ^ string_of_int hole_index in
        let pattern_part : string list =
          match rest with
          | L.Hole :: _ -> [ "term:arg"; "ppSpace"; "colGt" ]
          | _ -> [ "term:" ^ notation_priority rest ]
        in
        print_parts (hole_index + 1) (child_index + 1)
          (pattern @ pattern_part)
          (macro_arguments @ [ Printf.sprintf "⟨stx[%d]⟩" child_index ])
          (unexpander_arguments @ [ argument ]) rest
    | L.Literal literal :: rest ->
        print_parts hole_index (child_index + 1)
          (pattern @ [ quote_notation_literal (" " ^ literal ^ " ") ])
          macro_arguments
          (unexpander_arguments
          @ [ "Lean.mkAtom " ^ quote_notation_literal literal ])
          rest
  in
  let pattern, macro_arguments, unexpander_arguments, arity =
    print_parts 0 0 [] [] [] parts
  in
  let unexpander_pattern : string =
    String.concat " "
      ("$f" :: List.init arity (fun index -> "$x" ^ string_of_int index))
  in
  let syntax_name : string =
    "SpecTec.Notation." ^ printed_name ^ ".relationNotation"
  in
  String.concat "\n"
    [ "meta def expandRelationNotation : Lean.Macro := fun stx => do";
      "  let arguments : Array (Lean.TSyntax `term) :=";
      "    #[" ^ String.concat ", " macro_arguments ^ "]";
      Printf.sprintf "  return (Lean.Syntax.mkCApp ``_root_.SpecTec.%s arguments).raw"
        printed_name;
      "";
      "def unexpandRelationNotation : Lean.PrettyPrinter.Unexpander";
      "  | `(" ^ unexpander_pattern ^ ") =>";
      Printf.sprintf "      pure (.node .none `%s" syntax_name;
      "        #[" ^ String.concat ", " unexpander_arguments ^ "])";
      "  | _ => throw ()";
      "";
      "scoped syntax:50 (name := relationNotation)";
      "  " ^ String.concat " " pattern ^ " : term";
      Printf.sprintf "attribute [scoped macro %s] expandRelationNotation"
        syntax_name;
      Printf.sprintf
        "attribute [scoped app_unexpander _root_.SpecTec.%s] unexpandRelationNotation"
        printed_name ]

let rec has_adjacent_holes (parts : L.notation_part list) : bool =
  match parts with
  | L.Hole :: L.Hole :: _ -> true
  | _ :: rest -> has_adjacent_holes rest
  | [] -> false

let print_notation (name : string) (parts : L.notation_part list) : string =
  let printed_name : string = print_identifier name in
  let declaration : string =
    if has_adjacent_holes parts then print_syntax_notation printed_name parts
    else print_simple_notation printed_name parts
  in
  String.concat "\n"
    [ "namespace Notation." ^ printed_name;
      declaration;
      "end Notation." ^ printed_name ]

let print_type_parameters (parameters : string list) : string =
  match parameters with
  | [] -> ""
  | _ -> " (" ^ String.concat " " (List.map print_identifier parameters) ^ " : Type)"

let print_selector_pattern (pattern : L.selector_pattern) : string =
  match pattern with
  | Wildcard -> "_"
  | ConstructorPattern (reference, arity) ->
      print_constructor_ref [] reference
      ^ String.concat "" (List.init arity (fun _ -> " _"))

let print_selector (selector : L.selector) : string =
  let result : string = print_type [] (L.BuiltinType ("Nat", [])) in
  if selector.parameters = [] then
    match selector.arms with
    | [ ([], row) ] ->
        Printf.sprintf "def %s : %s := %d"
          (print_identifier selector.name) result row
    | _ -> invalid_arg "parameterless selector must have exactly one empty arm"
  else
    let binders : string =
      selector.parameters
      |> List.mapi (fun index typ ->
             Printf.sprintf " (arg%d : %s)" index (print_type [] typ))
      |> String.concat ""
    in
    let arguments : string =
      selector.parameters
      |> List.mapi (fun index _ -> "arg" ^ string_of_int index)
      |> String.concat ", "
    in
    let arms : string list =
      List.map
        (fun (patterns, row) ->
          "  | " ^ String.concat ", " (List.map print_selector_pattern patterns)
          ^ " => " ^ string_of_int row)
        selector.arms
    in
    String.concat "\n"
      (Printf.sprintf "def %s%s : %s :="
         (print_identifier selector.name) binders result
       :: ("  match " ^ arguments ^ " with") :: arms)

let print_declaration ?(derive_decidable_eq = false)
    (declaration : L.declaration) : string =
  let deriving (printed : string) : string =
    if derive_decidable_eq then printed ^ "\nderiving _root_.DecidableEq"
    else printed
  in
  match declaration with
  | ExternType name ->
      Printf.sprintf "abbrev %s : Type := _root_.SpecTecExternTypes.%s"
        (print_identifier name) (print_identifier name)
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
        argument_types; rules; notation = _; _ } ->
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
  | Selector selector -> print_selector selector
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

let rec relations_in_group (group : L.declaration_group) : L.declaration list =
  match group with
  | Single (Relation _ as relation) -> [ relation ]
  | Mutual declarations ->
      List.filter (function L.Relation _ -> true | _ -> false) declarations
  | DerivingDecidableEq group -> relations_in_group group
  | Single _ | ManualDecidableEq _ | ManualPrinter _ -> []

let relation_name (declaration : L.declaration) : string =
  match declaration with
  | Relation { name; _ } -> name
  | _ -> invalid_arg "expected relation"

(* Generated ':' relations are definitional helpers.  Only an ordered-rule
   boundary needs a separate evaluator to enforce source selection; supply
   relations already encode their failure chain in the public WFS judgment. *)
let emits_ordered_evaluator (name : string) : bool =
  not (String.contains name ':')
  || String.ends_with ~suffix:":regular" name

let print_call_tuple (bound : string list) (arguments : L.term list) : string =
  match arguments with
  | [] -> "()"
  | [ argument ] -> print_term bound argument
  | _ ->
      let rec nest = function
        | [] -> assert false
        | [ last ] -> print_term bound last
        | first :: rest ->
            "(" ^ print_term bound first ^ ", " ^ nest rest ^ ")"
      in
      nest arguments

let explicit_atom ?(atom_name = "Atom") (name : string) : string =
  "@" ^ atom_name ^ "." ^ name
  ^ (if !atom_has_extern_types then
       " (inferInstance : _root_.SpecTecExternTypes)"
     else "")

let print_atom ?(atom_name = "Atom") (relations : L.declaration list) (bound : string list)
    (application : L.application) : string =
  match application.target with
  | Local name ->
      let reversed = List.rev application.arguments in
      (match reversed with
      | result :: reversed_inputs ->
          "(" ^ explicit_atom ~atom_name "relation_call" ^ " _ _ " ^ print_identifier name ^ " "
          ^ print_call_tuple bound (List.rev reversed_inputs) ^ " "
          ^ print_term bound result ^ ")"
      | [] -> invalid_arg ("relation call has no result: " ^ name))
  | Global _ ->
  let (name, type_parameters, equality_parameters, print_parameters) =
    match application.target with
    | Global name ->
        let parameters : string list * string list * string list =
          match List.find_opt (fun declaration -> relation_name declaration = name) relations with
          | Some (Relation relation) ->
              (relation.type_parameters, relation.equality_parameters,
               relation.print_parameters)
          | _ -> invalid_arg ("unknown relation atom " ^ name)
        in
        let types, equality, printers = parameters in
        atom_name ^ "." ^ print_identifier name, types, equality, printers
    | Local _ -> assert false
  in
  let find_type (parameter : string) : string =
    let rec search parameters arguments =
      match parameters, arguments with
      | name :: rest, typ :: remaining ->
          if name = parameter then print_type bound typ
          else search rest remaining
      | _ -> "_"
    in
    search type_parameters application.type_arguments
  in
  let explicit_printers : string list =
    if List.length application.print_instance_arguments = List.length print_parameters
    then List.map (print_instance bound) application.print_instance_arguments
    else []
  in
  let class_instances : string list =
    List.map
      (fun parameter ->
        "(inferInstance : _root_.DecidableEq " ^ find_type parameter ^ ")")
      equality_parameters
    @ List.mapi
        (fun index parameter ->
          match List.nth_opt explicit_printers index with
          | Some printed -> printed
          | None ->
              "(inferInstance : _root_.SpecTecPrint " ^ find_type parameter ^ ")")
        print_parameters
  in
  let arguments : string list =
    List.mapi
      (fun index _ ->
        match List.nth_opt application.type_arguments index with
        | Some typ -> print_type bound typ
        | None -> "_")
      type_parameters
    @ class_instances
    @ List.map (print_term bound) application.arguments
  in
  let constructor =
    if !atom_has_extern_types then
      "@" ^ name ^ " (inferInstance : _root_.SpecTecExternTypes)"
    else "@" ^ name
  in
  "(" ^ String.concat " " (constructor :: arguments) ^ ")"

let print_atom_list ?(atom_name = "Atom") (relations : L.declaration list) (bound : string list)
    (applications : L.application list) : string =
  "[" ^ String.concat ", "
    (List.map (print_atom ~atom_name relations bound) applications) ^ "]"

let program_rule_name (index : int) : string = "rule_" ^ string_of_int index

let rule_parts (rule : L.rule) :
    L.application list * L.application list * L.prop list =
  List.fold_left
    (fun (positive, negative, side) premise ->
      match premise with
      | L.Holds application ->
          positive @ [ application ], negative, side
      | L.NotHolds (application, _) ->
          positive, negative @ [ application ], side
      | L.NotExists _ ->
          invalid_arg "unlowered existential negative premise"
      | L.Prop proposition -> positive, negative, side @ [ proposition ])
    ([], [], []) rule.premises

let rec print_side (bound : string list) (conditions : L.prop list) : string =
  match conditions with
  | [] -> "_root_.True"
  | condition :: rest ->
      "(" ^ print_prop bound condition ^ " ∧ " ^ print_side bound rest ^ ")"

let print_wfs_rule ?(atom_name = "Atom") (relations : L.declaration list) (bound : string list)
    (rule : L.rule) : string =
  let positive, negative, side = rule_parts rule in
  "{ head := " ^ print_atom ~atom_name relations bound rule.conclusion
  ^ ", positive := " ^ print_atom_list ~atom_name relations bound positive
  ^ ", negative := " ^ print_atom_list ~atom_name relations bound negative
  ^ ", side := " ^ print_side bound side ^ " }"

let print_wfs_parameters (type_parameters : string list)
    (equality_parameters : string list) (print_parameters : string list) : string =
  String.concat ""
    (List.map (fun name -> " {" ^ print_identifier name ^ " : Type}") type_parameters
    @ List.map
        (fun name -> " [_root_.DecidableEq " ^ print_identifier name ^ "]")
        equality_parameters
    @ List.map
        (fun name -> " [_root_.SpecTecPrint " ^ print_identifier name ^ "]")
        print_parameters)

let print_wfs_binders (bound : string list) (binders : (string * L.type_ref) list) : string =
  String.concat ""
    (List.map
       (fun (name, typ) ->
         " (" ^ print_identifier name ^ " : " ^ print_type bound typ ^ ")")
       binders)

let print_atom_constructor ?(result = "Atom") (declaration : L.declaration) : string =
  match declaration with
  | Relation { name; type_parameters; equality_parameters; print_parameters;
               argument_types; _ } ->
      let parameters : string =
        String.concat ""
          (List.map
             (fun parameter -> " {" ^ print_identifier parameter ^ " : Type}")
             type_parameters)
        ^ String.concat ""
            (List.map
               (fun parameter ->
                 " [_root_.DecidableEq " ^ print_identifier parameter ^ "]")
               equality_parameters)
        ^ String.concat ""
            (List.map
               (fun parameter ->
                 " [_root_.SpecTecPrint " ^ print_identifier parameter ^ "]")
               print_parameters)
      in
      let signature : string =
        String.concat " → "
          (List.map (print_type type_parameters) argument_types @ [ result ])
      in
      "  | " ^ print_identifier name ^ parameters ^ " : " ^ signature
  | _ -> invalid_arg "expected relation"

(* Lean builds expensive auxiliary declarations for wide inductives. Keep
   polymorphic constructors real constructors: match_pattern abbreviations make
   implicit fields inaccessible in patterns (notably DecidableEq instances).
   Pack the remaining constructors in a bounded-width tree. The root necessarily
   retains all polymorphic constructors to preserve that pattern API. *)
let print_atoms (relations : L.declaration list) : string =
  let root_width = 128 in
  let width = 32 in
  let call = "  | relation_call {α β : Type} : _root_.SpecTecRelationRef α β → α → β → Atom" in
  let flat () =
    "inductive Atom : Type 1 where\n"
    ^ String.concat "\n" (List.map print_atom_constructor relations @ [call])
  in
  if List.length relations + 1 <= root_width then flat () else
  let polymorphic, monomorphic = List.partition
    (function L.Relation { type_parameters; _ } -> type_parameters <> []
      | _ -> invalid_arg "expected relation") relations in
  if monomorphic = [] then flat () else
  let rec take n acc rest = match n, rest with
    | 0, _ | _, [] -> List.rev acc, rest
    | _, x :: xs -> take (n - 1) (x :: acc) xs
  in
  let rec chunks = function
    | [] -> []
    | xs -> let first, rest = take width [] xs in first :: chunks rest
  in
  let group_name level index =
    print_identifier ("Atom:" ^ string_of_int level ^ ":" ^ string_of_int index)
  in
  let wrap_name index = print_identifier ("group:" ^ string_of_int index) in
  let parameters = if !atom_has_extern_types then " [SpecTecExternTypes]" else "" in
  let extern_argument = if !atom_has_extern_types then
      " (inferInstance : _root_.SpecTecExternTypes)" else "" in
  let declare name constructors =
    "inductive " ^ name ^ parameters ^ " : Type 1 where\n"
    ^ String.concat "\n" constructors
  in
  let arguments = function
    | L.Relation { argument_types; _ } ->
        List.mapi (fun i _ -> "atomArg" ^ string_of_int i) argument_types
    | _ -> invalid_arg "expected relation"
  in
  let leaves = List.mapi (fun i members ->
    let name = group_name 0 i in
    let aliases = List.map (fun relation ->
      relation, String.concat " "
        (("@" ^ name ^ "." ^ print_identifier (relation_name relation)
          ^ extern_argument) :: arguments relation)) members in
    declare name (List.map (print_atom_constructor ~result:name) members),
    (name, aliases)) (chunks monomorphic) in
  let wrap parent children =
    List.mapi (fun i (name, aliases) ->
      let ctor = wrap_name i in
      "  | " ^ ctor ^ " : " ^ name ^ " → " ^ parent,
      List.map (fun (relation, payload) ->
        relation, parent ^ "." ^ ctor ^ " (" ^ payload ^ ")") aliases) children
    |> List.split
  in
  let capacity = max 1 (root_width - List.length polymorphic - 1) in
  let rec pack level nodes =
    if List.length nodes <= capacity then [], nodes else
    let groups = List.mapi (fun i children ->
      let name = group_name level i in
      let constructors, aliases = wrap name children in
      declare name constructors, (name, List.concat aliases)) (chunks nodes) in
    let definitions, roots = pack (level + 1) (List.map snd groups) in
    List.map fst groups @ definitions, roots
  in
  let branches, roots = pack 1 (List.map snd leaves) in
  let constructors, aliases = wrap "Atom" roots in
  let print_alias (relation, payload) = match relation with
    | L.Relation { name; argument_types; _ } ->
        let signature = String.concat " → "
          (List.map (print_type []) argument_types @ ["Atom"]) in
        let body = match arguments relation with
          | [] -> payload
          | args -> "fun " ^ String.concat " " args ^ " => " ^ payload in
        "@[match_pattern] abbrev Atom." ^ print_identifier name ^ " : "
        ^ signature ^ " := " ^ body
    | _ -> invalid_arg "expected relation"
  in
  String.concat "\n\n"
    (List.map fst leaves @ branches
     @ ["inductive Atom : Type 1 where\n"
        ^ String.concat "\n" (List.map print_atom_constructor polymorphic @ [call] @ constructors)]
     @ List.map print_alias (List.concat aliases))

type program_constructor = {
  constructor_name : string;
  constructor_parameters : string;
  constructor_arguments : string;
  constructor_fields : string;
  constructor_head : string;
  rule_index : string;
}

type local_plan_rule = {
  plan_declaration : string;
  plan_constructor : program_constructor;
  allowed_constructor : program_constructor;
  plan_name : string;
  plan_owner : string;
  plan_rule : string;
  witness_pattern : string;
}

let program_constructor name type_parameters equality_parameters print_parameters
    binders head rule_index : program_constructor =
  let bound = type_parameters @ List.map fst binders in
  { constructor_name = name;
    constructor_parameters =
      print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ print_wfs_binders bound binders;
    constructor_arguments = String.concat " "
      (List.map (fun name -> "(" ^ print_identifier name ^ " := "
          ^ print_identifier name ^ ")") type_parameters
       @ List.map (fun (name, _) -> print_identifier name) binders);
    constructor_fields = String.concat " "
      (List.map print_identifier type_parameters
       @ List.map (fun _ -> "_") (equality_parameters @ print_parameters)
       @ List.map (fun (name, _) -> print_identifier name) binders);
    constructor_head = head;
    rule_index }

(* All levels are uniform: cases_in_program peels one wrapper per level,
   then leaves the individual rule cases for the caller's next tactic. *)
let print_program_membership ?(tactic_name = "cases_in_program")
    ?(program_name = "InProgram") ?(index_type = "SpecTecWFS.Rule Atom")
    (constructors : program_constructor list) : string =
  let width = 32 in
  let rec take n acc rest = match n, rest with
    | 0, _ | _, [] -> List.rev acc, rest
    | _, x :: xs -> take (n - 1) (x :: acc) xs in
  let rec chunks = function
    | [] -> []
    | xs -> let first, rest = take width [] xs in first :: chunks rest in
  let group_name level index = print_identifier
    (program_name ^ ":" ^ string_of_int level ^ ":" ^ string_of_int index) in
  let declare name body =
    "inductive " ^ name ^ " : " ^ index_type ^ " → Prop where\n"
    ^ String.concat "\n" body in
  let print_constructor name constructor =
    "  | " ^ constructor.constructor_name ^ constructor.constructor_parameters
    ^ " : " ^ name ^ " " ^ constructor.rule_index in
  let tactic depth =
    "macro \"" ^ tactic_name
    ^ "\" h:Lean.Parser.Tactic.elimTarget : tactic =>\n"
    ^ "  `(tactic| (cases $h"
    ^ String.concat "" (List.init depth (fun _ ->
        " <;> (rename_i programPart; cases programPart)")) ^ "))" in
  if List.length constructors <= width then
    declare program_name (List.map (print_constructor program_name) constructors)
    ^ "\n\n" ^ tactic 0
  else
  let leaves = List.mapi (fun i members ->
    let name = group_name 0 i in
    let aliases = List.map (fun constructor -> constructor,
      name ^ "." ^ constructor.constructor_name
      ^ (if constructor.constructor_arguments = "" then ""
         else " " ^ constructor.constructor_arguments)) members in
    declare name (List.map (print_constructor name) members), (name, aliases))
    (chunks constructors) in
  let wrap parent children =
    List.mapi (fun i (name, aliases) ->
      let ctor = print_identifier ("group:" ^ string_of_int i) in
      "  | " ^ ctor ^ " {rule : " ^ index_type ^ "} : "
      ^ name ^ " rule → " ^ parent ^ " rule",
      List.map (fun (constructor, payload) ->
        constructor, parent ^ "." ^ ctor ^ " (" ^ payload ^ ")") aliases) children
    |> List.split in
  let rec pack level nodes =
    if List.length nodes <= width then [], nodes, level else
    let groups = List.mapi (fun i children ->
      let name = group_name level i in
      let body, aliases = wrap name children in
      declare name body, (name, List.concat aliases)) (chunks nodes) in
    let definitions, roots, depth = pack (level + 1) (List.map snd groups) in
    List.map fst groups @ definitions, roots, depth in
  let branches, roots, depth = pack 1 (List.map snd leaves) in
  let body, aliases = wrap program_name roots in
  String.concat "\n\n"
    (List.map fst leaves @ branches @ [declare program_name body]
     @ List.map (fun (constructor, payload) ->
       "abbrev " ^ program_name ^ "." ^ constructor.constructor_name
       ^ constructor.constructor_parameters ^ " := " ^ payload) (List.concat aliases)
     @ [tactic depth])

let print_dispatch_constructor (relations : L.declaration list) (index : int)
    (declaration : L.declaration) : program_constructor =
  match declaration with
  | Relation { name; type_parameters; equality_parameters; print_parameters;
               argument_types; _ } ->
      let arguments : L.term list =
        List.mapi
          (fun i typ -> L.Variable ("arg" ^ string_of_int i, typ))
          argument_types
      in
      let application : L.application =
        { target = L.Global name;
          type_arguments = List.map (fun n -> L.TypeParameter n) type_parameters;
          instance_arguments = []; print_instance_arguments = []; arguments }
      in
      let reversed = List.rev arguments in
      (match reversed with
      | result :: reversed_inputs ->
          let inputs = List.rev reversed_inputs in
          let binders = List.mapi (fun i typ -> "arg" ^ string_of_int i, typ)
            argument_types in
          program_constructor (program_rule_name index)
            type_parameters equality_parameters print_parameters binders
            ("(" ^ explicit_atom "relation_call" ^ " _ _ "
             ^ "(_root_.SpecTecRelationRef.named \"" ^ escape_string name ^ "\") "
             ^ print_call_tuple type_parameters inputs ^ " "
             ^ print_term type_parameters result ^ ")")
            ("{ head := (" ^ explicit_atom "relation_call" ^ " _ _ "
             ^ "(_root_.SpecTecRelationRef.named \"" ^ escape_string name ^ "\") "
             ^ print_call_tuple type_parameters inputs ^ " "
             ^ print_term type_parameters result ^ "), positive := ["
             ^ print_atom relations type_parameters application
             ^ "], negative := [], side := _root_.True }")
      | [] -> invalid_arg ("relation has no output: " ^ name))
  | _ -> invalid_arg "expected relation"

let print_dispatch_theorem ~(scope : string list) (_relations : L.declaration list) (index : int)
    (declaration : L.declaration) : string =
  match declaration with
  | Relation { name; type_parameters; equality_parameters; print_parameters;
               argument_types; _ } ->
      let bound = scope @ type_parameters in
      let arguments : L.term list =
        List.mapi (fun i typ -> L.Variable ("arg" ^ string_of_int i, typ))
          argument_types
      in
      let application : L.application =
        { target = L.Global name;
          type_arguments = List.map (fun n -> L.TypeParameter n) type_parameters;
          instance_arguments = []; print_instance_arguments = []; arguments }
      in
      let result, reversed_inputs =
        match List.rev arguments with
        | result :: reversed_inputs -> result, reversed_inputs
        | [] -> invalid_arg ("relation has no output: " ^ name)
      in
      let binders =
        List.mapi (fun i typ -> " (arg" ^ string_of_int i ^ " : "
          ^ print_type bound typ ^ ")") argument_types
        |> String.concat ""
      in
      let call =
        "(" ^ explicit_atom "relation_call" ^ " _ _ (_root_.SpecTecRelationRef.named \""
        ^ escape_string name ^ "\") "
        ^ print_call_tuple bound (List.rev reversed_inputs)
        ^ " " ^ print_term bound result ^ ")"
      in
      "theorem " ^ print_identifier name ^ ".dispatch"
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ binders ^ " (proof : SpecTecWFS.Holds InProgram "
      ^ print_atom _relations bound application
      ^ ") : SpecTecWFS.Holds InProgram " ^ call ^ " := by\n"
      ^ "  exact SpecTecWFS.Holds.rule _ (InProgram."
      ^ program_rule_name index ^ " "
      ^ String.concat " "
          (List.mapi (fun i _ -> "arg" ^ string_of_int i) argument_types)
      ^ ") trivial ⟨proof, trivial⟩ trivial"
  | _ -> invalid_arg "expected relation"

let print_in_program_constructor (relations : L.declaration list) (index : int)
    (declaration : L.declaration) (rule : L.rule) : program_constructor =
  match declaration with
  | Relation { type_parameters; equality_parameters; print_parameters; _ } ->
      let bound : string list = type_parameters @ List.map fst rule.binders in
      program_constructor (program_rule_name index)
        type_parameters equality_parameters print_parameters rule.binders
        (print_atom relations bound rule.conclusion)
        (print_wfs_rule relations bound rule)
  | _ -> invalid_arg "expected relation"

let print_wfs_premise (relations : L.declaration list) (bound : string list)
    (premise : L.premise) : string =
  match premise with
  | L.Holds ({ target = Local _; _ } as application) ->
      "SpecTecWFS.Holds InProgram " ^ print_atom relations bound application
  | L.NotHolds (application, _) ->
      "SpecTecWFS.Fails InProgram " ^ print_atom relations bound application
  | _ -> print_premise bound premise

let rec all_proof (names : string list) : string =
  match names with
  | [] -> "trivial"
  | name :: rest -> "⟨" ^ name ^ ", " ^ all_proof rest ^ "⟩"

let print_wfs_rule_theorem ~(scope : string list) (relations : L.declaration list) (index : int)
    (declaration : L.declaration) (rule : L.rule) : string =
  match declaration with
  | Relation { name; type_parameters; equality_parameters; print_parameters; _ } ->
      let bound : string list = scope @ type_parameters @ List.map fst rule.binders in
      let assumptions : string list =
        List.mapi
          (fun index premise ->
            " (h" ^ string_of_int index ^ " : "
            ^ print_wfs_premise relations bound premise ^ ")")
          rule.premises
      in
      let numbered : (int * L.premise) list = List.mapi (fun i p -> i, p) rule.premises in
      let positive : string list =
        List.filter_map
          (function i, L.Holds _ -> Some ("h" ^ string_of_int i) | _ -> None)
          numbered
      in
      let negative : string list =
        List.filter_map
          (function i, L.NotHolds _ -> Some ("h" ^ string_of_int i) | _ -> None)
          numbered
      in
      let side : string list =
        List.filter_map
          (function
            | i, L.Prop _ -> Some ("h" ^ string_of_int i)
            | _ -> None)
          numbered
      in
      let binder_arguments : string =
        String.concat "" (List.map (fun (name, _) -> " " ^ print_identifier name) rule.binders)
      in
      "theorem " ^ print_identifier name ^ "." ^ print_identifier rule.name
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ print_wfs_binders bound rule.binders
      ^ String.concat "" assumptions
      ^ " : " ^ print_application bound rule.conclusion ^ " :=\n"
      (* The constructor's index already contains the complete rule. Let Lean
         infer it instead of printing that large record a second time. *)
      ^ "  SpecTecWFS.Holds.rule _ (InProgram." ^ program_rule_name index ^ binder_arguments ^ ")\n"
      ^ "    (" ^ all_proof side ^ ") (" ^ all_proof positive ^ ") (" ^ all_proof negative ^ ")"
  | _ -> invalid_arg "expected relation"

let print_wfs_relation (relations : L.declaration list)
    (declaration : L.declaration) : string =
  match declaration with
  | Relation { name; type_parameters; equality_parameters; print_parameters;
               argument_types; _ } ->
      let parameters : string =
        String.concat ""
          (List.mapi
             (fun index typ ->
               " (arg" ^ string_of_int index ^ " : " ^ print_type type_parameters typ ^ ")")
             argument_types)
      in
      let application : L.application =
        { target = L.Global name;
          type_arguments = List.map (fun name -> L.TypeParameter name) type_parameters;
          instance_arguments = []; print_instance_arguments = [];
          arguments = List.mapi
            (fun index typ -> L.Variable ("arg" ^ string_of_int index, typ))
            argument_types }
      in
      "def " ^ print_identifier name
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ parameters ^ " : Prop :=\n  SpecTecWFS.Holds InProgram "
      ^ print_atom relations type_parameters application
  | _ -> invalid_arg "expected relation"

let print_wfs_program (relations : L.declaration list) : string =
  let rules : (int * L.declaration * L.rule) list =
    relations
    |> List.concat_map (function
         | L.Relation ({ rules; _ } as relation) ->
             List.map (fun rule -> L.Relation relation, rule) rules
         | _ -> [])
    |> List.mapi (fun index (relation, rule) -> index, relation, rule)
  in
  let rec referenced_name (target : string) (term : L.term) : bool =
    match term with
    | FunctionReference { target = Global name; _ } when name = target -> true
    | _ -> List.exists (referenced_name target) (Traversal.term_children term)
  in
  let referenced_as_value (name : string) : bool =
    List.exists
      (function
        | L.Relation relation ->
            List.exists
              (fun (rule : L.rule) ->
                List.exists (referenced_name name)
                  (rule.conclusion.arguments
                   @ List.concat_map Traversal.premise_terms rule.premises))
              relation.rules
        | _ -> false)
      relations
  in
  let named_relations : L.declaration list =
    List.filter
      (fun declaration ->
        let name = relation_name declaration in
        String.length name > 0 && name.[0] = '$'
        && not (String.contains name ':')
        && referenced_as_value name)
      relations
  in
  let dispatch : (int * L.declaration) list =
    List.mapi (fun i declaration -> List.length rules + i, declaration)
      named_relations
  in
  String.concat "\n\n"
    ([ print_atoms relations;
       print_program_membership
         (List.map (fun (index, relation, rule) ->
              print_in_program_constructor relations index relation rule) rules
          @ List.map (fun (index, declaration) ->
              print_dispatch_constructor relations index declaration) dispatch
          @ [{ constructor_name = "external_call";
               constructor_parameters = " {α β : Type} (f : α → β → Prop) (input : α) (output : β)";
               constructor_arguments = "(α := α) (β := β) f input output";
               constructor_fields = "α β f input output";
               constructor_head = "(" ^ explicit_atom "relation_call" ^ " α β (_root_.SpecTecRelationRef.external f) input output)";
               rule_index = "{ head := (" ^ explicit_atom "relation_call" ^ " α β (_root_.SpecTecRelationRef.external f) input output), positive := [], negative := [], side := f input output }" }]) ]
    @ List.map (print_wfs_relation relations) relations
    @ List.concat_map
        (fun relation ->
          let name : string = relation_name relation in
          let scope = "dispatch" :: (match relation with
            | L.Relation { rules; _ } -> List.map (fun (rule : L.rule) -> rule.name) rules
            | _ -> []) in
          let theorems : string list =
            List.filter_map
              (fun (index, owner, rule) ->
                if relation_name owner = name then
                  Some (print_wfs_rule_theorem ~scope relations index owner rule)
                else None)
              rules
          in
          let theorems : string list =
            theorems @
            List.filter_map
              (fun (index, owner) ->
                if relation_name owner = name then
                  Some (print_dispatch_theorem ~scope relations index owner)
                else None)
              dispatch
          in
          (* Qualified declarations preserve the public names without two
             namespace commands and their snapshots for every relation. *)
          theorems @ declaration_notation relation)
        relations)

(* The default backend keeps WFS atoms and membership evidence inside one
   dependency component.  Public relation constants below are the only bridge
   between components; the legacy printer above remains available for the two
   explicit counter modes. *)
let component_namespace (component : Relation_graph.component) : string =
  match component.relations with
  | first :: _ -> print_identifier (first ^ ":Semantics")
  | [] -> invalid_arg "empty relation component"

let relation_table (relations : L.declaration list) : L.declaration StringMap.t =
  List.map (fun relation -> relation_name relation, relation) relations
  |> List.to_seq |> StringMap.of_seq

let application_target_name (application : L.application) : string option =
  match application.target with L.Global name -> Some name | L.Local _ -> None

let print_application_suffix (bound : string list) (suffix : string)
    (application : L.application) : string =
  let original, name = match application.target with
    | L.Global name -> name, print_global_name bound name ^ suffix
    | L.Local name -> name, print_identifier name ^ suffix
  in
  let name = match application.type_arguments with
    | [] -> name
    | _ ->
        "@" ^ name
        ^ (if StringSet.mem original !extern_relation_names then
                " (inferInstance : _root_.SpecTecExternTypes)" else "")
        ^ (if StringSet.mem original !model_relation_names then
                  " (inferInstance : _root_.SpecTec.SpecTecP4ExternModel)" else "")
  in
  let arguments =
    List.map (print_type bound) application.type_arguments
    @ List.map (fun _ -> "_") application.instance_arguments
    @ List.map (print_instance bound) application.print_instance_arguments
    @ List.map (print_term bound) application.arguments
  in
  match arguments with [] -> name | _ -> "(" ^ String.concat " " (name :: arguments) ^ ")"

let print_public_failure (bound : string list) (application : L.application) : string =
  print_application_suffix bound ".fails" application

let print_local_membership ~(component_index : int)
    (constructors : program_constructor list) : string =
  if List.length constructors > 32 then
    print_program_membership
      ~tactic_name:("cases_in_program_" ^ string_of_int component_index)
      constructors
  else
    "inductive InProgram : SpecTecWFS.Rule Atom → Prop where\n"
    ^ String.concat "\n" (List.map (fun constructor ->
        "  | " ^ constructor.constructor_name ^ constructor.constructor_parameters
        ^ " : InProgram " ^ constructor.rule_index) constructors)

let print_local_side_premise (bound : string list) (premise : L.premise) : string =
  match premise with
  | L.NotHolds (application, _) -> print_public_failure bound application
  | L.NotExists (binders, application, _) ->
      let inner_bound = bound @ List.map fst binders in
      List.fold_right (fun (name, typ) body ->
        "∀ (" ^ print_identifier name ^ " : " ^ print_type inner_bound typ ^ "), " ^ body)
        binders (print_public_failure inner_bound application)
  | L.Holds application -> print_application bound application
  | L.Prop proposition -> print_prop bound proposition

let print_local_public_relation (qualified : string) (recursive : bool)
    (relations : L.declaration list) (declaration : L.declaration) : string =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; _ } ->
      let parameters = String.concat ""
        (List.mapi (fun index typ ->
           " (arg" ^ string_of_int index ^ " : "
           ^ print_type type_parameters typ ^ ")") argument_types) in
      let application = {
        L.target = L.Global name;
        type_arguments = List.map (fun parameter -> L.TypeParameter parameter) type_parameters;
        instance_arguments = []; print_instance_arguments = [];
        arguments = List.mapi (fun index typ ->
          L.Variable ("arg" ^ string_of_int index, typ)) argument_types;
      } in
      let atom = print_atom ~atom_name:(qualified ^ ".Atom") relations
        type_parameters application in
      let prefix suffix = "def " ^ print_identifier name ^ suffix
        ^ print_wfs_parameters type_parameters equality_parameters print_parameters
        ^ parameters in
      let public_application = { application with
        instance_arguments = List.map (fun parameter ->
          L.TypeParameter parameter) equality_parameters;
        print_instance_arguments = List.map (fun parameter ->
          L.TypeParameter parameter) print_parameters } in
      let certificate = "theorem " ^ print_identifier name
        ^ ".checkedSuccess"
        ^ print_wfs_parameters type_parameters equality_parameters print_parameters
        ^ parameters
        ^ " (same : " ^ qualified ^ ".Atom → " ^ qualified ^ ".Atom → Bool)"
        ^ " (sameSound : ∀ left right, same left right = true → left = right)"
        ^ " (fuel : Nat)"
        ^ " (certificate : SpecTecPlan.SuccessCertificate " ^ qualified
        ^ ".InProgram)"
        ^ " (accepted : SpecTecPlan.checkSuccessWith same fuel certificate = some "
        ^ atom ^ ") : " ^ print_application type_parameters public_application
        ^ " := by\n  exact SpecTecPlan.checkSuccessWith_sound same sameSound"
        ^ " fuel certificate _ accepted" in
      String.concat "\n\n"
        ([ prefix "" ^ " : Prop :=\n  SpecTecWFS.Holds " ^ qualified ^ ".InProgram " ^ atom;
           prefix ".fails" ^ " : Prop :=\n  SpecTecWFS.Fails " ^ qualified ^ ".InProgram " ^ atom ]
         @ (if recursive then
             [ prefix ".undetermined" ^ " : Prop :=\n  SpecTecWFS.Undetermined "
               ^ qualified ^ ".InProgram " ^ atom ]
           else [])
         @ [certificate])
  | _ -> invalid_arg "expected relation"

let print_local_rule_premise (qualified : string) (relations : L.declaration list)
    (members : StringSet.t) (bound : string list) (premise : L.premise) : string =
  let internal application = match application.L.target with
    | L.Local _ -> true
    | L.Global name -> StringSet.mem name members
  in
  match premise with
  | L.Holds application when internal application ->
      "SpecTecWFS.Holds " ^ qualified ^ ".InProgram "
      ^ print_atom ~atom_name:(qualified ^ ".Atom") relations bound application
  | L.NotHolds (application, _) when internal application ->
      "SpecTecWFS.Fails " ^ qualified ^ ".InProgram "
      ^ print_atom ~atom_name:(qualified ^ ".Atom") relations bound application
  | _ -> print_local_side_premise bound premise

let local_membership_call qualified type_parameters equality_parameters print_parameters index =
  "@" ^ qualified ^ ".InProgram." ^ program_rule_name index
  ^ (if !program_has_extern_types then " (inferInstance : SpecTecExternTypes)" else "")
  ^ (if !program_has_p4_extern_model then " (inferInstance : SpecTecP4ExternModel)" else "")
  ^ String.concat "" (List.map (fun parameter -> " " ^ print_identifier parameter) type_parameters)
  ^ String.concat "" (List.map (fun _ -> " inferInstance") (equality_parameters @ print_parameters))

let print_local_rule_theorem (qualified : string) (relations : L.declaration list)
    (members : StringSet.t) (index : int) (declaration : L.declaration)
    (rule : L.rule) (plan : local_plan_rule) : string =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 rules; _ } ->
      let scope = List.map relation_name relations in
      let rule_scope = List.map (fun (member : L.rule) -> member.name) rules in
      let bound = scope @ rule_scope @ type_parameters @ List.map fst rule.binders in
      let assumptions = List.mapi (fun premise_index premise ->
        " (h" ^ string_of_int premise_index ^ " : "
        ^ print_local_rule_premise qualified relations members bound premise ^ ")")
        rule.premises in
      let type_arguments = String.concat ""
        (List.map (fun parameter -> " (" ^ print_identifier parameter
          ^ " := " ^ print_identifier parameter ^ ")") type_parameters) in
      "theorem " ^ print_identifier name ^ "." ^ print_identifier rule.name
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ print_wfs_binders bound rule.binders ^ String.concat "" assumptions
      ^ " : " ^ print_application bound rule.conclusion ^ " :=\n"
      ^ "  SpecTecPlan.Plan.holds_rule (program := " ^ qualified ^ ".InProgram) (" ^ qualified ^ "."
      ^ program_rule_name index ^ "_plan" ^ type_arguments ^ ").body () "
      ^ plan.witness_pattern ^ " ("
      ^ local_membership_call qualified type_parameters equality_parameters print_parameters index
      ^ " (" ^ plan.witness_pattern
      ^ " : (" ^ qualified ^ "." ^ program_rule_name index ^ "_plan"
      ^ type_arguments ^ ").body.Witness))\n"
      ^ "    (by dsimp [" ^ qualified ^ "." ^ program_rule_name index
      ^ "_plan, SpecTecPlan.Plan.premises, SpecTecEval.Prefix]; all_goals exact "
      ^ all_proof (List.mapi (fun i _ -> "h" ^ string_of_int i) rule.premises) ^ ")"

  | _ -> invalid_arg "expected relation"

let print_local_rule_cases (qualified : string)
    (_component_index : int)
    (_members : StringSet.t)
    (relations : L.declaration list)
    (_indexed_rules : (int * L.declaration * L.rule) list)
    (declaration : L.declaration) : string =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; rules; _ } ->
      let arg_names = List.mapi (fun i _ -> "arg" ^ string_of_int i)
        argument_types in
      let type_scope = type_parameters @ List.map (fun (rule : L.rule) ->
        rule.name) rules in
      let args = String.concat "" (List.map2 (fun arg typ ->
        " (" ^ arg ^ " : " ^ print_type type_scope typ ^ ")")
        arg_names argument_types) in
      let application = {
        L.target = L.Global name;
        type_arguments = List.map (fun parameter ->
          L.TypeParameter parameter) type_parameters;
        instance_arguments = List.map (fun parameter ->
          L.TypeParameter parameter) equality_parameters;
        print_instance_arguments = List.map (fun parameter ->
          L.TypeParameter parameter) print_parameters;
        arguments = List.map2 (fun arg typ -> L.Variable (arg, typ))
          arg_names argument_types;
      } in
      let target = print_atom ~atom_name:(qualified ^ ".Atom") relations
        type_parameters application in
      "theorem " ^ print_identifier name ^ ".ruleCases"
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ args ^ " (proof : " ^ print_application type_parameters application
      ^ ") : SpecTecPlan.Cases " ^ qualified ^ ".Allowed () " ^ target
      ^ " :=\n  SpecTecPlan.ProgramOf.holds_cases proof"
  | _ -> invalid_arg "expected relation"

let print_local_dispatch_constructor (relations : L.declaration list)
    (members : StringSet.t) (index : int) (declaration : L.declaration) :
    program_constructor =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; _ } ->
      let arguments = List.mapi (fun i typ -> L.Variable ("arg" ^ string_of_int i, typ))
        argument_types in
      let application = { L.target = L.Global name;
        type_arguments = List.map (fun parameter -> L.TypeParameter parameter) type_parameters;
        instance_arguments = []; print_instance_arguments = []; arguments } in
      let result, reversed_inputs = match List.rev arguments with
        | result :: inputs -> result, inputs
        | [] -> invalid_arg ("relation has no output: " ^ name) in
      let inputs = List.rev reversed_inputs in
      let binders = List.mapi (fun i typ -> "arg" ^ string_of_int i, typ) argument_types in
      let head = "(" ^ explicit_atom "relation_call" ^ " _ _ "
        ^ "(_root_.SpecTecRelationRef.named \"" ^ escape_string name ^ "\") "
        ^ print_call_tuple type_parameters inputs ^ " " ^ print_term type_parameters result ^ ")" in
      let body = if StringSet.mem name members then
          "{ head := " ^ head ^ ", positive := ["
          ^ print_atom relations type_parameters application
          ^ "], negative := [], side := _root_.True }"
        else
          "{ head := " ^ head ^ ", positive := [], negative := [], side := "
          ^ print_application type_parameters application ^ " }" in
      program_constructor (program_rule_name index)
        type_parameters equality_parameters print_parameters binders head body
  | _ -> invalid_arg "expected relation"

let print_local_dispatch_theorem (qualified : string) (_members : StringSet.t)
    (index : int) (declaration : L.declaration) : string =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; _ } ->
      let arguments = List.mapi (fun i typ -> L.Variable ("arg" ^ string_of_int i, typ))
        argument_types in
      let result, reversed_inputs = match List.rev arguments with
        | result :: inputs -> result, inputs
        | [] -> invalid_arg ("relation has no output: " ^ name) in
      let binders = List.mapi (fun i typ -> " (arg" ^ string_of_int i ^ " : "
        ^ print_type type_parameters typ ^ ")") argument_types |> String.concat "" in
      let call = "(" ^ explicit_atom ~atom_name:(qualified ^ ".Atom") "relation_call"
        ^ " _ _ (_root_.SpecTecRelationRef.named \"" ^ escape_string name ^ "\") "
        ^ print_call_tuple type_parameters (List.rev reversed_inputs) ^ " "
        ^ print_term type_parameters result ^ ")" in
      let proof = print_application type_parameters { L.target = L.Global name;
        type_arguments = List.map (fun parameter -> L.TypeParameter parameter) type_parameters;
        instance_arguments = []; print_instance_arguments = []; arguments } in
      "theorem " ^ qualified ^ "." ^ print_identifier ("dispatch:" ^ name)
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ binders ^ " (proof : " ^ proof ^ ") : SpecTecWFS.Holds "
      ^ qualified ^ ".InProgram " ^ call ^ " := by\n"
      ^ "  apply SpecTecPlan.Plan.holds_rule (" ^ qualified ^ "."
      ^ program_rule_name index ^ "_plan).body () _ ("
      ^ local_membership_call qualified type_parameters equality_parameters print_parameters index ^ " "
      ^ List.fold_right (fun i rest -> "⟨arg" ^ string_of_int i ^ ", " ^ rest ^ "⟩")
          (List.mapi (fun i _ -> i) argument_types) "()"
      ^ ")\n  exact ⟨proof, trivial⟩"

  | _ -> invalid_arg "expected relation"

let eval_product_type (bound : string list) (types : L.type_ref list) : string =
  match types with
  | [] -> "_root_.Unit"
  | [ typ ] -> print_type bound typ
  | _ -> print_tuple_type bound types

let rec eval_tuple_pattern (names : string list) : string =
  match names with
  | [] -> "()"
  | [ name ] -> print_identifier name
  | name :: rest ->
      "(" ^ print_identifier name ^ ", " ^ eval_tuple_pattern rest ^ ")"

let rec eval_tuple_term (bound : string list) (terms : L.term list) : string =
  match terms with
  | [] -> "()"
  | [ term ] -> print_term bound term
  | term :: rest ->
      "(" ^ print_term bound term ^ ", " ^ eval_tuple_term bound rest ^ ")"

type eval_premise = {
  proposition : string;
  public_evidence : string -> string;
}

let print_eval_application (relations : L.declaration list)
    (members : StringSet.t) (bound : string list) (application : L.application) :
    (string * string) option =
  match application.target with
  | L.Local _ -> None
  | L.Global target when StringSet.mem target members -> None
  | L.Global target when not (emits_ordered_evaluator target) -> None
  | L.Global target ->
      let table = relation_table relations in
      (match StringMap.find_opt target table with
      | Some (L.Relation { argument_types; input_positions; _ }) ->
          let positions = Option.value input_positions
            ~default:(List.init (max 0 (List.length argument_types - 1)) Fun.id) in
          let indexed = List.mapi (fun index term -> index, term)
            application.arguments in
          let inputs, outputs = List.partition
            (fun (index, _) -> List.mem index positions) indexed in
          let original_name = print_global_name bound target in
          let evaluator_name = original_name ^ ".evalSelected" in
          let evaluator_name = match application.type_arguments with
            | [] -> evaluator_name
            | _ ->
                "@" ^ evaluator_name
                ^ (if StringSet.mem target !extern_relation_names then
                        " (inferInstance : _root_.SpecTecExternTypes)" else "")
                ^ (if StringSet.mem target !model_relation_names then
                          " (inferInstance : _root_.SpecTec.SpecTecP4ExternModel)" else "")
          in
          let arguments =
            List.map (print_type bound) application.type_arguments
            @ List.map (fun _ -> "_") application.instance_arguments
            @ List.map (print_instance bound) application.print_instance_arguments
            @ [ eval_tuple_term bound (List.map snd inputs);
                eval_tuple_term bound (List.map snd outputs) ]
          in
          Some ("(" ^ String.concat " " (evaluator_name :: arguments) ^ ")",
            original_name)
      | _ -> None)

let print_eval_premise (qualified : string) (all_relations : L.declaration list)
    (component_relations : L.declaration list) (members : StringSet.t)
    (relation_name : string) (rule_index : int) (premise_index : int)
    (bound : string list) (premise : L.premise) : eval_premise =
  let public = print_local_rule_premise qualified component_relations members
    bound premise in
  match premise with
  | L.Holds ({ target = L.Global "$fresh_typeId"; arguments; _ }) ->
      let output = match List.rev arguments with
        | output :: _ -> print_term bound output
        | [] -> invalid_arg "fresh_typeId call without output" in
      let site = "({ relation := \"" ^ escape_string relation_name
        ^ "\", rule := " ^ string_of_int rule_index ^ ", premise := "
        ^ string_of_int premise_index ^ " } : SpecTecFresh.Site)" in
      { proposition = "SpecTecFresh.AllocatedAt " ^ site ^ " [] " ^ output;
        public_evidence = (fun evidence ->
          "(by apply " ^ print_identifier "$fresh_typeId"
          ^ ".allocated; exact SpecTecFresh.AllocatedAt.toAllocated "
          ^ evidence ^ ")") }
  | L.Holds application ->
      (match print_eval_application all_relations members bound application with
      | None -> { proposition = public; public_evidence = Fun.id }
      | Some (selected, target) ->
          { proposition = selected;
            public_evidence = (fun evidence ->
              "(by simpa only [" ^ target ^ ".evalSucceeds] using ("
              ^ target ^ ".selected_sound " ^ evidence ^ "))") })
  | L.NotHolds _ | L.NotExists _ | L.Prop _ ->
      { proposition = public; public_evidence = Fun.id }

let rule_recoverable (name : string) (rule : L.rule) : int list =
  List.mapi (fun index premise -> index, premise) rule.premises
  |> List.filter_map (fun (index, premise) -> match premise with
       | L.Prop _ | L.NotHolds _ | L.NotExists _ -> Some index
       | L.Holds _ when List.mem index rule.catchable -> Some index
       | L.Holds { target = L.Global target; _ }
         when String.starts_with ~prefix:"regular" rule.name
           && target = name ^ ":regular" -> Some index
       | L.Holds _ -> None)


let print_ordered_evaluator (qualified : string)
    (_component_relations : L.declaration list) (plans : local_plan_rule list)
    (recursive : bool) (declaration : L.declaration) : string =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; input_positions; rules; _ } ->
      let positions = Option.value input_positions
        ~default:(List.init (max 0 (List.length argument_types - 1)) Fun.id) in
      let rule_scope = List.map (fun (rule : L.rule) -> rule.name) rules in
      let type_scope = rule_scope @ type_parameters in
      let indexed = List.mapi (fun index typ -> index, typ) argument_types in
      let inputs, outputs = List.partition
        (fun (index, _) -> List.mem index positions) indexed in
      let input_types = List.map snd inputs and output_types = List.map snd outputs in
      let input_names = List.map (fun (index, _) -> "eval:arg:" ^ string_of_int index) inputs in
      let output_names = List.map (fun (index, _) -> "eval:arg:" ^ string_of_int index) outputs in
      let input_pattern = eval_tuple_pattern input_names in
      let output_pattern = eval_tuple_pattern output_names in
      let all_names = List.init (List.length argument_types)
        (fun index -> "eval:arg:" ^ string_of_int index) in
      let all_terms = List.map2 (fun name typ -> L.Variable (name, typ))
        all_names argument_types in
      let application = { L.target = L.Global name;
        type_arguments = List.map (fun parameter -> L.TypeParameter parameter) type_parameters;
        instance_arguments = List.map
          (fun parameter -> L.TypeParameter parameter) equality_parameters;
        print_instance_arguments = List.map
          (fun parameter -> L.TypeParameter parameter) print_parameters;
        arguments = all_terms } in
      let type_parameters_only = String.concat ""
        (List.map (fun parameter -> " {" ^ print_identifier parameter ^ " : Type}")
           type_parameters) in
      let wfs_parameters = print_wfs_parameters type_parameters equality_parameters
        print_parameters in
      let type_arguments = String.concat ""
        (List.map (fun parameter ->
           " (" ^ print_identifier parameter ^ " := "
           ^ print_identifier parameter ^ ")") type_parameters) in
      let input_type = eval_product_type type_scope input_types in
      let output_type = eval_product_type type_scope output_types in
      let input_alias = "abbrev " ^ print_identifier name ^ ".EvalInput"
        ^ type_parameters_only ^ " : Type := " ^ input_type in
      let output_alias = "abbrev " ^ print_identifier name ^ ".EvalOutput"
        ^ type_parameters_only ^ " : Type := " ^ output_type in
      let input_ref = if type_parameters = [] then print_identifier name ^ ".EvalInput"
        else "(@" ^ print_identifier name ^ ".EvalInput "
          ^ String.concat " " (List.map print_identifier type_parameters) ^ ")" in
      let output_ref = if type_parameters = [] then print_identifier name ^ ".EvalOutput"
        else "(@" ^ print_identifier name ^ ".EvalOutput "
          ^ String.concat " " (List.map print_identifier type_parameters) ^ ")" in
      let succeeds = "def " ^ print_identifier name ^ ".evalSucceeds" ^ wfs_parameters
        ^ " : " ^ input_ref ^ " → " ^ output_ref ^ " → Prop\n"
        ^ "  | " ^ input_pattern ^ ", " ^ output_pattern ^ " => "
        ^ print_application (type_scope @ all_names) application in
      let fresh_sites = rules |> List.mapi (fun rule_index (rule : L.rule) ->
        rule.premises |> List.mapi (fun premise_index premise ->
          Traversal.premise_applications premise
          |> List.filter_map (fun application ->
               match application.L.target with
               | L.Global "$fresh_typeId" ->
                   Some ("{ relation := \"" ^ escape_string name
                     ^ "\", rule := " ^ string_of_int rule_index
                     ^ ", premise := " ^ string_of_int premise_index ^ " }")
               | _ -> None)) |> List.concat) |> List.concat in
      let fresh_sites_declaration =
        "def " ^ print_identifier name ^ ".freshSites : List SpecTecFresh.Site := ["
        ^ String.concat ", " fresh_sites ^ "]" in
      let signature_call = "(" ^ qualified ^ "."
        ^ print_identifier (name ^ ":signature") ^ type_arguments ^ ")" in
      let alternatives = List.map (fun (rule : L.rule) ->
        let plan = List.find (fun plan -> plan.plan_owner = name
          && plan.plan_rule = rule.name) plans in
        "⟨" ^ qualified ^ "." ^ plan.plan_name ^ type_arguments ^ ", "
        ^ qualified ^ ".Allowed." ^ plan.allowed_constructor.constructor_name
        ^ type_arguments ^ "⟩") rules in
      let evaluator = "def " ^ print_identifier name ^ ".evaluator"
        ^ wfs_parameters ^ " : SpecTecEval.Evaluator " ^ input_ref ^ " "
        ^ output_ref ^ " " ^ print_identifier name ^ ".evalSucceeds :=\n  "
        ^ "SpecTecPlan.evaluator " ^ qualified ^ ".Allowed " ^ signature_call
        ^ " [" ^ String.concat ", " alternatives ^ "] _root_.Bool." ^ string_of_bool recursive in
      let evaluator_call = "(" ^ print_identifier name ^ ".evaluator" ^ type_arguments ^ ")" in
      let alias suffix field = "abbrev " ^ print_identifier name ^ suffix
        ^ wfs_parameters ^ " := " ^ evaluator_call ^ "." ^ field in
      let eval_rules = alias ".evalRules" "rules" in
      let undetermined = alias ".evalUndetermined" "undetermined" in
      let all_failed = alias ".allRulesFailed" "AllFailed" in
      let selected = alias ".evalSelected" "Selected" in
      let selected_sound = "theorem " ^ print_identifier name ^ ".selected_sound"
        ^ wfs_parameters ^ " {input : " ^ input_ref ^ "} {output : " ^ output_ref
        ^ "} (proof : " ^ print_identifier name ^ ".evalSelected input output) : "
        ^ print_identifier name ^ ".evalSucceeds input output :=\n  "
        ^ "SpecTecEval.Evaluator.selected_sound (evaluator := " ^ evaluator_call ^ ") proof" in
      let boundary = " [SpecTecEval.Boundary " ^ input_ref
        ^ " _root_.String _root_.String]" in
      let outcome = "(SpecTecEval.Outcome " ^ output_ref
        ^ " _root_.String _root_.String)" in
      let eval = "abbrev " ^ print_identifier name ^ ".eval" ^ wfs_parameters
        ^ boundary ^ " : _root_.Nat → " ^ input_ref ^ " → " ^ outcome
        ^ " → Prop :=\n  " ^ evaluator_call ^ ".Evaluation" in
      String.concat "\n\n"
        [ input_alias; output_alias; succeeds; fresh_sites_declaration;
          evaluator; eval_rules; undetermined; all_failed; selected; selected_sound; eval ]
  | _ -> invalid_arg "expected relation"

let plan_environment_pattern (binders : (string * L.type_ref) list) : string =
  List.fold_left (fun pattern (name, _) ->
    "⟨" ^ pattern ^ ", " ^ print_identifier name ^ "⟩") "()" binders

let plan_witness (terms : string list) : string =
  List.fold_right (fun term rest ->
    "⟨" ^ term ^ ", " ^ rest ^ "⟩") terms "()"

let print_plan_signature (relations : L.declaration list) (declaration : L.declaration) =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; input_positions; selection_policy; _ } ->
      let positions = Option.value input_positions
        ~default:(List.init (max 0 (List.length argument_types - 1)) Fun.id) in
      let indexed = List.mapi (fun i typ -> i, typ) argument_types in
      let inputs, outputs = List.partition (fun (i, _) -> List.mem i positions) indexed in
      let names = List.mapi (fun i _ -> "arg" ^ string_of_int i) argument_types in
      let names_for values = List.map (fun (i, _) -> List.nth names i) values in
      let application = { L.target = L.Global name;
        type_arguments = List.map (fun p -> L.TypeParameter p) type_parameters;
        instance_arguments = []; print_instance_arguments = [];
        arguments = List.map2 (fun n t -> L.Variable (n, t)) names argument_types } in
      "abbrev " ^ print_identifier (name ^ ":signature")
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ " : SpecTecPlan.Signature Atom :=\n  { Input := "
      ^ eval_product_type type_parameters (List.map snd inputs) ^ ", Output := "
      ^ eval_product_type type_parameters (List.map snd outputs)
      ^ ", inputPositions := [" ^ String.concat ", " (List.map string_of_int positions)
      ^ "], policy := " ^ (match selection_policy with
          | L.Ordered -> ".ordered" | L.Nondeterministic -> ".nondeterministic")
      ^ ", atom := fun " ^ eval_tuple_pattern (names_for inputs) ^ " "
      ^ eval_tuple_pattern (names_for outputs) ^ " => "
      ^ print_atom relations (type_parameters @ names) application ^ " }"
  | _ -> invalid_arg "expected relation"

let signature_type_arguments (parameters : string list) =
  String.concat "" (List.map (fun parameter -> " (" ^ print_identifier parameter
    ^ " := " ^ print_identifier parameter ^ ")") parameters)

let print_external_signature (qualified : string) (declaration : L.declaration) =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters; _ } ->
      let arguments = signature_type_arguments type_parameters in
      "abbrev " ^ print_identifier name ^ ".externalSignature"
      ^ print_wfs_parameters type_parameters equality_parameters print_parameters
      ^ " : SpecTecPlan.ExternalSignature :=\n  SpecTecPlan.Signature."
      ^ (if emits_ordered_evaluator name then "evaluated" else "external")
      ^ " (" ^ qualified ^ "." ^ print_identifier (name ^ ":signature") ^ arguments
      ^ ") " ^ qualified ^ ".InProgram"
      ^ (if emits_ordered_evaluator name then " (" ^ print_identifier name
          ^ ".evaluator" ^ arguments ^ ")" else "")
  | _ -> invalid_arg "expected relation"

let print_local_plan_rule (all_relations : L.declaration list)
    (component_relations : L.declaration list) (members : StringSet.t)
    (index : int) (declaration : L.declaration) (rule : L.rule) : local_plan_rule =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 rules; _ } ->
      let plan_name = program_rule_name index ^ "_plan" in
      let table = relation_table all_relations in
      let call_shape (application : L.application) =
        match application.target with
          | L.Global target ->
              (match StringMap.find_opt target table with
              | Some (L.Relation { argument_types; type_parameters = parameters;
                                   input_positions; selection_policy; _ }) ->
                  let bindings = List.filter_map Fun.id
                    (List.mapi (fun i parameter ->
                       Option.map (fun typ -> parameter, typ)
                         (List.nth_opt application.type_arguments i)) parameters) in
                  let types = List.map
                    (Translator.substitute_type_parameters bindings) argument_types in
                  let positions = Option.value input_positions
                    ~default:(List.init (max 0 (List.length types - 1)) Fun.id) in
                  types, positions, selection_policy
              | _ -> invalid_arg ("plan call has no signature: " ^ target))
          | L.Local target ->
              (match List.assoc_opt target rule.binders with
              | Some (L.RelationType (inputs, output)) ->
                  inputs @ [output], List.init (List.length inputs) Fun.id,
                  L.Nondeterministic
              | _ -> invalid_arg ("plan callback has no signature: " ^ target))
      in
      let has_signature application = match application.L.target with
        | L.Local target ->
            (match List.assoc_opt target rule.binders with
            | Some (L.RelationType _) -> true | _ -> false)
        | L.Global target -> StringMap.mem target table in
      let output_bindings application =
        let _, positions, _ = call_shape application in
        let outputs = application.L.arguments
        |> List.mapi (fun i term -> i, term)
        |> List.filter_map (fun (i, term) ->
             if List.mem i positions then None else Some term)
        in
        let names = List.filter_map (function
          | L.Variable (name, _) when List.mem_assoc name rule.binders ->
              Some name
          | _ -> None) outputs in
        if names <> [] && List.length names = List.length outputs
          && List.length (List.sort_uniq String.compare names) = List.length names
        then names else []
      in
      let mentions name term =
        List.exists (fun (variable, _) -> variable = name)
          (Translator.variables_in_term term) in
      let mentioned_before index name =
        rule.premises |> List.mapi (fun i premise -> i, premise)
        |> List.exists (fun (i, premise) -> i < index &&
             List.exists (mentions name) (Traversal.premise_terms premise)) in
      let call_candidates = List.filter_map (fun (index, premise) ->
        match premise with
        | L.Holds application when has_signature application ->
            (match output_bindings application with
            | [] -> None
            | names when List.for_all (fun name ->
                not (mentioned_before index name)) names ->
                let _, positions, _ = call_shape application in
                let input_uses = application.arguments
                  |> List.mapi (fun i term -> i, term)
                  |> List.exists (fun (i, term) ->
                       List.mem i positions
                       && List.exists (fun name -> mentions name term) names) in
                if input_uses then None else Some names
            | _ -> None)
        | _ -> None)
        (List.mapi (fun i premise -> i, premise) rule.premises) in
      let fresh_candidates = List.filter_map (fun (index, premise) ->
        match premise with
        | L.Prop (L.Predicate
            (L.Native (("SpecTecFresh.Allocates" |
              "_root_.SpecTecFresh.Allocates"),
              [site; before; L.Variable (output, _); L.Variable (after, _)])))
          when output <> after && List.mem_assoc output rule.binders
            && List.mem_assoc after rule.binders
            && not (mentioned_before index output)
            && not (mentioned_before index after)
            && not (List.exists (mentions output) [site; before])
            && not (List.exists (mentions after) [site; before]) ->
              Some [output; after]
        | _ -> None) (List.mapi (fun i premise -> i, premise) rule.premises) in
      let candidate_groups = call_candidates @ fresh_candidates in
      let candidates = List.concat candidate_groups in
      let produced = candidate_groups
        |> List.filter (fun group -> List.for_all (fun name ->
             List.length (List.filter (String.equal name) candidates) = 1) group)
        |> List.concat in
      let initial = List.filter (fun (name, _) ->
        not (List.mem name produced)) rule.binders in
      let initial_scope = List.map (fun (member : L.rule) -> member.name) rules
        @ type_parameters in
      let print_call (premise_index : int) (env_binders : (string * L.type_ref) list)
          (application : L.application) =
        let scope = initial_scope @ List.map fst env_binders in
        let pattern = "()" in
        let lambda body = "(fun " ^ pattern ^ " => " ^ body ^ ")" in
        let argument_types, positions, policy = call_shape application in
        let indexed_types = List.mapi (fun i typ -> i, typ) argument_types in
        let inputs, outputs = List.partition
          (fun (i, _) -> List.mem i positions) indexed_types in
        let indexed_terms = List.mapi (fun i term -> i, term)
          application.arguments in
        let input_terms, output_terms = List.partition
          (fun (i, _) -> List.mem i positions) indexed_terms in
        let names = List.mapi (fun i _ -> "plan:arg:" ^ string_of_int i)
          argument_types in
        let synthetic = { application with
          arguments = List.map2 (fun name typ -> L.Variable (name, typ))
            names argument_types } in
        let names_for indexed = List.map (fun (i, _) -> List.nth names i) indexed in
        let input_pattern = eval_tuple_pattern (names_for inputs) in
        let output_pattern = eval_tuple_pattern (names_for outputs) in
        let input_type = eval_product_type scope (List.map snd inputs) in
        let output_type = eval_product_type scope (List.map snd outputs) in
        let policy = match policy with
          | L.Nondeterministic -> ".nondeterministic"
          | L.Ordered -> ".ordered" in
        let kind = match application.target with
          | L.Local _ -> `Internal
          | L.Global target when StringSet.mem target members -> `Internal
          | L.Global _ -> `External in
        let values = "({ Input := " ^ input_type ^ ", Output := "
          ^ output_type ^ ", inputPositions := ["
          ^ String.concat ", " (List.map string_of_int positions)
          ^ "], policy := " ^ policy in
        let signature = match kind with
          | `Scoped | `Internal ->
              let atom = print_atom component_relations (scope @ names)
                synthetic in
              let atom_lambda = if kind = `Scoped then "fun " ^ pattern
                ^ " " ^ input_pattern ^ " " ^ output_pattern ^ " => " ^ atom
                else "fun " ^ input_pattern ^ " " ^ output_pattern
                  ^ " => " ^ atom in
              values ^ ", atom := " ^ atom_lambda
              ^ " } : SpecTecPlan."
              ^ (if kind = `Scoped then "ScopedSignature Atom _"
                  else "Signature Atom") ^ ")"
          | `External ->
              (match application.target with
              | L.Global "$fresh_typeId" ->
                  let rule_index = Option.get (List.find_index
                    (fun (candidate : L.rule) -> candidate.name = rule.name) rules) in
                  let evaluation = print_eval_premise "" all_relations
                    component_relations members name rule_index premise_index
                    (scope @ names) (L.Holds synthetic) in
                  values ^ ", boundary := .priorSCC, holds := (fun "
                  ^ input_pattern ^ " " ^ output_pattern ^ " => "
                  ^ print_application (scope @ names) synthetic ^ ")"
                  ^ ", selection := some ⟨(fun " ^ input_pattern ^ " " ^ output_pattern
                  ^ " => " ^ evaluation.proposition ^ "), (fun " ^ input_pattern
                  ^ " " ^ output_pattern ^ " proof => "
                  ^ evaluation.public_evidence "proof" ^ ")⟩"
                  ^ " } : SpecTecPlan.ExternalSignature)"
              | _ -> print_application_suffix scope ".externalSignature"
                  {application with arguments = []}) in
        let input = lambda (eval_tuple_term scope (List.map snd input_terms)) in
        let output = lambda (eval_tuple_term scope (List.map snd output_terms)) in
        let failure = "(fun " ^ input_pattern ^ " " ^ output_pattern
          ^ " => " ^ print_public_failure (scope @ names) synthetic ^ ")" in
        kind, signature, input, output, failure
      in
      let steps, final_env, witness_names =
        List.fold_left (fun (steps, env, witnesses) (i, premise) ->
          let scope = initial_scope @ List.map fst env in
          let pattern = "()" in
          let lambda body = "(fun " ^ pattern ^ " => " ^ body ^ ")" in
          let step, env, witnesses = match premise with
          | L.Holds application when has_signature application ->
              let kind, signature, input, output, _ =
                print_call i env application in
              (match output_bindings application with
              | names when names <> []
                && List.for_all (fun name -> List.mem name produced) names ->
                  let env_outputs = List.map (fun name ->
                    name, List.assoc name rule.binders) names in
                  let witness_term = eval_tuple_pattern names in
                  (fun body -> "(SpecTecPlan.Plan."
                    ^ (match kind with `Scoped | `Internal -> "bindCall "
                        | `External -> "bindExternal ")
                    ^ signature ^ " " ^ input ^ " (fun " ^ witness_term
                    ^ " => " ^ body ^ "))"),
                  env @ env_outputs, witnesses @ [witness_term]
              | _ ->
                  (fun body -> "(SpecTecPlan.Plan."
                    ^ (match kind with `Scoped -> "callKnownScoped "
                        | `Internal -> "callKnown "
                        | `External -> "externalKnown ")
                    ^ signature ^ " " ^ input ^ " " ^ output ^ " " ^ body ^ ")"),
                  env, witnesses)
          | L.NotHolds (application, _) when has_signature application ->
              let kind, signature, input, output, failure =
                print_call i env application in
              (fun body -> "(SpecTecPlan.Plan."
                ^ (match kind with `Scoped -> "negativeScoped "
                    | `Internal -> "negative "
                    | `External -> "externalNegative ")
                ^ signature ^ " "
                ^ (if kind = `External then failure ^ " " else "")
                ^ input ^ " " ^ output ^ " " ^ body ^ ")"),
                env, witnesses
          | L.Prop (L.Predicate
              (L.Native (("SpecTecFresh.Allocates" |
                "_root_.SpecTecFresh.Allocates"),
                [site; before; output; after]))) ->
              (match output, after with
              | L.Variable (output_name, _), L.Variable (after_name, _)
                when List.mem output_name produced
                  && List.mem after_name produced ->
                  (fun body -> "(SpecTecPlan.Plan.bindFresh "
                    ^ lambda (print_term scope site) ^ " "
                    ^ lambda (print_term scope before) ^ " (fun "
                    ^ print_identifier output_name ^ " " ^ print_identifier after_name
                    ^ " => " ^ body ^ "))"),
                  env @ [output_name, List.assoc output_name rule.binders;
                    after_name, List.assoc after_name rule.binders],
                  witnesses @ [print_identifier output_name;
                    print_identifier after_name]
              | _ ->
                  (fun body -> "(SpecTecPlan.Plan.freshKnown "
                    ^ lambda (print_term scope site) ^ " "
                    ^ lambda (print_term scope before) ^ " "
                    ^ lambda (print_term scope output) ^ " "
                    ^ lambda (print_term scope after) ^ " " ^ body ^ ")"),
                  env, witnesses)
          | L.Holds _ | L.NotHolds _ | L.NotExists _ | L.Prop _ ->
              (fun body -> "(SpecTecPlan.Plan.guard "
                ^ lambda (print_local_side_premise scope premise)
                ^ " " ^ body ^ ")"), env, witnesses
          in
          (steps @ [(fun body -> "(SpecTecPlan.Plan.at " ^ string_of_int i
            ^ " " ^ step body ^ ")")], env, witnesses))
          ([], initial, List.map (fun (name, _) -> print_identifier name) initial)
          (List.mapi (fun i premise -> i, premise) rule.premises) in
      let final_scope = initial_scope @ List.map fst final_env in
      let final_pattern = "()" in
      let head = print_atom component_relations final_scope rule.conclusion in
      let body = "(SpecTecPlan.Plan.ret (fun " ^ final_pattern
        ^ " => " ^ head ^ "))" in
      let body = List.fold_right (fun step body -> step body) steps body in
      let rec bind_initial scope = function
        | [] -> body
        | (binder, typ) :: rest ->
            "(SpecTecPlan.Plan.bind (fun (" ^ print_identifier binder ^ " : "
            ^ print_type scope typ ^ ") => "
            ^ bind_initial (binder :: scope) rest ^ "))" in
      let body = bind_initial initial_scope initial in
      let recoverable = rule_recoverable name rule in
      let declaration_text = "def " ^ plan_name
        ^ print_wfs_parameters type_parameters equality_parameters print_parameters
        ^ " : SpecTecPlan.Alternative Atom Unit :=\n  { sourceIndex := "
        ^ string_of_int index ^ ", recoverable := ["
        ^ String.concat ", " (List.map string_of_int recoverable)
        ^ "], body := " ^ body ^ " }" in
      let type_arguments = String.concat ""
        (List.map (fun parameter -> " (" ^ print_identifier parameter
          ^ " := " ^ print_identifier parameter ^ ")") type_parameters) in
      let plan_ref = "(" ^ plan_name ^ type_arguments ^ ")" in
      let compiled = "(" ^ plan_ref ^ ".body.compile () "
        ^ plan_witness witness_names ^ ")" in
      { plan_declaration = declaration_text;
        plan_name; plan_owner = name; plan_rule = rule.name;
        witness_pattern = plan_witness witness_names;
        allowed_constructor = program_constructor (program_rule_name index)
          type_parameters equality_parameters print_parameters [] head plan_ref;
        plan_constructor = program_constructor (program_rule_name index)
          type_parameters equality_parameters print_parameters rule.binders
          head compiled }
  | _ -> invalid_arg "expected relation"

let print_plan_membership ~(component_index : int) (plans : local_plan_rule list) =
  let constructors = List.map (fun plan -> plan.allowed_constructor) plans in
  let allowed = if List.length constructors > 32 then
    print_program_membership ~program_name:"Allowed"
      ~index_type:"SpecTecPlan.Alternative Atom Unit"
      ~tactic_name:("cases_allowed_" ^ string_of_int component_index) constructors
    else "inductive Allowed : SpecTecPlan.Alternative Atom Unit → Prop where\n"
      ^ String.concat "\n" (List.map (fun constructor ->
          "  | " ^ constructor.constructor_name ^ constructor.constructor_parameters
          ^ " : Allowed " ^ constructor.rule_index) constructors) in
  let aliases = List.map (fun plan ->
    "abbrev InProgram." ^ plan.allowed_constructor.constructor_name
    ^ plan.allowed_constructor.constructor_parameters
    ^ " := SpecTecPlan.ProgramOf.compiled (allowed := Allowed) (entry := ()) (Allowed."
    ^ plan.allowed_constructor.constructor_name ^ " "
    ^ plan.allowed_constructor.constructor_arguments ^ ")") plans in
  String.concat "\n\n" (allowed ::
    "abbrev InProgram : SpecTecWFS.Program Atom := SpecTecPlan.ProgramOf Allowed ()"
    :: aliases)

let print_boundary_plan ?(binder_types = []) (index : int) (type_parameters : string list)
    (equality_parameters : string list) (print_parameters : string list)
    (binders : (string * L.type_ref) list) (constructor : program_constructor)
    (positive : string option) (side : string) : local_plan_rule =
  let plan_name = constructor.constructor_name ^ "_plan" in
  let pattern = plan_environment_pattern binders in
  let ret = "(SpecTecPlan.Plan.ret (fun " ^ pattern ^ " => "
    ^ constructor.constructor_head ^ "))" in
  let body = match positive with
    | Some atom -> "(SpecTecPlan.Plan.callKnownScoped "
        ^ "({ Input := Unit, Output := Unit, inputPositions := [], policy := .nondeterministic, "
        ^ "atom := fun " ^ pattern ^ " _ _ => " ^ atom
        ^ " } : SpecTecPlan.ScopedSignature Atom _) (fun _ => ()) (fun _ => ()) " ^ ret ^ ")"
    | None -> "(SpecTecPlan.Plan.guard (fun " ^ pattern ^ " => " ^ side ^ ") " ^ ret ^ ")" in
  let body = List.fold_right (fun (name, typ) body ->
    let typ = Option.value (List.assoc_opt name binder_types)
      ~default:(print_type type_parameters typ) in
    "(SpecTecPlan.Plan.choose (Value := " ^ typ
    ^ ") " ^ body ^ ")") binders body in
  let parameters = print_wfs_parameters type_parameters equality_parameters print_parameters in
  let allowed = program_constructor constructor.constructor_name type_parameters
    equality_parameters print_parameters [] constructor.constructor_head "" in
  let plan_ref = "(" ^ plan_name ^ " " ^ allowed.constructor_arguments ^ ")" in
  let witness_pattern = plan_witness (List.map (fun (name, _) -> print_identifier name) binders) in
  { plan_name; plan_owner = ""; plan_rule = ""; witness_pattern;
    plan_declaration = "def " ^ plan_name ^ parameters
      ^ " : SpecTecPlan.Alternative Atom Unit :=\n  { sourceIndex := " ^ string_of_int index
      ^ ", recoverable := [], body := " ^ body ^ " }";
    allowed_constructor = { allowed with rule_index = plan_ref };
    plan_constructor = { constructor with rule_index = "(" ^ plan_ref
      ^ ".body.compile () " ^ witness_pattern ^ ")" } }

let print_dispatch_plan relations members index declaration =
  match declaration with
  | L.Relation { name; type_parameters; equality_parameters; print_parameters;
                 argument_types; _ } ->
      let constructor = print_local_dispatch_constructor relations members index declaration in
      let binders = List.mapi (fun i typ -> "arg" ^ string_of_int i, typ) argument_types in
      let application = { L.target = L.Global name;
        type_arguments = List.map (fun p -> L.TypeParameter p) type_parameters;
        instance_arguments = []; print_instance_arguments = [];
        arguments = List.map (fun (name, typ) -> L.Variable (name, typ)) binders } in
      let positive = if StringSet.mem name members then
        Some (print_atom relations type_parameters application) else None in
      print_boundary_plan index type_parameters equality_parameters print_parameters
        binders constructor positive (print_application type_parameters application)
  | _ -> invalid_arg "expected relation"

let print_relation_local_program ~(atom_extern_relations : StringSet.t)
    ~(extern_relations : StringSet.t)
    ~(model_relations : StringSet.t) (analysis : Relation_graph.analysis)
    (relations : L.declaration list) : string =
  let table = relation_table relations in
  let owners = List.mapi (fun index (component : Relation_graph.component) ->
    index, component.relations) analysis.components
    |> List.fold_left (fun owners (index, names) -> List.fold_left
         (fun owners name -> StringMap.add name index owners) owners names) StringMap.empty in
  let external_signatures = List.fold_left (fun needed (edge : Relation_graph.edge) ->
    if StringMap.find_opt edge.source owners = StringMap.find_opt edge.target owners
    then needed else StringSet.add edge.target needed) StringSet.empty analysis.edges in
  let print_component (component_index : int)
      (component : Relation_graph.component) =
    let component_relations = List.map (fun name -> StringMap.find name table)
      component.relations in
    let members = StringSet.of_list component.relations in
    let needs_extern = not
      (StringSet.is_empty (StringSet.inter members extern_relations)) in
    let atom_needs_extern = not
      (StringSet.is_empty (StringSet.inter members atom_extern_relations)) in
    let needs_model = not
      (StringSet.is_empty (StringSet.inter members model_relations)) in
    atom_has_extern_types := atom_needs_extern;
    program_has_extern_types := needs_extern;
    program_has_p4_extern_model := needs_model;
    let qualified = component_namespace component in
    let rules = component_relations
      |> List.concat_map (function
           | L.Relation ({ rules; _ } as relation) ->
               List.map (fun rule -> L.Relation relation, rule) rules
           | _ -> [])
      |> List.mapi (fun index (relation, rule) -> index, relation, rule) in
    let callback_targets = analysis.callback_sites
      |> List.filter (fun (site : Relation_graph.callback_site) ->
           StringSet.mem site.relation members)
      |> List.concat_map (fun (site : Relation_graph.callback_site) -> site.targets)
      |> List.sort_uniq String.compare
      |> List.filter_map (fun name -> StringMap.find_opt name table) in
    let dispatch = List.mapi (fun offset declaration ->
      List.length rules + offset, declaration) callback_targets in
    let has_external_callback = List.exists (fun (site : Relation_graph.callback_site) ->
      StringSet.mem site.relation members && site.has_external) analysis.callback_sites in
    let dependencies = analysis.edges
      |> List.filter_map (fun (edge : Relation_graph.edge) ->
           if StringSet.mem edge.source members
              && not (StringSet.mem edge.target members)
           then Some edge.target else None)
      |> List.sort_uniq String.compare in
    let string_list values = "[" ^ String.concat ", "
      (List.map (fun value -> "\"" ^ escape_string value ^ "\"") values) ^ "]" in
    let metadata =
      "def metadata : SpecTecWFS.ComponentMetadata :=\n"
      ^ "  { relations := " ^ string_list component.relations
      ^ ", dependencies := " ^ string_list dependencies
      ^ ", recursive := " ^ string_of_bool component.recursive
      ^ ", negativeCycle := " ^ string_of_bool component.negative_cycle
      ^ ", externalCallback := " ^ string_of_bool has_external_callback ^ " }" in
    let plans = List.map (fun (index, relation, rule) ->
      print_local_plan_rule relations component_relations members index relation rule)
      rules in
    let plans = plans @ List.map (fun (index, declaration) ->
      print_dispatch_plan component_relations members index declaration) dispatch in
    let plans = if not has_external_callback then plans else
      let constructor = { constructor_name = "external_call";
        constructor_parameters = " {α β : Type} (f : α → β → Prop) (input : α) (output : β)";
        constructor_arguments = "(α := α) (β := β) f input output";
        constructor_fields = "α β f input output";
        constructor_head = "(" ^ explicit_atom "relation_call"
          ^ " α β (_root_.SpecTecRelationRef.external f) input output)";
        rule_index = "" } in
      let binders = ["f", L.RelationType ([L.TypeParameter "α"], L.TypeParameter "β");
        "input", L.TypeParameter "α"; "output", L.TypeParameter "β"] in
      (* A callback value is a Lean predicate, not a named RelationRef. *)
      let plan = print_boundary_plan ~binder_types:["f", "α → β → Prop"]
        (List.length rules + List.length dispatch)
        ["α"; "β"] [] [] binders constructor None "f input output" in
      plans @ [plan] in
    let local = "namespace " ^ qualified ^ "\n\n"
      ^ print_atoms component_relations ^ "\n\n"
      ^ String.concat "\n\n" (List.map (print_plan_signature component_relations) component_relations)
      ^ "\n\n" ^ String.concat "\n\n" (List.map (fun plan -> plan.plan_declaration) plans)
      ^ "\n\n"
      ^ print_plan_membership ~component_index plans ^ "\n\n" ^ metadata
      ^ "\n\nend " ^ qualified in
    let public = List.map
      (print_local_public_relation qualified component.recursive component_relations)
      component_relations in
    let theorems = List.map (fun (index, relation, rule) ->
      print_local_rule_theorem qualified component_relations members index relation rule
        (List.find (fun plan -> plan.plan_name = program_rule_name index ^ "_plan") plans)) rules
      @ List.map (fun (index, declaration) ->
          print_local_dispatch_theorem qualified members index declaration) dispatch in
    let cases = List.map
      (print_local_rule_cases qualified component_index members component_relations rules)
      component_relations in
    let evaluators = component_relations
      |> List.filter (fun declaration ->
           emits_ordered_evaluator (relation_name declaration))
      |> List.map
           (print_ordered_evaluator qualified component_relations plans
              component.recursive) in
    let notation = List.concat_map declaration_notation component_relations in
    let wrap body = if body = "" then "-- no declarations"
      else if not needs_extern && not needs_model then body else
        "section\n\n"
        ^ (if needs_extern then "variable [SpecTecExternTypes]\n" else "")
        ^ (if needs_model then "variable [SpecTecP4ExternModel]\n" else "")
        ^ "\n" ^ body ^ "\n\nend" in
    let marker kind boundary = "-- SpecTecModule:" ^ kind ^ ":"
      ^ boundary ^ ":" ^ string_of_int component_index in
    let semantics = String.concat "\n\n" (local :: public @ theorems) in
    let evaluation = String.concat "\n\n" (evaluators
      @ (component_relations |> List.filter (fun relation ->
               StringSet.mem (relation_name relation) external_signatures)
           |> List.map (print_external_signature qualified)) @ notation) in
    let inversions = String.concat "\n\n" cases in
    String.concat "\n\n" [
      marker "sem" "begin"; wrap semantics; marker "sem" "end";
      marker "eval" "begin"; wrap evaluation; marker "eval" "end";
      marker "inv" "begin"; wrap inversions; marker "inv" "end" ]
  in
  String.concat "\n\n" (List.mapi print_component analysis.components)

let print ?(fresh_rollback = false) ?(relation_local = false) ?analysis
    (program : L.program) : string =
  let relations : L.declaration list = List.concat_map relations_in_group program in
  let rec declarations_in_group (group : L.declaration_group) : L.declaration list =
    match group with
    | L.Single declaration -> [ declaration ]
    | L.Mutual declarations -> declarations
    | L.DerivingDecidableEq group -> declarations_in_group group
    | L.ManualDecidableEq _ | L.ManualPrinter _ -> []
  in
  let all_declarations = List.concat_map declarations_in_group program in
  let extern_types : bool =
    List.exists (function L.ExternType _ -> true | _ -> false) all_declarations
  in
  let extern_dependent_types = Order.extern_dependent_types all_declarations in
  let atom_extern_relations : StringSet.t =
    List.fold_left
      (fun names -> function
        | L.Relation { name; argument_types; _ }
          when List.exists
            (fun typ ->
              not (Order.StringSet.is_empty
                (Order.StringSet.inter extern_dependent_types (Order.type_references typ))))
            argument_types -> StringSet.add name names
        | _ -> names)
      StringSet.empty relations
  in
  let atom_needs_extern_types = not (StringSet.is_empty atom_extern_relations) in
  let p4_externs : bool =
    List.exists
      (function
        | L.Relation { name = "ExternFunctionCall_eval_lctk"
                       | "ExternFunctionCall_eval"
                       | "ExternMethodCall_eval"; _ } -> true
        | _ -> false)
      relations
  in
  extern_types_active := extern_types;
  atom_has_extern_types := atom_needs_extern_types;
  let rec uses_p4_model (term : L.term) =
    match term with
    | L.Native (("SpecTec.externStaticAllowed" | "SpecTec.externFunctionAllowed"
                 | "SpecTec.externMethodAllowed"), _) -> true
    | _ -> List.exists uses_p4_model (Traversal.term_children term)
  in
  program_has_p4_extern_model := List.exists (function
    | L.Relation { rules; _ } -> List.exists (fun (rule : L.rule) ->
        List.exists uses_p4_model
          (List.concat_map Traversal.premise_terms rule.premises)) rules
    | _ -> false) relations;
  program_has_extern_types := atom_needs_extern_types
    || (!program_has_p4_extern_model
        && List.exists (fun name -> Order.StringSet.mem name extern_dependent_types)
          Extern_model.p4_model_type_names);
  let direct_extern_relations = List.fold_left (fun names declaration ->
    let references = Order.references declaration in
    if Order.StringSet.is_empty
         (Order.StringSet.inter extern_dependent_types references)
    then names else StringSet.add (relation_name declaration) names)
    StringSet.empty relations in
  let direct_model_relations = List.fold_left (fun names declaration ->
    match declaration with
    | L.Relation { name; rules; _ }
      when List.exists (fun (rule : L.rule) ->
        List.exists uses_p4_model
          (List.concat_map Traversal.premise_terms rule.premises)) rules ->
        StringSet.add name names
    | _ -> names) StringSet.empty relations in
  let close_relation_dependencies (roots : StringSet.t) : StringSet.t =
    match analysis with
    | None -> roots
    | Some (graph : Relation_graph.analysis) ->
        let rec close names =
          let next = List.fold_left (fun names (edge : Relation_graph.edge) ->
            if StringSet.mem edge.target names then StringSet.add edge.source names
            else names) names graph.edges in
          if StringSet.equal names next then names else close next
        in
        close roots
  in
  (* The current P4 model class mentions architecture types, so even its
     static-only predicates carry the extern-type instance.  Keep that
     dependency explicit instead of relying on an ambient namespace variable. *)
  let local_extern_relations = close_relation_dependencies
    (StringSet.union direct_extern_relations direct_model_relations) in
  let local_model_relations = close_relation_dependencies direct_model_relations in
  let all_relation_names =
    StringSet.of_list (List.map relation_name relations) in
  extern_relation_names :=
    if relation_local then local_extern_relations
    else if !program_has_extern_types then all_relation_names
    else StringSet.empty;
  model_relation_names :=
    if relation_local then local_model_relations
    else if !program_has_p4_extern_model then all_relation_names
    else StringSet.empty;
  let other_groups : L.declaration_group list =
    List.filter (fun group -> relations_in_group group = []) program
  in
  let printed_other_groups =
    let body = String.concat "\n\n" (List.map print_group other_groups) in
    if relation_local && extern_types && body <> "" then
      "section\n\nvariable [SpecTecExternTypes]\n\n" ^ body ^ "\n\nend"
    else body
  in
  (* A full specification has thousands of constructors in one inductive
     program, which exceeds Lean's default elaboration heartbeat limit. *)
  "-- SpecTec Lean mode: "
  ^ (if relation_local then "relation-local" else if fresh_rollback then
       "legacy-fresh-rollback" else "legacy-fresh-exact-counter")
  ^ "\nset_option autoImplicit false\nset_option linter.unusedVariables false\n"
  ^ (if extern_types then "set_option linter.unusedSectionVars false\n" else "")
  ^ (if List.length relations > 100 then "set_option maxHeartbeats 0\n" else "")
  ^ "\n"
  ^ print_prelude ^ "\n\n"
  ^ (if extern_types then Extern_model.types_source ^ "\n\n" else "")
  ^ (if relations = [] then "" else Wfs_backend.source ^ "\n\n"
     ^ if relation_local then Ordered_semantics.source ^ "\n\n" else "")
  ^ (if relation_local then Fresh_nominal.source ^ "\n\n" else "")
  ^ (if relation_local && relations <> [] then Typed_rule_plan.source ^ "\n\n" else "")
  ^ "namespace SpecTec\n\n"
  ^ (if extern_types && not relation_local then
       "variable [SpecTecExternTypes]\n\n" else "")
  ^ printed_other_groups
  ^ (if relation_local || fresh_rollback then
       "\n\n" ^ Fresh_alpha.render ~nominal:relation_local program else "")
  ^ (if p4_externs then "\n\n"
       ^ if relation_local && extern_types then
           "section\n\nvariable [SpecTecExternTypes]\n\n"
           ^ Extern_model.p4_source ^ "\n\nend"
         else Extern_model.p4_source
     else "")
  ^ (if relations = [] then "" else "\n\n"
     ^ if relation_local then
         print_relation_local_program
           ~atom_extern_relations
           ~extern_relations:local_extern_relations
           ~model_relations:local_model_relations
           (Option.get analysis) relations
       else print_wfs_program relations)
  ^ "\n\nend SpecTec"

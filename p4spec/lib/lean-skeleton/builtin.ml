module L = Ast.Lean

let name (value : string) : L.type_ref = L.Name value
let list (value : L.type_ref) : L.type_ref = L.BuiltinType ("List", [ value ])
let set (value : L.type_ref) : L.type_ref = L.Applied ("set", [ value ])

let is_text_set_operation (builtin_name : string) : bool =
  List.mem builtin_name
    [ "union_set"; "unions_set"; "diff_set"; "intersect_set" ]

let pair (left : L.type_ref) (right : L.type_ref) : L.type_ref =
  L.TupleType [ left; right ]

let definition (name : string) (type_parameters : string list)
    (parameters : L.type_ref list) (result : L.type_ref) (body : string) :
    (L.builtin, string) result =
  Ok
    { name; type_parameters; equality_parameters = []; print_parameters = [];
      parameters; result; body }

let band_body : string =
  "match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat \
   (Nat.land a b) | Int.ofNat a, Int.negSucc b => Int.ofNat (a - \
   Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.ofNat (b - Nat.land \
   a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.lor a b)"

let bxor_body : string =
  "match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat \
   (Nat.xor a b) | Int.ofNat a, Int.negSucc b => Int.negSucc (Nat.xor a \
   b) | Int.negSucc a, Int.ofNat b => Int.negSucc (Nat.xor a b) | \
   Int.negSucc a, Int.negSucc b => Int.ofNat (Nat.xor a b)"

(* These operations are deliberately monomorphic. SpecTec's OCaml runtime
   orders set elements with Value.compare, whose text case is String.compare.
   That order agrees with Lean String ordering for valid UTF-8; other key
   types are rejected at calls because their observable ordering is not
   reproduced here. *)
let text_set_definition (builtin_name : string) : (L.builtin, string) result =
  let text : L.type_ref = L.BuiltinType ("String", []) in
  let text_set : L.type_ref = set text in
  let define = definition builtin_name [] in
  match builtin_name with
  | "union_set" ->
      define [ text_set; text_set ] text_set
        "match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => \
         .«`{ % `}» (_root_.specTecTextSetUnion left right)"
  | "unions_set" ->
      define [ list text_set ] text_set
        ".«`{ % `}» (arg0.foldr (fun current result => match current with | \
         .«`{ % `}» elements => _root_.specTecTextSetUnion elements result) [])"
  | "diff_set" ->
      define [ text_set; text_set ] text_set
        "match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => \
         .«`{ % `}» (_root_.specTecTextSetDiff left right)"
  | "intersect_set" ->
      define [ text_set; text_set ] text_set
        "match arg0, arg1 with | .«`{ % `}» left, .«`{ % `}» right => \
         .«`{ % `}» (_root_.specTecTextSetIntersect left right)"
  | _ -> assert false

let translate (builtin_name : string) (type_parameters : string list) :
    (L.builtin, string) result =
  let nat : L.type_ref = L.BuiltinType ("Nat", []) in
  let int : L.type_ref = L.BuiltinType ("Int", []) in
  let text : L.type_ref = L.BuiltinType ("String", []) in
  let define = definition builtin_name type_parameters in
  match (builtin_name, type_parameters) with
  | "sum_nat", [] -> define [ list nat ] nat "arg0.foldl (· + ·) 0"
  | "sum_int", [] -> define [ list int ] int "arg0.foldl (· + ·) 0"
  | "max_int", [] ->
      define
        [ list int ]
        int "match arg0 with | [] => 0 | x :: xs => xs.foldl max x"
  | "min_int", [] ->
      define
        [ list int ]
        int "match arg0 with | [] => 0 | x :: xs => xs.foldl min x"
  | "strip_all_whitespace", [] ->
      define [ text ] text "String.ofList (arg0.toList.filter (· != ' '))"
  | "rev_", [ x ] ->
      let x : L.type_ref = L.TypeParameter x in
      define [ list x ] (list x) "arg0.reverse"
  | "concat_", [ x ] ->
      let x : L.type_ref = L.TypeParameter x in
      define [ list (list x) ] (list x) "arg0.flatten"
  | "sort_", [ x ] ->
      let item : L.type_ref = pair nat (L.TypeParameter x) in
      define
        [ list item ]
        (list item) "arg0.mergeSort (fun left right => left.1 ≤ right.1)"
  | "pow2", [] -> define [ nat ] int "(2 : Int) ^ arg0"
  | "bits_to_int_unsigned", [] ->
      define
        [ name "bits" ]
        int
        "arg0.foldl (fun value bit => 2 * value + (if bit then 1 else 0)) (0 : \
         Int)"
  | "bneg", [] -> define [ int ] int "-arg0 - 1"
  | "band", [] -> define [ int; int ] int band_body
  | "bor", [] ->
      define [ int; int ] int
        "match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat \
         (Nat.lor a b) | Int.ofNat a, Int.negSucc b => Int.negSucc (b - \
         Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.negSucc (a - \
         Nat.land a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.land \
         a b)"
  | "bxor", [] -> define [ int; int ] int bxor_body
  | "text_to_int", _ ->
      Error
        "text_to_int because Lean and SpecTec accept different numeral syntax"
  (* PL list subsumption can pass a Nat-tagged value here. The OCaml builtin
     omits its sign, but this is unused in the spec, so model only Int values. *)
  | "int_to_text", [] ->
      define [ int ] text
        "(if arg0 ≥ 0 then \"+\" else \"-\") ++ toString arg0.natAbs"
  | "split_text", _ ->
      Error "split_text because SpecTec requires a one-byte separator"
  | "transpose_", _ ->
      Error "transpose_ because SpecTec rejects ragged matrices"
  | ("intersect_set" | "union_set" | "unions_set" | "diff_set"), [ _ ] ->
      text_set_definition builtin_name
  | "sub_set", _ -> Error "sub_set without SpecTec set representation"
  | "eq_set", _ -> Error "eq_set without SpecTec set representation"
  | "fresh_typeId", _ ->
      Error "fresh_typeId must be lowered as a counter-threaded relation"
  | "bits_to_int_signed", _ ->
      Error
        "bits_to_int_signed without the SpecTec bits type and empty-input error"
  | "int_to_bits_unsigned", _ ->
      Error
        "int_to_bits_unsigned without the SpecTec bits type and width bounds"
  | "int_to_bits_signed", _ ->
      Error "int_to_bits_signed without the SpecTec bits type and width bounds"
  | "bitacc", _ -> Error "bitacc without SpecTec's inclusive bit-slice bounds"
  | "bitacc_replace", _ ->
      Error "bitacc_replace without SpecTec's unmasked replacement behavior"
  | "sum", _ ->
      Error "sum because the current SpecTec runtime has no implementation"
  | "max", _ ->
      Error "max because the current SpecTec runtime has no implementation"
  | "min", _ ->
      Error "min because the current SpecTec runtime has no implementation"
  | "fresh_tid", _ ->
      Error
        "fresh_tid because the current SpecTec runtime has no implementation"
  | ( ( "sum_nat" | "sum_int" | "max_int" | "min_int" | "strip_all_whitespace"
      | "rev_" | "concat_" | "sort_" | "pow2" | "bits_to_int_unsigned" | "bneg"
      | "band" | "bor" | "bxor" | "int_to_text" ),
      _ ) ->
      Error
        (builtin_name ^ " because its number of type parameters is unexpected")
  | ("intersect_set" | "union_set" | "unions_set" | "diff_set"), _ ->
      Error
        (builtin_name ^ " because its number of type parameters is unexpected")
  | _, _ -> Error (builtin_name ^ " because no SpecTec implementation is known")

(* The SpecTec declaration of a text set operation stays generic in K, while
   its Lean definition is specialized to String. *)
let signature (builtin_name : string) (type_parameters : string list) :
    (L.type_ref list * L.type_ref, string) result =
  if is_text_set_operation builtin_name then
    match type_parameters with
    | [ key ] ->
        let generic_set : L.type_ref = set (L.TypeParameter key) in
        let parameters : L.type_ref list =
          if builtin_name = "unions_set" then [ list generic_set ]
          else [ generic_set; generic_set ]
        in
        Ok (parameters, generic_set)
    | _ ->
        Error
          (builtin_name ^ " because its number of type parameters is unexpected")
  else
    match translate builtin_name type_parameters with
    | Ok builtin -> Ok (builtin.parameters, builtin.result)
    | Error reason -> Error reason

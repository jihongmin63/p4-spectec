module L = Ast.Lean

(* Builtins that are partial or compare IL values, translated as relations
   following p4spec/lib/interface/builtin. An input on which the OCaml
   implementation fails has no rule. *)

type constructor_lookup =
  string -> L.type_ref list -> string list -> L.constructor_ref

let names : string list =
  [ "find_map"; "find_maps"; "add_map"; "adds_map"; "update_map"; "assoc_";
    "distinct_"; "partition_"; "max_nat"; "min_nat"; "strip_prefix";
    "strip_suffix"; "shl"; "shr"; "shr_arith"; "int_to_bitstr";
    "bitstr_to_int"; "split_text"; "sub_set"; "eq_set";
    "bits_to_int_signed"; "int_to_bits_unsigned"; "int_to_bits_signed";
    "bitacc"; "bitacc_replace"; "text_to_int"; "print_";
    "fresh_typeId" ]

let is_relation (name : string) : bool = List.mem name names

let nat : L.type_ref = L.BuiltinType ("Nat", [])
let int : L.type_ref = L.BuiltinType ("Int", [])
let bool : L.type_ref = L.BuiltinType ("Bool", [])
let text : L.type_ref = L.BuiltinType ("String", [])
let list (typ : L.type_ref) : L.type_ref = L.BuiltinType ("List", [ typ ])
let option (typ : L.type_ref) : L.type_ref = L.BuiltinType ("Option", [ typ ])
let key : L.type_ref = L.TypeParameter "K"
let value : L.type_ref = L.TypeParameter "V"
let map : L.type_ref = L.Applied ("map", [ key; value ])
let pair : L.type_ref = L.Applied ("pair", [ key; value ])
let set : L.type_ref = L.Applied ("set", [ key ])
let bits : L.type_ref = L.Name "bits"
let left : L.type_ref = L.TypeParameter "X"
let right : L.type_ref = L.TypeParameter "Y"

let signature (name : string) (type_parameters : string list) :
    (L.type_ref list * L.type_ref, string) result =
  let expect (expected : string list) (arguments : L.type_ref list)
      (result : L.type_ref) : (L.type_ref list * L.type_ref, string) result =
    if type_parameters = expected then Ok (arguments, result)
    else
      Error (name ^ " because its type parameters differ from the SpecTec declaration")
  in
  match name with
  | "find_map" -> expect [ "K"; "V" ] [ map; key ] (option value)
  | "find_maps" -> expect [ "K"; "V" ] [ list map; key ] (option value)
  | "add_map" | "update_map" -> expect [ "K"; "V" ] [ map; key; value ] map
  | "adds_map" -> expect [ "K"; "V" ] [ map; list key; list value ] map
  | "assoc_" ->
      expect [ "X"; "Y" ] [ left; list (L.TupleType [ left; right ]) ]
        (option right)
  | "distinct_" -> expect [ "K" ] [ list key ] bool
  | "partition_" ->
      expect [ "X" ] [ list left; nat ]
        (L.TupleType [ list left; list left ])
  | "max_nat" | "min_nat" -> expect [] [ list nat ] nat
  | "strip_prefix" | "strip_suffix" -> expect [] [ text; text ] text
  | "split_text" -> expect [] [ text; text ] (list text)
  | "sub_set" | "eq_set" -> expect [ "K" ] [ set; set ] bool
  | "shl" | "shr" | "int_to_bitstr" | "bitstr_to_int" -> expect [] [ int; int ] int
  | "shr_arith" -> expect [] [ int; int; int ] int
  | "bits_to_int_signed" -> expect [] [ bits ] int
  | "int_to_bits_unsigned" | "int_to_bits_signed" ->
      expect [] [ nat; int ] bits
  | "bitacc" -> expect [] [ int; int; int ] int
  | "bitacc_replace" -> expect [] [ int; int; int; int ] int
  | "text_to_int" -> expect [] [ text ] int
  | "print_" -> expect [ "X" ] [ left ] text
  | "fresh_typeId" -> expect [] [] (L.Name "typeId")
  | _ -> Error (name ^ " because no relation builtin implementation is known")

let variable (name : string) (typ : L.type_ref) : L.term = L.Variable (name, typ)
let number (literal : string) (typ : L.type_ref) : L.term = L.Number (literal, typ)
let native (name : string) (arguments : L.term list) : L.term = L.Native (name, arguments)
let cons (head : L.term) (tail : L.term) : L.term = L.Binary ("::", head, tail)
let none : L.term = native "Option.none" []
let some (term : L.term) : L.term = native "Option.some" [ term ]

let application (name : string) (types : L.type_ref list) (arguments : L.term list) :
    L.application =
  { target = L.Global ("$" ^ name); type_arguments = types;
    instance_arguments = []; print_instance_arguments = []; arguments }

let holds (name : string) (types : L.type_ref list) (arguments : L.term list) :
    L.premise =
  L.Holds (application name types arguments)

let comparison (operator : L.comparison) (left : L.term) (right : L.term) : L.premise =
  L.Prop (L.Comparison (operator, left, right))

let rule (relation : string) (types : L.type_ref list) (name : string)
    (binders : (string * L.type_ref) list) (premises : L.premise list)
    (arguments : L.term list) : L.rule =
  { name; binders; premises; catchable = [];
    conclusion = application relation types arguments }

let relation ?(print_parameters = []) (name : string)
    (type_parameters : string list)
    (argument_types : L.type_ref list) (rules : L.rule list) : L.declaration =
  L.Relation
    { name = "$" ^ name; type_parameters; equality_parameters = [];
      print_parameters; argument_types;
      input_positions = Some (List.init (max 0 (List.length argument_types - 1)) Fun.id);
      selection_policy = L.Nondeterministic;
      rules; notation = None }

let builtin (name : string) (parameters : L.type_ref list)
    (result : L.type_ref) (body : string) : L.declaration =
  L.Builtin
    { name = "$" ^ name; type_parameters = []; equality_parameters = [];
      print_parameters = []; parameters; result; body }

(* First pair with key k: a later pair is reached only past pairs with other
   keys, as in Maps.map_find_opt and Lists.assoc_. *)
let find_map (relation_types : L.type_ref list) (constructor : constructor_lookup) :
    L.declaration list =
  let types : L.type_ref list = [ key; value ] in
  let helper : string = "find_map:list" in
  let pair_of (k : L.term) (v : L.term) : L.term =
    L.Constructor (constructor "pair" types [ "%"; "':'"; "%" ], [ k; v ])
  in
  let set_of (pairs : L.term) : L.term =
    L.Constructor (constructor "set" [ pair ] [ "`{"; "%"; "`}" ], [ pairs ])
  in
  let pairs : L.term = variable "ps" (list pair) in
  let k : L.term = variable "k" key in
  let other : L.term = variable "k'" key in
  let v : L.term = variable "v" value in
  let result : L.term = variable "r" (option value) in
  [ relation helper [ "K"; "V" ] [ list pair; key; option value ]
      [ rule helper types "nil" [ ("k", key) ] [] [ L.ListLiteral []; k; none ];
        rule helper types "hit" [ ("k", key); ("v", value); ("ps", list pair) ] []
          [ cons (pair_of k v) pairs; k; some v ];
        rule helper types "miss"
          [ ("k", key); ("k'", key); ("v", value); ("ps", list pair); ("r", option value) ]
          [ comparison L.Ne other k; holds helper types [ pairs; k; result ] ]
          [ cons (pair_of other v) pairs; k; result ] ];
    relation "find_map" [ "K"; "V" ] relation_types
      [ rule "find_map" types "find"
          [ ("ps", list pair); ("k", key); ("r", option value) ]
          [ holds helper types [ pairs; k; result ] ]
          [ set_of pairs; k; result ] ] ]

(* The first map with a binding wins, as in the fold of Maps.find_maps. *)
let find_maps (relation_types : L.type_ref list) : L.declaration list =
  let types : L.type_ref list = [ key; value ] in
  let m : L.term = variable "m" map in
  let ms : L.term = variable "ms" (list map) in
  let k : L.term = variable "k" key in
  let v : L.term = variable "v" value in
  let result : L.term = variable "r" (option value) in
  [ relation "find_maps" [ "K"; "V" ] relation_types
      [ rule "find_maps" types "nil" [ ("k", key) ] [] [ L.ListLiteral []; k; none ];
        rule "find_maps" types "hit"
          [ ("m", map); ("ms", list map); ("k", key); ("v", value) ]
          [ holds "find_map" types [ m; k; some v ] ]
          [ cons m ms; k; some v ];
        rule "find_maps" types "miss"
          [ ("m", map); ("ms", list map); ("k", key); ("r", option value) ]
          [ holds "find_map" types [ m; k; none ];
            holds "find_maps" types [ ms; k; result ] ]
          [ cons m ms; k; result ] ] ]

(* Maps.map_update replaces the first pair with key k in place and appends
   when there is none. *)
let add_map (name : string) (relation_types : L.type_ref list)
    (constructor : constructor_lookup) : L.declaration list =
  let types : L.type_ref list = [ key; value ] in
  let helper : string = name ^ ":list" in
  let pair_of (k : L.term) (v : L.term) : L.term =
    L.Constructor (constructor "pair" types [ "%"; "':'"; "%" ], [ k; v ])
  in
  let set_of (pairs : L.term) : L.term =
    L.Constructor (constructor "set" [ pair ] [ "`{"; "%"; "`}" ], [ pairs ])
  in
  let pairs : L.term = variable "ps" (list pair) in
  let updated : L.term = variable "qs" (list pair) in
  let k : L.term = variable "k" key in
  let other : L.term = variable "k'" key in
  let v : L.term = variable "v" value in
  let old : L.term = variable "old" value in
  [ relation helper [ "K"; "V" ] [ list pair; key; value; list pair ]
      [ rule helper types "nil" [ ("k", key); ("v", value) ] []
          [ L.ListLiteral []; k; v; L.ListLiteral [ pair_of k v ] ];
        rule helper types "hit"
          [ ("k", key); ("v", value); ("old", value); ("ps", list pair) ] []
          [ cons (pair_of k old) pairs; k; v; cons (pair_of k v) pairs ];
        rule helper types "miss"
          [ ("k", key); ("k'", key); ("v", value); ("old", value);
            ("ps", list pair); ("qs", list pair) ]
          [ comparison L.Ne other k; holds helper types [ pairs; k; v; updated ] ]
          [ cons (pair_of other old) pairs; k; v; cons (pair_of other old) updated ] ];
    relation name [ "K"; "V" ] relation_types
      [ rule name types "update"
          [ ("ps", list pair); ("qs", list pair); ("k", key); ("v", value) ]
          [ holds helper types [ pairs; k; v; updated ] ]
          [ set_of pairs; k; v; set_of updated ] ] ]

(* List.fold_left2 fails on lists of different lengths. *)
let adds_map (relation_types : L.type_ref list) : L.declaration list =
  let types : L.type_ref list = [ key; value ] in
  let m : L.term = variable "m" map in
  let next : L.term = variable "next" map in
  let result : L.term = variable "r" map in
  let k : L.term = variable "k" key in
  let v : L.term = variable "v" value in
  let ks : L.term = variable "ks" (list key) in
  let vs : L.term = variable "vs" (list value) in
  [ relation "adds_map" [ "K"; "V" ] relation_types
      [ rule "adds_map" types "nil" [ ("m", map) ] []
          [ m; L.ListLiteral []; L.ListLiteral []; m ];
        rule "adds_map" types "step"
          [ ("m", map); ("next", map); ("r", map); ("k", key); ("v", value);
            ("ks", list key); ("vs", list value) ]
          [ holds "add_map" types [ m; k; v; next ];
            holds "adds_map" types [ next; ks; vs; result ] ]
          [ m; cons k ks; cons v vs; result ] ] ]

let assoc (relation_types : L.type_ref list) : L.declaration list =
  let types : L.type_ref list = [ left; right ] in
  let entries : L.type_ref = list (L.TupleType [ left; right ]) in
  let k : L.term = variable "key" left in
  let other : L.term = variable "other" left in
  let v : L.term = variable "value" right in
  let pairs : L.term = variable "ps" entries in
  let result : L.term = variable "r" (option right) in
  [ relation "assoc_" [ "X"; "Y" ] relation_types
      [ rule "assoc_" types "nil" [ ("key", left) ] [] [ k; L.ListLiteral []; none ];
        rule "assoc_" types "hit" [ ("key", left); ("value", right); ("ps", entries) ] []
          [ k; cons (L.Tuple (k, v)) pairs; some v ];
        rule "assoc_" types "miss"
          [ ("key", left); ("other", left); ("value", right); ("ps", entries);
            ("r", option right) ]
          [ comparison L.Ne other k; holds "assoc_" types [ k; pairs; result ] ]
          [ k; cons (L.Tuple (other, v)) pairs; result ] ] ]

(* The OCaml set of the elements has as many elements as the list. *)
let distinct (relation_types : L.type_ref list) : L.declaration list =
  let elements : L.term = variable "xs" (list key) in
  let result : L.term = variable "b" bool in
  [ relation "distinct_" [ "K" ] relation_types
      [ rule "distinct_" [ key ] "distinct" [ ("xs", list key); ("b", bool) ]
          [ L.Prop (L.Iff (L.IsTrue result, L.Predicate (native "List.Nodup" [ elements ]))) ]
          [ elements; result ] ] ]

let set_comparison (name : string) (relation_types : L.type_ref list)
    (constructor : constructor_lookup) : L.declaration list =
  let elements_left : L.term = variable "xs" (list key) in
  let elements_right : L.term = variable "ys" (list key) in
  let result : L.term = variable "b" bool in
  let set_of (elements : L.term) : L.term =
    L.Constructor (constructor "set" [ key ] [ "`{"; "%"; "`}" ], [ elements ])
  in
  let included (source : L.term) (target : L.term) : L.prop =
    let element : L.term = variable "x" key in
    L.Forall
      ( "x", key,
        L.Implies
          (L.Membership (element, source), L.Membership (element, target)) )
  in
  let condition : L.prop =
    let forward : L.prop = included elements_left elements_right in
    if name = "sub_set" then forward
    else L.And (forward, included elements_right elements_left)
  in
  [ relation name [ "K" ] relation_types
      [ rule name [ key ] "compare"
          [ ("xs", list key); ("ys", list key); ("b", bool) ]
          [ L.Prop (L.Iff (L.IsTrue result, condition)) ]
          [ set_of elements_left; set_of elements_right; result ] ] ]

(* The runtime also fails for n >= 2^62 when converting n to a machine int;
   that interpreter limit is not modeled. *)
let partition (relation_types : L.type_ref list) : L.declaration list =
  let elements : L.term = variable "xs" (list left) in
  let count : L.term = variable "n" nat in
  [ relation "partition_" [ "X" ] relation_types
      [ rule "partition_" [ left ] "partition" [ ("xs", list left); ("n", nat) ] []
          [ elements; count;
            L.Tuple
              ( native "List.take" [ count; elements ],
                native "List.drop" [ count; elements ] ) ] ] ]

(* The OCaml builtin fails on an empty list. *)
let extremum (name : string) (relation_types : L.type_ref list) (operation : string) :
    L.declaration list =
  let head : L.term = variable "head" nat in
  let tail : L.term = variable "tail" (list nat) in
  [ relation name [] relation_types
      [ rule name [] "nonempty" [ ("head", nat); ("tail", list nat) ] []
          [ cons head tail; native "List.foldl" [ native operation []; head; tail ] ] ] ]

(* Byte prefixes and suffixes of valid UTF-8 text are String appends. *)
let strip (name : string) (relation_types : L.type_ref list) : L.declaration list =
  let whole : L.term = variable "t" text in
  let result : L.term = variable "r" text in
  let affix_name : string = if name = "strip_prefix" then "p" else "s" in
  let affix : L.term = variable affix_name text in
  let joined : L.term =
    if name = "strip_prefix" then L.Binary ("++", affix, result)
    else L.Binary ("++", result, affix)
  in
  [ relation name [] relation_types
      [ rule name [] "strip" [ ("t", text); (affix_name, text); ("r", text) ]
          [ comparison L.Eq whole joined ] [ whole; affix; result ] ] ]

(* A one-byte UTF-8 separator is ASCII, so String.splitOn agrees with
   String.split_on_char and preserves empty fields. *)
let split_text (relation_types : L.type_ref list) : L.declaration list =
  let whole : L.term = variable "t" text in
  let separator : L.term = variable "separator" text in
  let result : L.term = variable "parts" (list text) in
  let split : L.term = native "String.splitOn" [ whole; separator ] in
  [ relation "split_text" [] relation_types
      [ rule "split_text" [] "split"
          [ ("t", text); ("separator", text); ("parts", list text) ]
          [ comparison L.Eq
              (native "String.utf8ByteSize" [ separator ])
              (number "1" nat);
            comparison L.Eq result split ]
          [ whole; separator; result ] ] ]

let bit_width_limit : L.term = number "2048" int

(* The OCaml loops run offset times, none when offset <= 0; Bigint division
   truncates toward zero. *)
let shift (name : string) (relation_types : L.type_ref list) : L.declaration list =
  let base : L.term = variable "base" int in
  let offset : L.term = variable "offset" int in
  let modulus : L.term = variable "modulus" int in
  let current : L.term = variable "value" int in
  let two : L.term = number "2" int in
  let step : L.term =
    match name with
    | "shl" -> L.Binary ("*", current, two)
    | "shr" -> native "Int.tdiv" [ current; two ]
    | _ -> L.Binary ("+", native "Int.tdiv" [ current; two ], modulus)
  in
  let arithmetic : bool = name = "shr_arith" in
  let binders : (string * L.type_ref) list =
    [ ("base", int); ("offset", int) ] @ if arithmetic then [ ("modulus", int) ] else []
  in
  let inputs : L.term list = [ base; offset ] @ if arithmetic then [ modulus ] else [] in
  let shifted : L.term =
    native "Nat.repeat" [ L.Lambda ("value", int, step); native "Int.toNat" [ offset ]; base ]
  in
  [ relation name [] relation_types
      [ rule name [] "shift" binders [ comparison L.Le offset bit_width_limit ]
          (inputs @ [ shifted ]) ] ]

(* pow2' w is 2^w, and 1 when w <= 0. *)
let power (width : L.term) : L.term =
  L.Binary ("^", number "2" int, native "Int.toNat" [ width ])

(* The OCaml loop adds 2^w to a negative n until it is not negative. *)
let int_to_bitstr (relation_types : L.type_ref list) : L.declaration list =
  let width : L.term = variable "width" int in
  let n : L.term = variable "value" int in
  [ relation "int_to_bitstr" [] relation_types
      [ rule "int_to_bitstr" [] "convert" [ ("width", int); ("value", int) ]
          [ comparison L.Le width bit_width_limit ]
          [ width; n; native "Int.emod" [ n; power width ] ] ] ]

(* The OCaml loop moves n by 2^w into [-2^w/2, 2^w/2). *)
let bitstr_to_int (relation_types : L.type_ref list) : L.declaration list =
  let width : L.term = variable "width" int in
  let n : L.term = variable "value" int in
  let half : L.term = native "Int.tdiv" [ power width; number "2" int ] in
  let centered : L.term =
    L.Binary ("-", native "Int.emod" [ L.Binary ("+", n, half); power width ], half)
  in
  [ relation "bitstr_to_int" [] relation_types
      [ rule "bitstr_to_int" [] "nonpositive" [ ("width", int); ("value", int) ]
          [ comparison L.Le width (number "0" int) ] [ width; n; number "0" int ];
        rule "bitstr_to_int" [] "positive" [ ("width", int); ("value", int) ]
          [ comparison L.Lt (number "0" int) width; comparison L.Le width bit_width_limit ]
          [ width; n; centered ] ] ]

let bits_to_int_signed (relation_types : L.type_ref list) : L.declaration list =
  let helper : string = "bits_to_int_signed:convert" in
  let head : L.term = variable "sign" bool in
  let tail : L.term = variable "tail" (list bool) in
  let result : L.term = variable "result" int in
  let input : L.term = cons head tail in
  let converted : L.term = L.Apply (application helper [] [ input ]) in
  [ builtin helper [ bits ] int
      "match arg0 with | [] => 0 | sign :: _ => let unsigned := arg0.foldl \
       (fun value bit => 2 * value + (if bit then 1 else 0)) (0 : Int); if \
       sign then unsigned - (2 : Int) ^ arg0.length else unsigned";
    relation "bits_to_int_signed" [] relation_types
      [ rule "bits_to_int_signed" [] "nonempty"
          [ ("sign", bool); ("tail", list bool); ("result", int) ]
          [ comparison L.Eq converted result ] [ input; result ] ] ]

(* Int.shiftRight exposes the same infinite two's-complement low bits as
   Bigint.land; the width guard also makes Bigint.to_int_exn total. *)
let int_to_bits (name : string) (relation_types : L.type_ref list) :
    L.declaration list =
  let width : L.term = variable "width" nat in
  let value : L.term = variable "value" int in
  let result : L.term = variable "result" bits in
  let index : L.term = variable "index" nat in
  let indices : L.term =
    native "List.reverse" [ native "List.range" [ width ] ]
  in
  let shifted : L.term = native "Int.shiftRight" [ value; index ] in
  let bit : L.term =
    L.Decide
      ([], L.Comparison (L.Eq,
              native "Int.emod" [ shifted; number "2" int ],
              number "1" int))
  in
  let converted : L.term =
    native "List.map" [ L.Lambda ("index", nat, bit); indices ]
  in
  [ relation name [] relation_types
      [ rule name [] "convert"
          [ ("width", nat); ("value", int); ("result", bits) ]
          [ comparison L.Le width (number "2048" nat);
            comparison L.Eq result converted ]
          [ width; value; result ] ] ]

(* Bigint.to_int_exn accepts exactly OCaml's nonnegative 63-bit int range. *)
let machine_int_max : L.term = number "4611686018427387903" int

let bitacc (relation_types : L.type_ref list) : L.declaration list =
  let helper : string = "bitacc:band" in
  let base : L.term = variable "base" int in
  let high : L.term = variable "high" int in
  let low : L.term = variable "low" int in
  let result : L.term = variable "result" int in
  let slice_width : L.term =
    L.Binary ("-", L.Binary ("+", high, number "1" int), low)
  in
  let shifted : L.term =
    native "Int.shiftRight" [ base; native "Int.toNat" [ low ] ]
  in
  let mask : L.term = L.Binary ("-", power slice_width, number "1" int) in
  let sliced : L.term = L.Apply (application helper [] [ shifted; mask ]) in
  [ builtin helper [ int; int ] int Builtin.band_body;
    relation "bitacc" [] relation_types
      [ rule "bitacc" [] "slice"
          [ ("base", int); ("high", int); ("low", int); ("result", int) ]
          [ comparison L.Le (number "0" int) low;
            comparison L.Le low machine_int_max;
            comparison L.Eq result sliced ]
          [ base; high; low; result ] ] ]

let bitacc_replace (relation_types : L.type_ref list) : L.declaration list =
  let band_helper : string = "bitacc_replace:band" in
  let xor_helper : string = "bitacc_replace:bxor" in
  let base : L.term = variable "base" int in
  let high : L.term = variable "high" int in
  let low : L.term = variable "low" int in
  let replacement : L.term = variable "replacement" int in
  let result : L.term = variable "result" int in
  let shifted_replacement : L.term =
    native "Int.shiftLeft" [ replacement; native "Int.toNat" [ low ] ]
  in
  let mask_high : L.term =
    L.Binary
      ("-", power (L.Binary ("+", high, number "1" int)), number "1" int)
  in
  let mask_low : L.term =
    L.Binary ("-", power low, number "1" int)
  in
  let mask_xor : L.term =
    L.Apply (application xor_helper [] [ mask_high; mask_low ])
  in
  let mask : L.term =
    L.Binary ("-", L.Unary ("-", mask_xor), number "1" int)
  in
  let preserved : L.term =
    L.Apply (application band_helper [] [ base; mask ])
  in
  let replaced : L.term =
    L.Apply
      (application xor_helper [] [ preserved; shifted_replacement ])
  in
  [ builtin band_helper [ int; int ] int Builtin.band_body;
    builtin xor_helper [ int; int ] int Builtin.bxor_body;
    relation "bitacc_replace" [] relation_types
      [ rule "bitacc_replace" [] "replace"
          [ ("base", int); ("high", int); ("low", int);
            ("replacement", int); ("result", int) ]
          [ comparison L.Le (number "0" int) low;
            comparison L.Le low machine_int_max;
            comparison L.Eq result replaced ]
          [ base; high; low; replacement; result ] ] ]

let text_to_int_parser : string =
  "let digit? (base : Nat) (c : Char) : Option Nat := \
   let code := c.toNat; \
   let value? := if '0'.toNat ≤ code ∧ code ≤ '9'.toNat then \
     some (code - '0'.toNat) else if 'a'.toNat ≤ code ∧ code ≤ 'f'.toNat \
     then some (code - 'a'.toNat + 10) else if 'A'.toNat ≤ code ∧ code ≤ \
     'F'.toNat then some (code - 'A'.toNat + 10) else none; \
   value?.bind (fun value => if value < base then some value else none); \
   let rec digits (base accumulator : Nat) (chars : List Char) : Option Nat := \
     match chars with | [] => some accumulator | '_' :: tail => digits base \
     accumulator tail | c :: tail => match digit? base c with | none => none | \
     some digit => digits base (accumulator * base + digit) tail; \
   let (negative, chars) := match arg0.toList with | '-' :: '+' :: tail => \
     (true, tail) | '-' :: tail => (true, tail) | '+' :: tail => (false, tail) \
     | chars => (false, chars); \
   let (base, chars) := match chars with | '0' :: 'x' :: tail | '0' :: 'X' \
     :: tail => (16, tail) | '0' :: 'o' :: tail | '0' :: 'O' :: tail => (8, \
     tail) | '0' :: 'b' :: tail | '0' :: 'B' :: tail => (2, tail) | chars \
     => (10, chars); \
   match chars with | '_' :: _ => none | _ => (digits base 0 chars).map \
     (fun value => if negative then -(Int.ofNat value) else Int.ofNat value)"

let text_to_int (relation_types : L.type_ref list) : L.declaration list =
  let helper : string = "text_to_int:parse" in
  let input : L.term = variable "input" text in
  let result : L.term = variable "result" int in
  let parsed : L.term = L.Apply (application helper [] [ input ]) in
  [ builtin helper [ text ] (option int) text_to_int_parser;
    relation "text_to_int" [] relation_types
      [ rule "text_to_int" [] "success"
          [ ("input", text); ("result", int) ]
          [ comparison L.Eq parsed (some result) ] [ input; result ] ] ]

(* P4.Unparse.pp_value returns text exactly when SpecTecPrint returns some text. *)
let print (relation_types : L.type_ref list) : L.declaration list =
  let value : L.term = variable "value" left in
  let result : L.term = variable "result" text in
  [ relation ~print_parameters:[ "X" ] "print_" [ "X" ] relation_types
      [ rule "print_" [ left ] "success"
          [ ("value", left); ("result", text) ]
          [ comparison L.Eq
              (native "SpecTecPrint.print?" [ value ])
              (some result) ]
          [ value; result ] ] ]

let translate (name : string) (type_parameters : string list)
    (constructor : constructor_lookup) : (L.declaration list, string) result =
  match signature name type_parameters with
  | Error reason -> Error reason
  | Ok (arguments, result) -> (
      let types : L.type_ref list = arguments @ [ result ] in
      match name with
      | "find_map" -> Ok (find_map types constructor)
      | "find_maps" -> Ok (find_maps types)
      | "add_map" | "update_map" -> Ok (add_map name types constructor)
      | "adds_map" -> Ok (adds_map types)
      | "assoc_" -> Ok (assoc types)
      | "distinct_" -> Ok (distinct types)
      | "sub_set" | "eq_set" -> Ok (set_comparison name types constructor)
      | "partition_" -> Ok (partition types)
      | "max_nat" -> Ok (extremum name types "Nat.max")
      | "min_nat" -> Ok (extremum name types "Nat.min")
      | "strip_prefix" | "strip_suffix" -> Ok (strip name types)
      | "split_text" -> Ok (split_text types)
      | "shl" | "shr" | "shr_arith" -> Ok (shift name types)
      | "int_to_bitstr" -> Ok (int_to_bitstr types)
      | "bitstr_to_int" -> Ok (bitstr_to_int types)
      | "bits_to_int_signed" -> Ok (bits_to_int_signed types)
      | "int_to_bits_unsigned" | "int_to_bits_signed" ->
          Ok (int_to_bits name types)
      | "bitacc" -> Ok (bitacc types)
      | "bitacc_replace" -> Ok (bitacc_replace types)
      | "text_to_int" -> Ok (text_to_int types)
      | "print_" -> Ok (print types)
      | "fresh_typeId" ->
          (* Fresh_state lowers this marker to the counter transition. *)
          Ok [ relation name [] types [] ]
      | _ -> Error (name ^ " because no relation builtin implementation is known"))

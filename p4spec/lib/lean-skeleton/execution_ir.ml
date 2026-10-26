(** Ordered calls keep source argument positions. Outputs are never query inputs. *)
module L = Ast.Lean

type signature = {
  name : string;
  parameters : string list;
  arguments : L.type_ref list;
  inputs : int list;
  external_ : bool;
}

let split signature = Lang.Hints.Input.split signature.inputs
let input_types signature = fst (split signature signature.arguments)
let output_types signature = snd (split signature signature.arguments)
let tuple_type = function
  | [] -> L.BuiltinType ("Unit", [])
  | [typ] -> typ
  | types -> L.TupleType types
let tuple_term = function
  | [] -> L.Native ("Unit.unit", [])
  | terms -> Translator.nest_pairs (fun a b -> L.Tuple (a, b)) terms

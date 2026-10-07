open Lang
open Il
module Value = Runtime.Value
open Util.Source

(* dec $fresh_typeId() : typeId *)

(* Observation only: the interpreter's counter and returned values are unchanged.
   Keep allocation identities so ordinary text with the same spelling is not
   accidentally classified as a generated identifier. *)
let allocation_observer : (Value.t -> unit) option ref = ref None

let with_allocations run =
  let previous = !allocation_observer in
  let allocated = ref [] in
  allocation_observer := Some (fun value ->
    allocated := value :: !allocated;
    Option.iter (fun observe -> observe value) previous);
  let result = Fun.protect
    ~finally:(fun () -> allocation_observer := previous) run in
  result, List.rev !allocated

let fresh_typeId (ctr : int ref) (add : value -> unit) (at : region)
    (targs : targ list) (values_input : value list) : value =
  Extract.zero at targs;
  Extract.zero at values_input;
  let tid = "FRESH__" ^ string_of_int !ctr in
  ctr := !ctr + 1;
  let value = Value.Make.text tid in
  add value;
  Option.iter (fun observe -> observe value) !allocation_observer;
  value

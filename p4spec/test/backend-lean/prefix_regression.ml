module Run = Runtime.Sim.Signature
module Value = Runtime.Value
module Typ = Runtime.Type.Typ

let unwrap = function
  | Ok value -> value
  | Error error -> failwith (P4spectec.Error.to_string error)

let () =
  let spec = unwrap (P4spectec.structure ~final:true [ Sys.argv.(1) ]) in
  List.iter (fun det ->
    let (module Simulator : Run.SIM) = unwrap (P4spectec.build_sim ~det (Run.SL spec)) in
    let nat n = Value.Make.nat (Bigint.of_int n) in
    let values ns = Value.Make.list Typ.Make.nat (List.map nat ns) in
    let check label name arguments =
      Interface.P4.Builtin_P4.init ();
      Simulator.Interp.clear ();
      match Simulator.Interp.eval_func name [Typ.Make.nat] arguments with
      | Run.Pass value ->
          Printf.printf "%s%s=%s\n" (if det then "det_" else "") label (Value.Get.text value)
      | Run.Fail failure ->
          failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure)))
    in
    check "prefix_success" "guarded_prefix" [nat 16; values [7]];
    check "prefix_failure" "guarded_prefix" [nat 12; values [7]];
    check "pattern_failure" "guarded_prefix" [nat 12; values []];
    check "late_pattern" "late_pattern" [values []]) [false; true]

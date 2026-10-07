module Run = Runtime.Sim.Signature
module Value = Runtime.Value

let unwrap = function
  | Ok value -> value
  | Error error -> failwith (P4spectec.Error.to_string error)

let () =
  let spec = unwrap (P4spectec.structure ~final:true [ Sys.argv.(1) ]) in
  let simulator = unwrap (P4spectec.build_sim ~det:false (Run.SL spec)) in
  let (module Simulator : Run.SIM) = simulator in
  let call name args =
    Interface.P4.Builtin_P4.init ();
    Simulator.Interp.clear ();
    match Simulator.Interp.eval_func name [] args with
    | Run.Pass value -> value
    | Run.Fail failure ->
        failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure)))
  in
  let text value = Value.Get.text value in
  let texts values = String.concat "," (List.map text values) in
  Printf.printf "once=%s\n" (text (call "once" []));
  Printf.printf "twice=%s\n" (texts (Value.Get.tuple (call "twice" [])));
  Printf.printf "twice_via_function=%s\n"
    (texts (Value.Get.tuple (call "twice_via_function" [])));
  Printf.printf "ids2=%s\n"
    (texts (Value.Get.list
      (call "fresh_typeIds" [ Value.Make.nat (Bigint.of_int 2) ])));
  Printf.printf "after_failed=%s\n" (text (call "after_failed" []));
  Printf.printf "after_rule_failure=%s\n"
    (text (call "after_rule_failure" []));
  Printf.printf "after_output_failure=%s\n"
    (text (call "after_output_failure" []));
  Printf.printf "new_program=%s\n" (text (call "once" []));
  let deterministic = unwrap (P4spectec.build_sim ~det:true (Run.SL spec)) in
  let (module Deterministic : Run.SIM) = deterministic in
  let call_deterministic name args =
    Interface.P4.Builtin_P4.init ();
    Deterministic.Interp.clear ();
    match Deterministic.Interp.eval_func name [] args with
    | Run.Pass value -> value
    | Run.Fail failure ->
        failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure)))
  in
  Printf.printf "det_ids2=%s\n"
    (texts (Value.Get.list
      (call_deterministic "fresh_typeIds"
        [ Value.Make.nat (Bigint.of_int 2) ])));
  Printf.printf "det_after_failed=%s\n"
    (text (call_deterministic "after_failed" []));
  Printf.printf "det_after_rule_failure=%s\n"
    (text (call_deterministic "after_rule_failure" []));
  Printf.printf "det_after_output_failure=%s\n"
    (text (call_deterministic "after_output_failure" []))

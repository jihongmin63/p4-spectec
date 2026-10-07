module Run = Runtime.Sim.Signature
module Value = Runtime.Value

let unwrap = function
  | Ok value -> value
  | Error error -> failwith (P4spectec.Error.to_string error)

let outcome = function
  | Run.Pass value -> value
  | Run.Fail failure ->
      failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure)))

let () =
  let spec = unwrap (P4spectec.structure ~final:true [ Sys.argv.(1) ]) in
  List.iter (fun det ->
    let simulator = unwrap (P4spectec.build_sim ~det (Run.SL spec)) in
    let (module Simulator : Run.SIM) = simulator in
    let reset () =
      Interface.P4.Builtin_P4.init ();
      Simulator.Interp.clear ()
    in
    let print name values =
      Printf.printf "%s%s=%s\n" (if det then "det_" else "") name
        (String.concat "," (List.map Value.Get.text values))
    in
    let func label name args =
      reset ();
      print label [outcome (Simulator.Interp.eval_func name [] args)]
    in
    let nat n = Value.Make.nat (Bigint.of_int n) in
    func "otherwise_zero" "otherwise_plain" [nat 0];
    func "otherwise_nonzero" "otherwise_plain" [nat 1];
    func "otherwise_effectful" "otherwise_effectful" [];
    func "otherwise_unvisited" "otherwise_unvisited" [];
    func "pattern_empty" "pattern" [Value.Make.list Runtime.Type.Typ.Make.text []];
    func "pattern_nonempty" "pattern" [Value.Make.list Runtime.Type.Typ.Make.text [Value.Make.text "x"]];
    func "pattern_after_fresh" "pattern_after_fresh" [];
    func "after_three" "after_three" [];
    func "after_all_failed" "after_all_failed" [];
    func "diagonal_same" "diagonal" [nat 1; nat 1];
    func "diagonal_different" "diagonal" [nat 0; nat 1];
    List.iter (fun name ->
      reset ();
      print name (outcome (Simulator.Interp.eval_rel name [nat 7])))
      ["Ordered"; "Guarded"];
    List.iter (fun n ->
      reset ();
      print ("Grouped" ^ string_of_int n)
        (outcome (Simulator.Interp.eval_rel "Grouped" [nat n]))) [0; 7])
    [false; true]

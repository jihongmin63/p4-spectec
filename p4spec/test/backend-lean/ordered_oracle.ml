(** Differential oracle: both existing interpreters use sequential selection. *)
module Run = Runtime.Dynamic_Runner.Signature
module Value = Runtime.Value
module Typ = Runtime.Type.Typ
open Util.Source

module Extern : Run.EXTERN = struct
  module Cache = struct let cache_on () = () let cache_off () = () end
  let checkpoint () = 0
  let seff _ _ = false
  let clear () = ()
  let init_mode _ = Ok ()
  let eval_extern_rel _ _ = Run.Fail (Run.abort ~source:"oracle" no_region "unexpected extern")
  let eval_extern_func _ _ _ = Run.Fail (Run.abort ~source:"oracle" no_region "unexpected extern")
end
let interpreters = ref None
let al_rel name inputs = let a, _, _, _ = Option.get !interpreters in a name inputs
let sl_rel name inputs = let _, s, _, _ = Option.get !interpreters in s name inputs
let al_func name types inputs = let _, _, a, _ = Option.get !interpreters in a name types inputs
let sl_func name types inputs = let _, _, _, s = Option.get !interpreters in s name types inputs

let unwrap = function Ok x -> x | Error d -> failwith (snd (Diagnostic.region_msg d))
let natural n = Value.Make.nat (Bigint.of_int n)
let number v = v |> Value.Get.num |> Lang.Xl.Num.to_int |> Bigint.to_string
let tag v = v |> Value.Get.case |> Domain.Mixfix.atoms
  |> List.map (fun a -> Domain.Atom.string_of_atom a.it) |> String.concat " "

let initialize paths =
  let module AL = Interp.Interp_Al.Interp.Make (Interface.SpecTec_AL) (Extern) () in
  let module SL = Interp.Interp_Sl.Interp.Make (Interface.SpecTec_SL) (Extern) () in
  let il = unwrap (Pass.elab paths) in
  let al = unwrap (Pass.algo_spec il) in
  let sl = unwrap (Pass.struct_spec ~final:true al) in
  unwrap (AL.init ~cache:false ~det:false ~guard:true al);
  unwrap (SL.init ~cache:false ~det:false ~guard:true sl);
  interpreters := Some (AL.eval_rel, SL.eval_rel, AL.eval_func, SL.eval_func)

let relation name inputs expected =
  List.iter (fun (label, evaluate) ->
    match evaluate name inputs with
    | Run.Pass [output] ->
        let actual = number output in
        if actual <> expected then failwith (label ^ ": " ^ name ^ " expected " ^ expected ^ ", got " ^ actual)
    | Run.Pass _ -> failwith "wrong output arity"
    | Run.Fail failure -> failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure))))
    ["AL", al_rel; "SL", sl_rel]

let () =
  let fresh_results = Array.length Sys.argv = 4 && Sys.argv.(3) = "--fresh-results" in
  initialize [Sys.argv.(1)];
  relation "Choose" [natural 7] "1";
  relation "Caller" [natural 7] "30";
  relation "Guarded" [natural 0] "10";
  relation "Guarded" [natural 1] "11";
  relation "Copy" [natural 7] "7";
  initialize [Sys.argv.(2)];
  let function_ name inputs expected =
    List.iter (fun evaluate -> match evaluate name [] inputs with
      | Run.Pass output when number output = expected -> ()
      | Run.Pass _ -> failwith ("unexpected result: " ^ name)
      | Run.Fail failure -> failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure failure))))
      [al_func; sl_func] in
  function_ "choose" [natural 7] "1";
  function_ "before_output" [natural 7] "1";
  function_ "left" [natural 3] "0";
  function_ "max_or_default" [Value.Make.list Typ.Make.nat []] "99";
  List.iter (fun evaluate ->
    try ignore (evaluate "parse_or_default" [] [Value.Make.text "bad"]);
        failwith "expected text_to_int host exception"
    with Failure message when String.starts_with ~prefix:"of_string.Bigint" message -> ())
    [al_func; sl_func];
  List.iter (fun evaluate ->
    let red = Value.Make.("RED" <| [] <<| "color") in
    match evaluate "table_fallback" [] [red] with
    | Run.Pass output when Value.Get.bool output = false -> ()
    | _ -> failwith "table output failure did not reach wildcard row") [al_func; sl_func];
  initialize [Filename.concat (Filename.dirname Sys.argv.(2)) "ordered-errors.watsup"];
  List.iter (fun evaluate ->
    List.iter (fun (name, inputs) ->
      match evaluate name [] inputs with
      (* The public entry point collapses AL Err and Unmatch into Run.Unmatch.
         With an unconditional successful fallback, any failure still proves
         that the internal Err stopped clause choice. *)
      | Run.Fail _ -> ()
      | _ -> failwith (name ^ ": runtime error incorrectly permitted fallback"))
      ["slice_text", [Value.Make.text "a"; natural 0; natural 2];
       "update_text", [Value.Make.text "a"; natural 0; Value.Make.text "xx"];
       "update_text", [Value.Make.text "a"; natural 1; Value.Make.text "x"];
       "slice_list", [Value.Make.list Typ.Make.nat [natural 1]; natural 0; natural 2];
       "update_list", [Value.Make.list Typ.Make.nat [natural 1]; natural 1; natural 3]];
    (try
       match evaluate "divide_nat" [] [natural 1; natural 0] with
       | Run.Fail _ -> ()
       | Run.Pass _ -> failwith "division by zero incorrectly permitted fallback"
     with Assert_failure (file, _, _) when Filename.basename file = "num.ml" -> ());
    (match evaluate "index_text" [] [Value.Make.text "é"; natural 0] with
     | Run.Pass output when Value.Get.text output = String.sub "é" 0 1 -> ()
     | _ -> failwith "the source's in-bounds byte extraction did not succeed");
    (match evaluate "index_text" [] [Value.Make.text "a"; natural 1] with
     | Run.Pass output when Value.Get.text output = "fallback" -> ()
     | _ -> failwith "AL indexing guard did not permit fallback")) [al_func; sl_func];
  initialize [Filename.concat (Filename.dirname Sys.argv.(2)) "ordered-downcast.watsup"];
  let integer n = Value.Make.int (Bigint.of_int n) in
  List.iter (fun (name, input, expected) -> relation name [input] expected)
    ["TupleDog", natural 0, "5"; "TupleDog", natural 1, "0";
     "TripleDogs", natural 0, "6"; "TripleDogs", natural 1, "0";
     "ListDogs", natural 0, "2"; "ListDogs", natural 1, "0";
     "SingleDog", natural 0, "7"; "SingleDog", natural 1, "0"; "SingleDog", natural 2, "0";
     "OptionDog", natural 0, "3"; "OptionDog", natural 1, "4"; "OptionDog", natural 2, "0";
     "NatPair", integer 2, "3"; "NatPair", integer (-2), "0";
     "PairDogs", natural 0, "2"; "PairDogs", natural 1, "0"];
  initialize [Filename.concat (Filename.dirname Sys.argv.(2)) "ordered-fresh.watsup"];
  List.iter (fun (label, reset, checkpoint, eval_rel, eval_func) ->
    let check expected final values =
      let actual = List.map Value.Get.text values in
      if actual <> expected then failwith (label ^ ": incorrect fresh names");
      if checkpoint () <> final then failwith (label ^ ": incorrect consumed supply") in
    List.iter (fun (name, expected, final) ->
      reset ();
      match eval_rel name [natural 7] with
      | Run.Pass outputs ->
          check expected final outputs;
          if fresh_results then
            Printf.printf "fresh\t%s\t%s\t%s\t%d\n" label name
              (String.concat "," (List.map Value.Get.text outputs)) (checkpoint ())
      | Run.Fail f -> failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure f))))
      ["FreshOne", ["FRESH__0"], 1;
       "FreshPair", ["FRESH__0"; "FRESH__1"], 2;
       "FreshMismatch", ["FRESH__1"], 2;
       "FailedCaller", ["FRESH__1"], 2;
       "NegatedFailure", ["FRESH__1"], 2;
       "NegatedSuccess", ["FRESH__1"], 2];
    List.iter (fun (name, inputs, extract, expected, final) ->
      reset ();
      match eval_func name [] inputs with
      | Run.Pass output -> check expected final (extract output)
      | Run.Fail f -> failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure f))))
      ["pair", [], Value.Get.tuple, ["FRESH__0"; "FRESH__1"], 2;
       "callback_pair", [], Value.Get.tuple, ["FRESH__0"; "FRESH__1"], 2;
       "fresh_typeIds", [natural 0], Value.Get.list, [], 0;
       "fresh_typeIds", [natural 3], Value.Get.list,
         ["FRESH__0"; "FRESH__1"; "FRESH__2"], 3;
       "many", [Value.Make.list Typ.Make.nat [natural 4; natural 4; natural 4]],
         Value.Get.list, ["FRESH__0"; "FRESH__1"; "FRESH__2"], 3;
       "debug_fresh", [], (fun v -> [v]), ["FRESH__1"], 2;
       "debug_iter", [Value.Make.list Typ.Make.nat [natural 7; natural 7]],
         (fun v -> [v]), ["FRESH__2"], 3;
       "debug_failure", [], (fun v -> [v]), ["FRESH__1"], 2];
    List.iter (fun name ->
      reset ();
      (try ignore (eval_func name [] []);
           failwith "expected text_to_int host exception after fresh"
       with Failure message when String.starts_with ~prefix:"of_string.Bigint" message -> ());
      if checkpoint () <> 1 then failwith (label ^ ": abort lost consumed fresh supply"))
      ["fresh_then_abort"; "debug_abort"];
    match eval_func "one" [] [natural 7] with
    | Run.Pass output -> check ["FRESH__1"] 2 [output]
    | _ -> failwith (label ^ ": allocation after abort failed"))
    ["AL", Interface.SpecTec_AL.Builtin_SpecTec.init, Interface.SpecTec_AL.checkpoint,
       al_rel, al_func;
     "SL", Interface.SpecTec_SL.Builtin_SpecTec.init, Interface.SpecTec_SL.checkpoint,
       sl_rel, sl_func];
  if Array.length Sys.argv > 3 && not fresh_results then (
    initialize [Sys.argv.(3)];
    let case mixop arguments = Value.Make.(mixop <| arguments <<| "typeIR") in
    List.iter (fun evaluate ->
      List.iter (fun (right, expected) ->
        match evaluate "Cast_expl_neq" [case "BOOL" []; right] with
        | Run.Pass [output] when tag output = expected -> ()
        | Run.Pass [output] -> failwith ("Cast_expl_neq: " ^ tag output)
        | Run.Pass _ -> failwith "cast output arity"
        | Run.Fail f -> failwith (snd (Diagnostic.region_msg (Run.diagnostic_of_failure f))))
        [case "BIT `< w `>" [natural 1], "OK"; case "STRING" [], "FAIL"])
      [al_rel; sl_rel]);
  if Array.length Sys.argv > 4 then (
    let paths = [Sys.argv.(3)] in
    let spec = match P4spectec.spec_of_mode Run.SL_mode paths with
      | Ok s -> s | Error _ -> failwith "P4 spec initialization failed" in
    let evaluate det =
      let simulator = match P4spectec.build_sim ~det spec with
        | Ok s -> s | Error _ -> failwith "P4 simulator initialization failed" in
      let module Simulator = (val simulator : Runtime.Sim.Signature.SIM) in
      Interface.P4.Builtin_P4.init ();
      Simulator.Interp.clear ();
      Simulator.Interp.eval_program "Program_ok" [Sys.argv.(5)] Sys.argv.(4) in
    match evaluate true, evaluate false with
    | Run.Pass old, Run.Pass ordered when List.for_all2 Value.eq old ordered -> ()
    | Run.Fail (`Runtime (Run.Unmatch _)), Run.Fail (`Runtime (Run.Unmatch _)) -> ()
    | _ -> failwith "P4 sequential outcome differs from deterministic execution");
  print_endline "Ordered AL/SL oracle comparisons passed"

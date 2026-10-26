open Lang
open Il

(* Entry point *)

type error = Diagnostic.t

let algo_spec (spec : spec) : (Al.spec, error) result =
  try
    Ok (spec |> Binding.Analyze.analyze_spec |> Sidecondition.Guard.insert_spec)
  with Error.AlgoError d -> Error d

(* Preserve independent definitions when one directional conversion fails. *)
let algo_defs (spec : spec) : (Al.def, error) result list =
  let ctx = Binding.Ctx.(load_spec (init ()) spec) in
  List.map (fun def ->
    try Ok (Binding.Analyze.analyze_def ctx def |> Sidecondition.Guard.insert_def)
    with Error.AlgoError d -> Error d) spec

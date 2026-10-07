module Value = Runtime.Value

let () =
  let counter = ref 0 in
  let allocate () =
    Builtin.Fresh.fresh_typeId counter ignore Util.Source.no_region [] [] in
  let (first, nested), outer = Builtin.Fresh.with_allocations (fun () ->
    let first = allocate () in
    let _, nested = Builtin.Fresh.with_allocations (fun () -> allocate ()) in
    (try
      ignore (Builtin.Fresh.with_allocations (fun () ->
        ignore (allocate ()); failwith "expected"))
    with Failure message when message = "expected" -> ());
    ignore (allocate ());
    first, nested) in
  assert (!counter = 4);
  assert (List.map Value.Get.text outer =
    ["FRESH__0"; "FRESH__1"; "FRESH__2"; "FRESH__3"]);
  assert (List.map Value.Get.text nested = ["FRESH__1"]);
  let ordinary = Value.Make.text "FRESH__0" in
  assert (first.note.vid <> ordinary.note.vid);
  ignore (allocate ());
  let _, isolated = Builtin.Fresh.with_allocations (fun () -> allocate ()) in
  assert (List.map Value.Get.text isolated = ["FRESH__5"]);
  assert (!counter = 6);
  print_endline "fresh trace: identity, nested scopes, exception restoration and unchanged counter"

(** Selection and oracle I/O, independent of Lean rendering and execution. *)
type expectation = Accept | Reject | AbortReject
type entry = expectation * string * string option

let label = function Accept -> "accept" | Reject -> "reject" | AbortReject -> "abort-reject"
let goal_kind = function
  | Accept -> "accepted-exact"
  | Reject -> "no-success"
  | AbortReject -> "rejection-conjecture"

let read path =
  try
    let channel = open_in path in
    Fun.protect ~finally:(fun () -> close_in channel) (fun () ->
      let relative name = if Filename.is_relative name then
          Filename.concat (Filename.dirname path) name else name in
      let rec loop line_number entries =
        match input_line channel with
        | line ->
            let line = String.trim line in
            if line = "" || String.starts_with ~prefix:"#" line then
              loop (line_number + 1) entries
            else
              let entry = match String.split_on_char '\t' line with
                | ["accept"; source; oracle] when source <> "" && oracle <> "" ->
                    Some (Accept, relative source, Some (relative oracle))
                | ["reject"; source] when source <> "" -> Some (Reject, relative source, None)
                | ["abort-reject"; source] when source <> "" -> Some (AbortReject, relative source, None)
                | _ -> None in
              (match entry with
              | Some entry -> loop (line_number + 1) (entry :: entries)
              | None -> Error (Printf.sprintf
                  "%s:%d: expected accept<TAB>path<TAB>expected, reject<TAB>path, or abort-reject<TAB>path"
                  path line_number))
        | exception End_of_file -> Ok (List.rev entries) in
      loop 1 [])
  with Sys_error message -> Error message

let select range entries =
  let indexed = List.mapi (fun index entry -> index, entry) entries in
  match range with
  | None -> indexed
  | Some (start, count) -> List.filter (fun (index, _) -> index >= start && index - start < count) indexed

let read_expected path =
  try
    let compressed = Filename.check_suffix path ".gz" in
    let channel = if compressed then
        Unix.open_process_args_in "gzip" [|"gzip"; "-dc"; "--"; path|]
      else open_in_bin path in
    let close () = if compressed then Unix.close_process_in channel
      else (close_in channel; Unix.WEXITED 0) in
    let contents, status =
      try
        let buffer = Buffer.create 4096 in
        let bytes = Bytes.create 65536 in
        let rec loop () =
          let count = input channel bytes 0 (Bytes.length bytes) in
          if count > 0 then (Buffer.add_subbytes buffer bytes 0 count; loop ()) in
        loop ();
        Buffer.contents buffer |> String.trim, close ()
      with exn -> ignore (close ()); raise exn in
    match status with
    | Unix.WEXITED 0 when contents <> "" -> Ok contents
    | Unix.WEXITED 0 -> Error ("empty expected output: " ^ path)
    | _ -> Error ("cannot decompress expected output: " ^ path)
  with
  | Sys_error message -> Error message
  | Unix.Unix_error (error, _, _) -> Error (Unix.error_message error)

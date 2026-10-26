module Call = Builtin.Call.Make (Builtin.Call.No_ext) ()
module Typ = Runtime.Type.Typ
module Value = Runtime.Value
open Lang
open Il
open Util.Source

let bigint (value : int) : Bigint.t = Bigint.of_int value

let invoke (name : string) (targs : typ list) (arguments : value list) : value =
  Call.invoke ignore (name $ no_region) targs arguments

let show (label : string) (render : value -> string) (call : unit -> value) : unit =
  try Printf.printf "%s=%s\n" label (render (call ()))
  with _ -> Printf.printf "%s=<failure>\n" label

let render_num (value : value) : string =
  value |> Value.Get.num |> Lang.Xl.Num.to_int |> Bigint.to_string

let render_bool (value : value) : string =
  value |> Value.Get.bool |> string_of_bool

let render_text (value : value) : string =
  value |> Value.Get.text |> Printf.sprintf "%S"

let render_texts (value : value) : string =
  value |> Value.Get.list |> List.map Value.Get.text
  |> List.map (Printf.sprintf "%S") |> String.concat ";"
  |> Printf.sprintf "[%s]"

let render_text_set (value : value) : string =
  match value |> Value.Get.case |> Domain.Mixfix.args with
  | [ elements ] -> render_texts elements
  | _ -> assert false

let render_bits (value : value) : string =
  value |> Value.Get.list |> List.map Value.Get.bool
  |> List.map (fun bit -> if bit then "1" else "0") |> String.concat ""

let number (value : int) : value = Value.Make.int (bigint value)
let natural (value : int) : value = Value.Make.nat (bigint value)

let bits (values : bool list) : value =
  Value.Make.list Typ.Make.bool (List.map Value.Make.bool values)

let case (mixop : string) (arguments : value list) (typ : string) : value =
  Value.Make.(mixop <| arguments <<| typ)

let set (values : value list) : value =
  let elements : value = Value.Make.list Typ.Make.int values in
  case "`{ k `}" [ elements ] "set"

let text_set (values : string list) : value =
  let elements : value =
    values |> List.map Value.Make.text |> Value.Make.list Typ.Make.text
  in
  case "`{ k `}" [ elements ] "set"

let text_sets (values : value list) : value =
  let set_type : typ = Typ.Make.var ("set" $ no_region) [ Typ.Make.text ] in
  Value.Make.list set_type values

let text_to_int (text : string) : unit -> value =
  fun () -> invoke "text_to_int" [] [ Value.Make.text text ]

let () =
  show "split_fields" render_texts (fun () ->
      invoke "split_text" [] [ Value.Make.text "a,,b,"; Value.Make.text "," ]);
  show "split_empty" render_texts (fun () ->
      invoke "split_text" [] [ Value.Make.text ""; Value.Make.text "," ]);
  show "split_empty_separator" render_texts (fun () ->
      invoke "split_text" [] [ Value.Make.text "abc"; Value.Make.text "" ]);
  show "split_multibyte_separator" render_texts (fun () ->
      invoke "split_text" [] [ Value.Make.text "aéb"; Value.Make.text "é" ]);

  show "sub_set_duplicate_true" render_bool (fun () ->
      invoke "sub_set" [ Typ.Make.int ]
        [ set [ number 1; number 1 ]; set [ number 2; number 1 ] ]);
  show "sub_set_false" render_bool (fun () ->
      invoke "sub_set" [ Typ.Make.int ]
        [ set [ number 1; number 3 ]; set [ number 1; number 2 ] ]);
  show "eq_set_reordered_true" render_bool (fun () ->
      invoke "eq_set" [ Typ.Make.int ]
        [ set [ number 1; number 1; number 2 ]; set [ number 2; number 1 ] ]);
  show "eq_set_false" render_bool (fun () ->
      invoke "eq_set" [ Typ.Make.int ] [ set [ number 1 ]; set [ number 2 ] ]);

  let text_left : value = text_set [ "b"; "a"; "a"; "Z"; "é"; "" ] in
  let text_right : value =
    text_set [ "z"; "ab"; "b"; "FRESH__2"; "FRESH__10"; "a" ]
  in
  show "union_set_text_unsorted_duplicates" render_text_set (fun () ->
      invoke "union_set" [ Typ.Make.text ] [ text_left; text_right ]);
  show "union_set_text_empty" render_text_set (fun () ->
      invoke "union_set" [ Typ.Make.text ] [ text_left; text_set [] ]);
  show "unions_set_text_empty" render_text_set (fun () ->
      invoke "unions_set" [ Typ.Make.text ] [ text_sets [] ]);
  show "unions_set_text_three" render_text_set (fun () ->
      invoke "unions_set" [ Typ.Make.text ]
        [ text_sets
            [ text_set [ "b"; "FRESH__2"; "" ];
              text_set [ "a"; "Z"; "FRESH__10" ];
              text_set [ "é"; "z"; "ab"; "b" ] ] ]);
  show "diff_set_text" render_text_set (fun () ->
      invoke "diff_set" [ Typ.Make.text ]
        [ text_left; text_set [ "b"; "Z"; "x"; "b" ] ]);
  show "intersect_set_text" render_text_set (fun () ->
      invoke "intersect_set" [ Typ.Make.text ]
        [ text_left; text_set [ "b"; "Z"; "x"; "b" ] ]);
  show "intersect_set_text_empty" render_text_set (fun () ->
      invoke "intersect_set" [ Typ.Make.text ] [ text_left; text_set [] ]);

  show "int_to_text_int_positive" render_text (fun () ->
      invoke "int_to_text" [] [ number 7 ]);
  show "int_to_text_int_negative" render_text (fun () ->
      invoke "int_to_text" [] [ number (-7) ]);
  show "int_to_text_nat_positive" render_text (fun () ->
      invoke "int_to_text" [] [ natural 7 ]);

  show "bits_to_int_signed_negative" render_num (fun () ->
      invoke "bits_to_int_signed" [] [ bits [ true; false; false; false ] ]);
  show "bits_to_int_signed_positive" render_num (fun () ->
      invoke "bits_to_int_signed" [] [ bits [ false; true; false ] ]);
  show "bits_to_int_signed_empty" render_num (fun () ->
      invoke "bits_to_int_signed" [] [ bits [] ]);

  show "int_to_bits_unsigned_wrap" render_bits (fun () ->
      invoke "int_to_bits_unsigned" [] [ natural 4; number 18 ]);
  show "int_to_bits_unsigned_negative" render_bits (fun () ->
      invoke "int_to_bits_unsigned" [] [ natural 4; number (-1) ]);
  show "int_to_bits_unsigned_zero" render_bits (fun () ->
      invoke "int_to_bits_unsigned" [] [ natural 0; number 7 ]);
  show "int_to_bits_unsigned_too_wide" render_bits (fun () ->
      invoke "int_to_bits_unsigned" [] [ natural 2049; number 0 ]);

  show "int_to_bits_signed_negative" render_bits (fun () ->
      invoke "int_to_bits_signed" [] [ natural 4; number (-3) ]);
  show "int_to_bits_signed_positive_wrap" render_bits (fun () ->
      invoke "int_to_bits_signed" [] [ natural 4; number 13 ]);
  show "int_to_bits_signed_zero" render_bits (fun () ->
      invoke "int_to_bits_signed" [] [ natural 0; number 7 ]);
  show "int_to_bits_signed_too_wide" render_bits (fun () ->
      invoke "int_to_bits_signed" [] [ natural 2049; number 0 ]);

  List.iter
    (fun (label, base, high, low) ->
      show label render_num (fun () ->
          invoke "bitacc" [] [ number base; number high; number low ]))
    [ "bitacc_normal", 53, 4, 2; "bitacc_negative_base", -1, 3, 1;
      "bitacc_negative_odd", -3, 2, 1;
      "bitacc_zero_width", 15, 0, 1;
      "bitacc_negative_width", 15, -1, 1;
      "bitacc_negative_low", 15, 2, -1 ];
  show "bitacc_huge_low" render_num (fun () ->
      invoke "bitacc" []
        [ number 15; number 2;
          Value.Make.int Bigint.(one lsl 62) ]);

  List.iter
    (fun (label, base, high, low, replacement) ->
      show label render_num (fun () ->
          invoke "bitacc_replace" []
            [ number base; number high; number low; number replacement ]))
    [ "bitacc_replace_normal", 15, 3, 1, 7;
      "bitacc_replace_reversed", 15, 0, 1, 7;
      "bitacc_replace_negative_high", 15, -1, 0, 7;
      "bitacc_replace_unmasked", 0, 3, 1, 255;
      "bitacc_replace_xor", 16, 3, 1, 15;
      "bitacc_replace_negative_base", -1, 3, 1, 0;
      "bitacc_replace_negative_replacement", 0, 3, 1, -1;
      "bitacc_replace_negative_low", 0, 3, -1, 1 ];
  show "bitacc_replace_huge_low" render_num (fun () ->
      invoke "bitacc_replace" []
        [ number 0; number 3;
          Value.Make.int Bigint.(one lsl 62); number 1 ]);

  List.iter
    (fun (label, text) -> show label render_num (text_to_int text))
    [ "text_empty", ""; "text_plus", "+"; "text_minus", "-";
      "text_hex_empty", "0x"; "text_binary_empty", "0b";
      "text_octal_empty", "0o"; "text_plus_decimal", "+12";
      "text_minus_plus_decimal", "-+12"; "text_minus_plus_empty", "-+";
      "text_plus_minus_invalid", "+-12";
      "text_upper_hex", "0XFa"; "text_binary", "0b101";
      "text_octal", "0o17"; "text_underscores", "1__000_";
      "text_negative_hex", "-0x10"; "text_leading_underscore", "_1";
      "text_prefix_underscore", "0x_F"; "text_bad_binary", "0b102";
      "text_bad_octal", "0o78"; "text_bad_hex", "0xfG";
      "text_only_underscore", "_"; "text_empty_hex_underscore", "0x_";
      "text_decimal_letter", "1a"; "text_leading_space", " 1";
      "text_trailing_space", "1 " ]

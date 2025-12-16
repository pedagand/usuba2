module Value = Ua0.Value.Make (Ua0.Value.Bool)

(* Generators *)

let value2 (a, b) = Value.Array [| a; b |]
let value4 (a, b, c, d) = Value.Array [| a; b; c; d |]
let qvalue_bool = QCheck.(map (fun v -> Value.Bool v) bool)

let qvalue4 =
  QCheck.(tup4 qvalue_bool qvalue_bool qvalue_bool qvalue_bool |> map value4)

let qvalue_4x4 = QCheck.(tup4 qvalue4 qvalue4 qvalue4 qvalue4 |> map value4)

let qvalue_4x4x4 =
  QCheck.(tup4 qvalue_4x4 qvalue_4x4 qvalue_4x4 qvalue_4x4 |> map value4)

let qvalue_2 = QCheck.(tup2 qvalue_bool qvalue_bool |> map value2)
let qvalue_4x2 = QCheck.(tup4 qvalue_2 qvalue_2 qvalue_2 qvalue_2 |> map value4)

let qvalue_4x4x2 =
  QCheck.(tup4 qvalue_4x2 qvalue_4x2 qvalue_4x2 qvalue_4x2 |> map value4)

let qvalue_4x4x4x2 =
  QCheck.(
    tup4 qvalue_4x4x2 qvalue_4x4x2 qvalue_4x4x2 qvalue_4x4x2 |> map value4)

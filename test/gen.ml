module Value = Ua0.Value

(* Generators *)

let value2 (a, b) = Value.VArray [| a; b |]
let value4 (a, b, c, d) = Value.VArray [| a; b; c; d |]
let qvalue_bool = QCheck.(bool |> map (fun v -> Value.VBool v))

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

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

let qvalue_4x4x4x7x4_raw =
  QCheck.(
    tup7
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4)
      (tup4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4 qvalue_4x4x4))

let qvalue_4x4x4x7x4 =
  QCheck.(
    map
      (fun ( (k1, k2, k3, k4),
             (k5, k6, k7, k8),
             (k9, k10, k11, k12),
             (k13, k14, k15, k16),
             (k17, k18, k19, k20),
             (k21, k22, k23, k24),
             (k25, k26, k27, k28) ) ->
        Value.Array
          [|
            Value.Array [| k1; k2; k3; k4 |];
            Value.Array [| k5; k6; k7; k8 |];
            Value.Array [| k9; k10; k11; k12 |];
            Value.Array [| k13; k14; k15; k16 |];
            Value.Array [| k17; k18; k19; k20 |];
            Value.Array [| k21; k22; k23; k24 |];
            Value.Array [| k25; k26; k27; k28 |];
          |])
      qvalue_4x4x4x7x4_raw)

let qvalue_4x4x4x28 =
  QCheck.(
    map
      (fun ( (k1, k2, k3, k4),
             (k5, k6, k7, k8),
             (k9, k10, k11, k12),
             (k13, k14, k15, k16),
             (k17, k18, k19, k20),
             (k21, k22, k23, k24),
             (k25, k26, k27, k28) ) ->
        Value.Array
          [|
            k1;
            k2;
            k3;
            k4;
            k5;
            k6;
            k7;
            k8;
            k9;
            k10;
            k11;
            k12;
            k13;
            k14;
            k15;
            k16;
            k17;
            k18;
            k19;
            k20;
            k21;
            k22;
            k23;
            k24;
            k25;
            k26;
            k27;
            k28;
          |])
      qvalue_4x4x4x7x4_raw)

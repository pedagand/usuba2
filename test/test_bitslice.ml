module Value = Ua0.Value
module IEnv = Ua0.Pass.Idents.Env
module EEnv = Ua0.Eval.Env
open Gen

(* Load & eval `gift_spec.ua` and `gift_bitslice.ua` *)

module GiftSpec = struct
  let symbol = File.load "src/gift_spec.ua"
  let gift32 = symbol "gift32"
  let round32 = symbol "round32"
  let subcells32 = symbol "subcells32"
end

module GiftBitslice = struct
  let symbol = File.load "src/gift_bitslice.ua"
  let transpose32 = symbol "transpose32"
  let transpose32_inv = symbol "transpose32_inv"
  let gift32 = symbol "gift32_bitslice"
  let round32 = symbol "round32_bitslice"
  let subcells32 = symbol "subcells32_bitslice"
end

(* QCheck tests *)

let test_transpose32 =
  QCheck.Test.make ~name:"transpose32 . transpose32_inv = id" qvalue_4x4x4
  @@ fun value ->
  Value.equal value
    ([ value ] |> GiftBitslice.transpose32
    |> (fun x -> [ x ])
    |> GiftBitslice.transpose32_inv)

let test_transpose32_id =
  QCheck.Test.make ~name:"transpose32 != id" qvalue_4x4x4 @@ fun value ->
  not (Value.equal value ([ value ] |> GiftBitslice.transpose32))

let test_transpose32_inv =
  QCheck.Test.make ~name:"transpose32_inv . transpose32 = id" qvalue_4x4x4
  @@ fun value ->
  Value.equal value
    ([ value ] |> GiftBitslice.transpose32_inv
    |> (fun x -> [ x ])
    |> GiftBitslice.transpose32)

let test_gift32 =
  QCheck.Test.make
    ~name:"gift32_bitslice = transpose32 . gift32 . transpose32_inv"
    (QCheck.pair qvalue_4x4x4x2
       (QCheck.array_of_size (QCheck.Gen.return 28) qvalue_4x4x4x2))
  @@ fun (state, keys) ->
  Value.equal
    (GiftBitslice.gift32 [ state; Value.VArray keys ])
    (let state = GiftBitslice.transpose32 [ state ] in
     let keys = keys |> Array.map (fun x -> GiftBitslice.transpose32 [ x ]) in
     let s = GiftSpec.gift32 [ state; Value.VArray keys ] in
     GiftBitslice.transpose32_inv [ s ])

let test_round32 =
  QCheck.Test.make
    ~name:"round32_bitslice = transpose32 . rounde32 . transpose32_inv"
    (QCheck.pair qvalue_4x4x4x2 qvalue_4x4x4x2)
  @@ fun (state, key) ->
  Value.equal
    (GiftBitslice.round32 [ state; key ])
    (let state = GiftBitslice.transpose32 [ state ] in
     let key = GiftBitslice.transpose32 [ key ] in
     let s = GiftSpec.round32 [ state; key ] in
     GiftBitslice.transpose32_inv [ s ])

let test_subcells32 =
  QCheck.Test.make
    ~name:"subcells32_bitslice = transpose32 . subcells32 . transpose32_inv"
    qvalue_4x4x4x2
  @@ fun state ->
  Value.equal
    (GiftBitslice.subcells32 [ state ])
    (let state = GiftBitslice.transpose32 [ state ] in
     let state = GiftSpec.subcells32 [ state ] in
     GiftBitslice.transpose32_inv [ state ])

let () =
  let open Alcotest in
  run "bitslice - test_reindex2.ua"
    [
      ( "transpose32",
        List.map QCheck_alcotest.to_alcotest
          [ test_transpose32_id; test_transpose32; test_transpose32_inv ] );
      ("gift32", [ QCheck_alcotest.to_alcotest ~long:true test_gift32 ]);
      ("round32", [ QCheck_alcotest.to_alcotest test_round32 ]);
      ("subcells32", [ QCheck_alcotest.to_alcotest test_subcells32 ]);
    ]

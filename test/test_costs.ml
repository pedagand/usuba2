module Eval = Ua0.Cost.Make (Ua0.Value.Bool)
module Value = Eval.Value
open Gen.Cost

module GiftSpec = struct
  let symbol = File.load_cost "src/gift_spec.ua"

  let vsymbol s =
    let value = symbol s in
    Value.Function { origin = s; value }

  let v_fnot = vsymbol "fnot"
  let v_fand = vsymbol "fand"
  let v_for' = vsymbol "for"
  let v_fxor = vsymbol "fxor"
  let subcells = symbol "subcells"
  let add_round_key = symbol "add_round_key"

  (* Test *)

  let test_subcells =
    QCheck.Test.make ~name:"subcells_" qvalue_4x4x4 @@ fun arg ->
    let c, _ = subcells [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    c = 11 * 16

  let test_add_round_key =
    QCheck.Test.make ~name:"add_round_key"
      QCheck.(pair qvalue_4x4x4 qvalue_4x4x4)
    @@ fun (state, key) ->
    let c, _ = add_round_key [ v_fxor; state; key ] in
    c = 64
end

module GiftBitslice = struct
  let symbol = File.load_cost "src/gift_bitslice.ua"

  let vsymbol s =
    let value = symbol s in
    Value.Function { origin = s; value }

  let v_fnot = vsymbol "fnot"
  let v_fand = vsymbol "fand"
  let v_for' = vsymbol "for"
  let v_fxor = vsymbol "fxor"
  let subcells_ = symbol "subcells_"
  let permbits = symbol "permbits_bitslice"
  let col_reverse = symbol "col_reverse"
  let permbits_bitslice0 = symbol "permbits_bitslice0"
  let subcells_bitslice = symbol "subcells_bitslice"
  let add_round_key_bitslice = symbol "add_round_key_bitslice"
  let round_bitslice = symbol "round_bitslice"
  let gift_bitslice = symbol "gift_bitslice"

  (* Test *)

  let test_col_reverse =
    QCheck.Test.make ~name:"col_reverse" qvalue4 @@ fun arg ->
    let c, _ = col_reverse [ arg ] in
    c = 0

  let test_permbits =
    QCheck.Test.make ~name:"permbits" qvalue_4x4x4 @@ fun arg ->
    let c, _ = permbits [ arg ] in
    c = 0

  let test_permbits_0 =
    QCheck.Test.make ~name:"permbits_0" qvalue_4x4x4 @@ fun arg ->
    let c, _ = permbits_bitslice0 [ arg ] in
    c = 0

  let test_subcells_ =
    QCheck.Test.make ~name:"subcells_" qvalue4 @@ fun arg ->
    let c, _ = subcells_ [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    c = 11

  let test_subcells_bitslice =
    QCheck.Test.make ~name:"subcells_bitslice" qvalue_4x4x4 @@ fun arg ->
    let c, _ = subcells_bitslice [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    c = 11 * 16

  let test_add_round_key_bitslice =
    QCheck.Test.make ~name:"add_round_key_bitslice"
      QCheck.(pair qvalue_4x4x4 qvalue_4x4x4)
    @@ fun (state, key) ->
    let c, _ = add_round_key_bitslice [ v_fxor; state; key ] in
    c = 64

  let test_round_bitslice =
    QCheck.Test.make ~name:"round_bitslice"
      QCheck.(pair qvalue_4x4x4 qvalue_4x4x4)
    @@ fun (state, key) ->
    let c, _ = round_bitslice [ v_fnot; v_fand; v_for'; v_fxor; state; key ] in
    c = (11 * 16) + 64

  let test_gift_bitslice =
    QCheck.Test.make ~name:"gift_bitslice"
      QCheck.(pair qvalue_4x4x4 qvalue_4x4x4x28)
    @@ fun (state, keys) ->
    let c, _ = gift_bitslice [ v_fnot; v_fand; v_for'; v_fxor; state; keys ] in
    c = 28 * ((11 * 16) + 64)
end

module GiftFixslice = struct
  let symbol = File.load_cost "src/gift_fixslice.ua"

  let vsymbol s =
    let value = symbol s in
    Value.Function { origin = s; value }

  let v_fnot = vsymbol "fnot"
  let v_fand = vsymbol "fand"
  let v_for' = vsymbol "for"
  let v_fxor = vsymbol "fxor"
  let gift_fixslice = symbol "gift_fixslice"

  (* Test *)

  let test_gift_fixslice =
    QCheck.Test.make ~name:"gift_fixslice"
      QCheck.(pair qvalue_4x4x4 qvalue_4x4x4x7x4)
    @@ fun (state, keys) ->
    let c, _ = gift_fixslice [ v_fnot; v_fand; v_for'; v_fxor; state; keys ] in
    c = 28 * ((11 * 16) + 64)
end

let () =
  let open Alcotest in
  run "cost - model naive"
    [
      ( "spec",
        QCheck_alcotest.(
          GiftSpec.[ to_alcotest test_subcells; to_alcotest test_add_round_key ])
      );
      ( "bitslice",
        QCheck_alcotest.(
          GiftBitslice.
            [
              to_alcotest test_col_reverse;
              to_alcotest test_permbits;
              to_alcotest test_permbits_0;
              to_alcotest test_subcells_;
              to_alcotest test_subcells_bitslice;
              to_alcotest test_add_round_key_bitslice;
              to_alcotest test_round_bitslice;
              to_alcotest test_gift_bitslice;
            ]) );
      ( "fixslice",
        QCheck_alcotest.(GiftFixslice.[ to_alcotest test_gift_fixslice ]) );
    ]

module Eval = Ua0.Cost.Make (Ua0.Value.Symbolical)
module Value = Eval.Value
module TermIdent = Ua0.Ident.TermIdent

let fresh_n n =
  let a =
    Array.init n (fun i ->
        let i = TermIdent.fresh (string_of_int i) in
        Value.Bool (Var i))
  in
  Value.Array a

let tup4 a b c d = (a, b, c, d)
let tup7 a b c d e f g = (a, b, c, d, e, f, g)
let value2 () = fresh_n 2
let value4 () = fresh_n 4
let value4x4 () = Value.Array [| value4 (); value4 (); value4 (); value4 () |]
let value4x2 () = Value.Array [| value2 (); value2 (); value2 (); value2 () |]

let value4x4x2 () =
  Value.Array [| value4x2 (); value4x2 (); value4x2 (); value4x2 () |]

let _value4x4x4x2 () =
  Value.Array [| value4x4x2 (); value4x4x2 (); value4x4x2 (); value4x4x2 () |]

let value4x4x4 () =
  Value.Array [| value4x4 (); value4x4 (); value4x4 (); value4x4 () |]

let value_4x4x4x7x4_raw () =
  tup7
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))
    (tup4 (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()) (value4x4x4 ()))

let value_4x4x4x7x4 () =
  let ( (k1, k2, k3, k4),
        (k5, k6, k7, k8),
        (k9, k10, k11, k12),
        (k13, k14, k15, k16),
        (k17, k18, k19, k20),
        (k21, k22, k23, k24),
        (k25, k26, k27, k28) ) =
    value_4x4x4x7x4_raw ()
  in

  Value.Array
    [|
      Value.Array [| k1; k2; k3; k4 |];
      Value.Array [| k5; k6; k7; k8 |];
      Value.Array [| k9; k10; k11; k12 |];
      Value.Array [| k13; k14; k15; k16 |];
      Value.Array [| k17; k18; k19; k20 |];
      Value.Array [| k21; k22; k23; k24 |];
      Value.Array [| k25; k26; k27; k28 |];
    |]

let value_4x4x4x28 () =
  let ( (k1, k2, k3, k4),
        (k5, k6, k7, k8),
        (k9, k10, k11, k12),
        (k13, k14, k15, k16),
        (k17, k18, k19, k20),
        (k21, k22, k23, k24),
        (k25, k26, k27, k28) ) =
    value_4x4x4x7x4_raw ()
  in
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
    |]

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
  let permbits = symbol "permbits"
  let round = symbol "round"
  let gift = symbol "gift"

  (* Test *)

  let test_subcells () =
    let arg = value4x4x4 () in
    let c, _ = subcells [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    Alcotest.(check int) "" (11 * 16) c

  let test_permbits () =
    let arg = value4x4x4 () in
    let c, _ = permbits [ arg ] in
    Alcotest.(check int) "" 0 c

  let test_add_round_key () =
    let state = value4x4x4 () in
    let key = value4x4x4 () in
    let c, _ = add_round_key [ v_fxor; state; key ] in
    Alcotest.(check int) "" 64 c

  let test_round () =
    let state = value4x4x4 () in
    let key = value4x4x4 () in
    let c, _ = round [ v_fnot; v_fand; v_for'; v_fxor; state; key ] in
    Alcotest.(check int) "" ((11 * 16) + 64) c

  let test_gift () =
    let state = value4x4x4 () in
    let keys = value_4x4x4x28 () in
    let c, _ = gift [ v_fnot; v_fand; v_for'; v_fxor; state; keys ] in
    let expected = 28 * ((11 * 16) + 64) in
    Alcotest.(check int) "" expected c

  let tests =
    Alcotest.
      [
        test_case "subcells" `Quick test_subcells;
        test_case "test_permbits" `Quick test_permbits;
        test_case "add_round_key" `Quick test_add_round_key;
        test_case "round" `Quick test_round;
        test_case "gift" `Quick test_gift;
      ]
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

  let test_col_reverse () =
    let arg = value4 () in
    let c, _ = col_reverse [ arg ] in
    Alcotest.(check int) "" 0 c

  let test_permbits () =
    let arg = value4x4x4 () in
    let c, _ = permbits [ arg ] in
    Alcotest.(check int) "" 0 c

  let test_permbits_0 () =
    let arg = value4x4x4 () in
    let c, _ = permbits_bitslice0 [ arg ] in
    Alcotest.(check int) "" 0 c

  let test_subcells_ () =
    let arg = value4 () in
    let c, _ = subcells_ [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    Alcotest.(check int) "" 11 c

  let test_subcells_bitslice () =
    let arg = value4x4x4 () in
    let c, _ = subcells_bitslice [ v_fnot; v_fand; v_for'; v_fxor; arg ] in
    Alcotest.(check int) "" (11 * 16) c

  let test_add_round_key_bitslice () =
    let state = value4x4x4 () in
    let key = value4x4x4 () in
    let c, _ = add_round_key_bitslice [ v_fxor; state; key ] in
    Alcotest.(check int) "" 64 c

  let test_round_bitslice () =
    let state = value4x4x4 () in
    let key = value4x4x4 () in
    let c, _ = round_bitslice [ v_fnot; v_fand; v_for'; v_fxor; state; key ] in
    Alcotest.(check int) "" ((11 * 16) + 64) c

  let test_gift_bitslice () =
    let state = value4x4x4 () in
    let keys = value_4x4x4x28 () in
    let c, _ = gift_bitslice [ v_fnot; v_fand; v_for'; v_fxor; state; keys ] in
    Alcotest.(check int) "" (28 * ((11 * 16) + 64)) c

  let tests =
    Alcotest.
      [
        test_case "col_reverse" `Quick test_col_reverse;
        test_case "permbits" `Quick test_permbits;
        test_case "permbits_0" `Quick test_permbits_0;
        test_case "subcells_" `Quick test_subcells_;
        test_case "subcells_bitslice" `Quick test_subcells_bitslice;
        test_case "add_round_key_bitslice" `Quick test_add_round_key_bitslice;
        test_case "round_bitslice" `Quick test_round_bitslice;
        test_case "gift_bitslice" `Quick test_gift_bitslice;
      ]
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

  let test_gift_fixslice () =
    let state = value4x4x4 () in
    let keys = value_4x4x4x7x4 () in
    let c, _ = gift_fixslice [ v_fnot; v_fand; v_for'; v_fxor; state; keys ] in
    Alcotest.(check int) "" (28 * ((11 * 16) + 64)) c

  let tests = Alcotest.[ test_case "gift_fixslice" `Quick test_gift_fixslice ]
end

let () =
  let open Alcotest in
  run "cost - model naive"
    [
      ("spec", GiftSpec.tests);
      ("bitslice", GiftBitslice.tests);
      ("fixslice", GiftFixslice.tests);
    ]

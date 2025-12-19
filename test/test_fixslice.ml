module Value = Ua0.Value

(* Load & eval `gift_fixslice.ua` *)

module GiftBitslice = struct
  let symbol = File.load "src/gift_bitslice.ua"
  let permbits = symbol "permbits_bitslice"
end

module GiftFixslice = struct
  let symbol = File.load "src/gift_fixslice.ua"
  let permbits_mod_0_ = symbol "permbits_fixslice_mod_0_"
  let permbits_mod_0_4 = symbol "permbits_fixslice_mod_0_4"
  let rev_rotate_1 = symbol "rev_rotate_1"
  let inv_rev_rotate_1 = symbol "inv_rev_rotate_1"
  let transpose = symbol "transpose"
  let inv_transpose = symbol "inv_transpose"
  let permbits_mod0 = symbol "permbits_fixslice_mod_0_4"
  let permbits_mod1 = symbol "permbits_fixslice_mod_1_"
  let permbits_mod2 = symbol "permbits_fixslice_mod_2_"
  let permbits_mod3 = symbol "permbits_fixslice_mod_3_"
  let map_rev_rotate_1 = symbol "map_rev_rotate_1"
end

let test_compose_id ~eq ~name f1 f2 ty =
  QCheck.Test.make ~name ty @@ fun value ->
  eq value
    (let value = f1 [ value ] in
     f2 [ value ])

(*
let apply2 f = fun args -> f [ f args ]*)
let compose g f args = g [ f args ]
let ( $ ) = compose

let test_eq_f ?verbose ~eq ~name lhs rhs ty =
  QCheck.Test.make ~name ty @@ fun value ->
  let lhs = lhs [ value ] in
  let rhs = rhs [ value ] in
  let () =
    Option.iter
      (fun pp -> Format.eprintf "\nlhs = %a\nrhs = %a\n" pp lhs pp rhs)
      verbose
  in
  eq lhs rhs

let test_permibits_fixslice_transformation =
  QCheck.Test.make ~name:"Permbits fixslice transformation" Gen.qvalue_4x4x4
  @@ fun value ->
  let args = [ value ] in
  Value.equal
    (GiftFixslice.permbits_mod_0_ args)
    (GiftFixslice.permbits_mod_0_4 args)

let test_sigma_compose =
  test_compose_id ~eq:Value.equal ~name:"Sigma | InvSigma compose id"
    GiftFixslice.rev_rotate_1 GiftFixslice.inv_rev_rotate_1 Gen.qvalue_4x4

let test_sigma4_id =
  let sigma = GiftFixslice.rev_rotate_1 in
  QCheck.Test.make ~name:"Sigma compose 4 = id" Gen.qvalue_4x4 @@ fun value ->
  Value.equal value ((sigma $ sigma $ sigma $ sigma) [ value ])

let test_compose_transposition =
  test_compose_id ~eq:Value.equal ~name:"tranposition | inv - compose"
    GiftFixslice.transpose GiftFixslice.inv_transpose Gen.qvalue_4x4

let test_permbits_fixslice_mod_0 =
  test_eq_f ~eq:Value.equal ~name:"Permbits fixslice : mod 0"
    GiftBitslice.permbits
    (GiftFixslice.map_rev_rotate_1 $ GiftFixslice.permbits_mod0)
    Gen.qvalue_4x4x4

let test_permbits_fixslice_mod_1 =
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 1"
    (GiftBitslice.permbits $ GiftBitslice.permbits)
    (GiftFixslice.map_rev_rotate_1 $ GiftFixslice.map_rev_rotate_1
   $ GiftFixslice.permbits_mod1 $ GiftFixslice.permbits_mod0)
    Gen.qvalue_4x4x4

let test_permbits_fixslice_mod_2 =
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 2"
    (GiftBitslice.permbits $ GiftBitslice.permbits $ GiftBitslice.permbits)
    (GiftFixslice.map_rev_rotate_1 $ GiftFixslice.map_rev_rotate_1
   $ GiftFixslice.map_rev_rotate_1 $ GiftFixslice.permbits_mod2
   $ GiftFixslice.permbits_mod1 $ GiftFixslice.permbits_mod0)
    Gen.qvalue_4x4x4

let test_permbits_fixslice_mod_3 =
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 3"
    (GiftBitslice.permbits $ GiftBitslice.permbits $ GiftBitslice.permbits
   $ GiftBitslice.permbits)
    (GiftFixslice.map_rev_rotate_1 $ GiftFixslice.map_rev_rotate_1
   $ GiftFixslice.map_rev_rotate_1 $ GiftFixslice.map_rev_rotate_1
   $ GiftFixslice.permbits_mod3 $ GiftFixslice.permbits_mod2
   $ GiftFixslice.permbits_mod1 $ GiftFixslice.permbits_mod0)
    Gen.qvalue_4x4x4

let test_permbits_fixslice_mod_3_no_sigma =
  test_eq_f ~verbose:Value.pp ~eq:Value.equal
    ~name:"Permbits fixslice : mod 3 (no sigma)"
    (GiftBitslice.permbits $ GiftBitslice.permbits $ GiftBitslice.permbits
   $ GiftBitslice.permbits)
    (GiftFixslice.permbits_mod3 $ GiftFixslice.permbits_mod2
   $ GiftFixslice.permbits_mod1 $ GiftFixslice.permbits_mod0)
    Gen.qvalue_4x4x4

let () =
  let open Alcotest in
  run "fixslice - test_reindex_fs.ua"
    [
      ("Transpose", [ QCheck_alcotest.to_alcotest test_compose_transposition ]);
      ( "Sigma",
        [
          QCheck_alcotest.to_alcotest test_sigma_compose;
          QCheck_alcotest.to_alcotest test_sigma4_id;
        ] );
      ( "Permbits",
        [
          QCheck_alcotest.to_alcotest test_permibits_fixslice_transformation;
          QCheck_alcotest.to_alcotest test_permbits_fixslice_mod_0;
          QCheck_alcotest.to_alcotest test_permbits_fixslice_mod_1;
          QCheck_alcotest.to_alcotest test_permbits_fixslice_mod_2;
          QCheck_alcotest.to_alcotest test_permbits_fixslice_mod_3;
          QCheck_alcotest.to_alcotest test_permbits_fixslice_mod_3_no_sigma;
        ] );
    ]

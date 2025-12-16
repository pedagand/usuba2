module Value = Ua0.Value
module IEnv = Ua0.Pass.Idents.Env
module EEnv = Ua0.Eval.Env

let filename = "src/test_reindex_fs.ua"

let env, ast =
  let file = filename in
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  Ua0.Pass.Idents.of_string_ast_env ast

let prog = Ua0.Eval.eval ast
let qvalue_bool = QCheck.(bool |> map (fun v -> Value.VBool v))
let value4 (a, b, c, d) = Value.VArray [| a; b; c; d |]

let qvalue4 =
  QCheck.(tup4 qvalue_bool qvalue_bool qvalue_bool qvalue_bool |> map value4)

let qvalue_4x4 = QCheck.(tup4 qvalue4 qvalue4 qvalue4 qvalue4 |> map value4)

let qvalue_4x4x4 =
  QCheck.(tup4 qvalue_4x4 qvalue_4x4 qvalue_4x4 qvalue_4x4 |> map value4)

let test_compose_id ~eq ~name f1 f2 ty =
  QCheck.Test.make ~name ty @@ fun value ->
  eq value
    (let value = f1 [ value ] in
     f2 [ value ])

(*
let apply2 f = fun args -> f [ f args ]*)
let compose g f args = g [ f args ]
let ( $ ) = compose

let symbol ienv functions s =
  let f = IEnv.find_fn_ident s ienv in
  EEnv.Functions.find f functions

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

let test_permibits_fixslice_transformation ienv functions =
  let permbits_fixslice_mod_0_ =
    symbol ienv functions "permbits_fixslice_mod_0_"
  in
  let permbits_fixslice_mod_0_4 =
    symbol ienv functions "permbits_fixslice_mod_0_4"
  in
  QCheck.Test.make ~name:"Permbits fixslice transformation" qvalue_4x4x4
  @@ fun value ->
  let args = [ value ] in
  Value.equal (permbits_fixslice_mod_0_ args) (permbits_fixslice_mod_0_4 args)

let test_sigma_compose ienv functions =
  let rev_rotate_1 = symbol ienv functions "rev_rotate_1" in
  let inv_rev_rotate_1 = symbol ienv functions "inv_rev_rotate_1" in
  test_compose_id ~eq:Value.equal ~name:"Sigma | InvSigma compose id"
    rev_rotate_1 inv_rev_rotate_1 qvalue_4x4

let test_sigma4_id ienv functions =
  let sigma = symbol ienv functions "rev_rotate_1" in
  QCheck.Test.make ~name:"Sigma compose 4 = id" qvalue_4x4 @@ fun value ->
  Value.equal value ((sigma $ sigma $ sigma $ sigma) [ value ])

let test_compose_transposition ienv functions =
  let transposition = symbol ienv functions "transpose" in
  let inv_transposition = symbol ienv functions "inv_transpose" in
  test_compose_id ~eq:Value.equal ~name:"tranposition | inv - compose"
    transposition inv_transposition qvalue_4x4

let test_permbits_fixslice_mod_0 ienv functions =
  let pb = symbol ienv functions "permbits_bitslice" in
  let pf_mod0 = symbol ienv functions "permbits_fixslice_mod_0_4" in
  let sync = symbol ienv functions "map_rev_rotate_1" in
  test_eq_f ~eq:Value.equal ~name:"Permbits fixslice : mod 0" pb
    (sync $ pf_mod0) qvalue_4x4x4

let test_permbits_fixslice_mod_1 ienv functions =
  let pb = symbol ienv functions "permbits_bitslice" in
  let pf_mod0 = symbol ienv functions "permbits_fixslice_mod_0_4" in
  let pf_mod1 = symbol ienv functions "permbits_fixslice_mod_1_" in
  let map_rev_rotate_1 = symbol ienv functions "map_rev_rotate_1" in
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 1"
    (pb $ pb)
    (map_rev_rotate_1 $ map_rev_rotate_1 $ pf_mod1 $ pf_mod0)
    qvalue_4x4x4

let test_permbits_fixslice_mod_2 ienv functions =
  let pb = symbol ienv functions "permbits_bitslice" in
  let pf_mod0 = symbol ienv functions "permbits_fixslice_mod_0_4" in
  let pf_mod1 = symbol ienv functions "permbits_fixslice_mod_1_" in
  let pf_mod2 = symbol ienv functions "permbits_fixslice_mod_2_" in
  let map_sigma = symbol ienv functions "map_rev_rotate_1" in
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 2"
    (pb $ pb $ pb)
    (map_sigma $ map_sigma $ map_sigma $ pf_mod2 $ pf_mod1 $ pf_mod0)
    qvalue_4x4x4

let test_permbits_fixslice_mod_3 ienv functions =
  let pb = symbol ienv functions "permbits_bitslice" in
  let pf_mod0 = symbol ienv functions "permbits_fixslice_mod_0_4" in
  let pf_mod1 = symbol ienv functions "permbits_fixslice_mod_1_" in
  let pf_mod2 = symbol ienv functions "permbits_fixslice_mod_2_" in
  let pf_mod3 = symbol ienv functions "permbits_fixslice_mod_3_" in
  let map_sigma = symbol ienv functions "map_rev_rotate_1" in
  test_eq_f ~verbose:Value.pp ~eq:Value.equal ~name:"Permbits fixslice : mod 3"
    (pb $ pb $ pb $ pb)
    (map_sigma $ map_sigma $ map_sigma $ map_sigma $ pf_mod3 $ pf_mod2 $ pf_mod1
   $ pf_mod0)
    qvalue_4x4x4

let test_permbits_fixslice_mod_3_no_sigma ienv functions =
  let pb = symbol ienv functions "permbits_bitslice" in
  let pf_mod0 = symbol ienv functions "permbits_fixslice_mod_0_4" in
  let pf_mod1 = symbol ienv functions "permbits_fixslice_mod_1_" in
  let pf_mod2 = symbol ienv functions "permbits_fixslice_mod_2_" in
  let pf_mod3 = symbol ienv functions "permbits_fixslice_mod_3_" in
  test_eq_f ~verbose:Value.pp ~eq:Value.equal
    ~name:"Permbits fixslice : mod 3 (no sigma)"
    (pb $ pb $ pb $ pb)
    (pf_mod3 $ pf_mod2 $ pf_mod1 $ pf_mod0)
    qvalue_4x4x4

let () =
  let open Alcotest in
  run "fixslice - test_reindex_fs.ua"
    [
      ( "Transpose",
        [ QCheck_alcotest.to_alcotest (test_compose_transposition env prog) ] );
      ( "Sigma",
        [
          QCheck_alcotest.to_alcotest (test_sigma_compose env prog);
          QCheck_alcotest.to_alcotest (test_sigma4_id env prog);
        ] );
      ( "Permbits",
        [
          QCheck_alcotest.to_alcotest
            (test_permibits_fixslice_transformation env prog);
          QCheck_alcotest.to_alcotest (test_permbits_fixslice_mod_0 env prog);
          QCheck_alcotest.to_alcotest (test_permbits_fixslice_mod_1 env prog);
          QCheck_alcotest.to_alcotest (test_permbits_fixslice_mod_2 env prog);
          QCheck_alcotest.to_alcotest (test_permbits_fixslice_mod_3 env prog);
          QCheck_alcotest.to_alcotest
            (test_permbits_fixslice_mod_3_no_sigma env prog);
        ] );
    ]

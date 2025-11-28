module Value = Ua0.Value
module IEnv = Ua0.Pass.Idents.Env
module EEnv = Ua0.Eval.Env

let ast file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  Ua0.Pass.Idents.of_string_ast_env ast

let filename = "test_reindex_fs.ua"
let test_reindex_fs = Filename.concat "src" filename
let qvalue_bool = QCheck.(bool |> map (fun v -> Value.VBool v))
let value4 (a, b, c, d) = Value.VArray [| a; b; c; d |]

let qvalue4 =
  QCheck.(tup4 qvalue_bool qvalue_bool qvalue_bool qvalue_bool |> map value4)

let test_compose_id ~eq ~name f1 f2 ty =
  QCheck.Test.make ~name ty @@ fun value ->
  eq value
    (let value = f1 [ value ] in
     f2 [ value ])

let symbole ienv functions s =
  let f = IEnv.find_fn_ident s ienv in
  EEnv.Functions.find f functions

let test_sigma_compose eenv functions =
  let rev_rotate_1 = symbole eenv functions "rev_rotate_1" in
  let inv_rev_rotate_1 = symbole eenv functions "inv_rev_rotate_1" in
  test_compose_id ~eq:Value.equal ~name:"Sigma | InvSigma compose id"
    rev_rotate_1 inv_rev_rotate_1
    QCheck.(tup4 qvalue4 qvalue4 qvalue4 qvalue4 |> map value4)

let test_compose_transposition ienv functions =
  let transposition = symbole ienv functions "transpose" in
  let inv_transposition = symbole ienv functions "inv_transpose" in
  test_compose_id ~eq:Value.equal ~name:"tranposition | inv - compose"
    transposition inv_transposition
    QCheck.(tup4 qvalue4 qvalue4 qvalue4 qvalue4 |> map value4)

let () =
  let open Alcotest in
  let env, ast = ast test_reindex_fs in
  let functions = Ua0.Eval.eval ast in
  run "fixslice - test_reindex_fs.ua"
    [
      ( "Transpose",
        [
          QCheck_alcotest.to_alcotest (test_compose_transposition env functions);
        ] );
      ( "Sigma",
        [ QCheck_alcotest.to_alcotest (test_sigma_compose env functions) ] );
    ]

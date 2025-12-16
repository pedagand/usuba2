module Value = Ua0.Value
module IEnv = Ua0.Pass.Idents.Env
module EEnv = Ua0.Eval.Env

(* Load & eval `test_reindex2.ua` *)

let filename = "src/test_reindex2.ua"

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

let symbol ienv functions s =
  let f = IEnv.find_fn_ident s ienv in
  EEnv.Functions.find f functions

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

(* QCheck tests *)

let test_transpose32 ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  let transpose32_inv = symbol ienv functions "transpose32_inv" in
  QCheck.Test.make ~name:"transpose32 . transpose32_inv = id" qvalue_4x4x4
  @@ fun value ->
  Value.equal value
    ([ value ] |> transpose32 |> (fun x -> [ x ]) |> transpose32_inv)

let test_transpose32_id ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  QCheck.Test.make ~name:"transpose32 != id" qvalue_4x4x4 @@ fun value ->
  not (Value.equal value ([ value ] |> transpose32))

let test_transpose32_inv ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  let transpose32_inv = symbol ienv functions "transpose32_inv" in
  QCheck.Test.make ~name:"transpose32_inv . transpose32 = id" qvalue_4x4x4
  @@ fun value ->
  Value.equal value
    ([ value ] |> transpose32_inv |> (fun x -> [ x ]) |> transpose32)

let test_gift32 ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  let transpose32_inv = symbol ienv functions "transpose32_inv" in
  let gift32 = symbol ienv functions "gift32" in
  let gift32_bitslice = symbol ienv functions "gift32_bitslice" in
  QCheck.Test.make
    ~name:"gift32_bitslice = transpose32 . gift32 . transpose32_inv"
    (QCheck.pair qvalue_4x4x4x2
       (QCheck.array_of_size (QCheck.Gen.return 28) qvalue_4x4x4x2))
  @@ fun (state, keys) ->
  Value.equal
    (gift32_bitslice [ state; Value.VArray keys ])
    (let state = transpose32 [ state ] in
     let keys = keys |> Array.map (fun x -> transpose32 [ x ]) in
     let s = gift32 [ state; Value.VArray keys ] in
     transpose32_inv [ s ])

let test_round32 ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  let transpose32_inv = symbol ienv functions "transpose32_inv" in
  let round32 = symbol ienv functions "round32" in
  let round32_bitslice = symbol ienv functions "round32_bitslice" in
  QCheck.Test.make
    ~name:"round32_bitslice = transpose32 . rounde32 . transpose32_inv"
    (QCheck.pair qvalue_4x4x4x2 qvalue_4x4x4x2)
  @@ fun (state, key) ->
  Value.equal
    (round32_bitslice [ state; key ])
    (let state = transpose32 [ state ] in
     let key = transpose32 [ key ] in
     let s = round32 [ state; key ] in
     transpose32_inv [ s ])

let test_subcells32 ienv functions =
  let transpose32 = symbol ienv functions "transpose32" in
  let transpose32_inv = symbol ienv functions "transpose32_inv" in
  let subcells32 = symbol ienv functions "subcells32" in
  let subcells32_bitslice = symbol ienv functions "subcells32_bitslice" in
  QCheck.Test.make
    ~name:"subcells32_bitslice = transpose32 . subcells32 . transpose32_inv"
    qvalue_4x4x4x2
  @@ fun state ->
  Value.equal
    (subcells32_bitslice [ state ])
    (let state = transpose32 [ state ] in
     let state = subcells32 [ state ] in
     transpose32_inv [ state ])

let () =
  let open Alcotest in
  run "bitslice - test_reindex2.ua"
    [
      ( "transpose32",
        List.map QCheck_alcotest.to_alcotest
          [
            test_transpose32_id env prog;
            test_transpose32 env prog;
            test_transpose32_inv env prog;
          ] );
      ( "gift32",
        [ QCheck_alcotest.to_alcotest ~long:true (test_gift32 env prog) ] );
      ("round32", [ QCheck_alcotest.to_alcotest (test_round32 env prog) ]);
      ("subcells32", [ QCheck_alcotest.to_alcotest (test_subcells32 env prog) ]);
    ]

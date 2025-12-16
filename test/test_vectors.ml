module Double = Ua0.Value.Naperian (struct
  let n = 2
end)

module Rows = Ua0.Value.Naperian (struct
  let n = 4
end)

module Cols = Rows
module Slice = Rows
module ColsRows = Ua0.Value.NaperianCompose (Cols) (Rows)
module ColsRowsSlice = Ua0.Value.NaperianCompose (ColsRows) (Slice)

let testable_value = Alcotest.testable Ua0.Value.pp Ua0.Value.equal
let filename = "test_reindex2.ua"
let test_reindex2 = Filename.concat "src" filename

let ast file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  Ua0.Pass.Idents.of_string_ast_env ast

let vbitslice value =
  Ua0.Value.reindex_lr (module ColsRows) (module Slice) value

let invbitslice value =
  Ua0.Value.reindex_lr (module Slice) (module ColsRows) value

let test_vector n =
  let ( / ) = Filename.concat in
  let prefix s = "test-vectors" / "gift64" / s in
  let n = match n with `T1 -> 1 | `T2 -> 2 | `T3 -> 3 in
  let plaintext = Printf.sprintf "gift64-plaintext%u.txt" n in
  let key = Printf.sprintf "gift64-key%u.txt" n in
  let cipher = Printf.sprintf "gift64-cipher%u.txt" n in
  (prefix plaintext, prefix key, prefix cipher)

let values_of_keyfilename ~bitslice key =
  let key = Util.Io.file_to_bools key in
  let keys = Util.Gift.uvconsts key in
  match bitslice with true -> List.map vbitslice keys | false -> keys

let value_of_plainfilename ~bitslice filename =
  let state = Util.Io.file_to_bools filename in
  let state = Util.Gift.spec_tabulate state in
  match bitslice with true -> vbitslice state | false -> state

let value_combine lhs rhs =
  Ua0.Value.map2 (fun lhs rhs -> Ua0.Value.VArray [| lhs; rhs |]) lhs rhs

let test_vector_16 ~bitslice fn plaintext key cipher () =
  let keys = values_of_keyfilename ~bitslice key in
  let state = value_of_plainfilename ~bitslice plaintext in
  let result = Util.Gift.spec_tabulate @@ Util.Io.file_to_bools cipher in
  let value = fn [ state; Ua0.Value.VArray (Array.of_list keys) ] in
  let message, value =
    match bitslice with
    | true -> ("gift bitslice", invbitslice value)
    | false -> ("gift", value)
  in
  Alcotest.check testable_value message result value

let test_vector_32 ~bitslice fn p1 k1 c1 p2 k2 c2 () =
  let k1 = values_of_keyfilename ~bitslice k1 in
  let s1 = value_of_plainfilename ~bitslice p1 in
  let r1 = Util.Gift.spec_tabulate @@ Util.Io.file_to_bools c1 in

  let k2 = values_of_keyfilename ~bitslice k2 in
  let s2 = value_of_plainfilename ~bitslice p2 in
  let r2 = Util.Gift.spec_tabulate @@ Util.Io.file_to_bools c2 in
  let results = [ r1; r2 ] in

  let state = value_combine s1 s2 in
  let keys = List.map2 value_combine k1 k2 in

  let value = fn [ state; Ua0.Value.VArray (Array.of_list keys) ] in
  let v1, v2 = Ua0.Value.split2 value in
  let values = [ v1; v2 ] in

  let message, values =
    match bitslice with
    | true -> ("gift32 bitslice", List.map invbitslice values)
    | false -> ("gift32 spec", values)
  in
  Alcotest.(check @@ list testable_value) message results values

let tests_gift16 ~bitslice symbole env =
  let fn = Ua0.Eval.Env.Functions.find symbole env in
  let p1, k1, c1 = test_vector `T1 in
  let p2, k2, c2 = test_vector `T2 in
  let p3, k3, c3 = test_vector `T3 in
  Alcotest.
    [
      test_case "test-vector 1" `Quick (test_vector_16 ~bitslice fn p1 k1 c1);
      test_case "test-vector 2" `Quick (test_vector_16 ~bitslice fn p2 k2 c2);
      test_case "test-vector 3" `Quick (test_vector_16 ~bitslice fn p3 k3 c3);
    ]

let tests_gift32 ~bitslice symbole env =
  let fn = Ua0.Eval.Env.Functions.find symbole env in
  let p1, k1, c1 = test_vector `T1 in
  let p2, k2, c2 = test_vector `T2 in
  let p3, k3, c3 = test_vector `T3 in
  Alcotest.
    [
      (* test 1*)
      test_case "test-vector 1 & 1" `Quick
        (test_vector_32 ~bitslice fn p1 k1 c1 p1 k1 c1);
      test_case "test-vector 1 & 2" `Quick
        (test_vector_32 ~bitslice fn p1 k1 c1 p2 k2 c2);
      test_case "test-vector 1 & 3" `Quick
        (test_vector_32 ~bitslice fn p1 k1 c1 p3 k3 c3);
      (* test 2 *)
      test_case "test-vector 2 & 1" `Quick
        (test_vector_32 ~bitslice fn p2 k2 c2 p1 k1 c1);
      test_case "test-vector 2 & 2" `Quick
        (test_vector_32 ~bitslice fn p2 k2 c2 p2 k2 c2);
      test_case "test-vector 2 & 3" `Quick
        (test_vector_32 ~bitslice fn p2 k2 c2 p3 k3 c3);
      (* Test 3*)
      test_case "test-vector 3 & 1" `Quick
        (test_vector_32 ~bitslice fn p3 k3 c3 p1 k1 c1);
      test_case "test-vector 3 & 2" `Quick
        (test_vector_32 ~bitslice fn p3 k3 c3 p2 k2 c2);
      test_case "test-vector 3 & 3" `Quick
        (test_vector_32 ~bitslice fn p3 k3 c3 p3 k3 c3);
    ]

let () =
  let open Alcotest in
  let env, prog = ast test_reindex2 in
  let gift16 = Ua0.Pass.Idents.Env.find_fn_ident "gift16" env in
  let giftb_16 = Ua0.Pass.Idents.Env.find_fn_ident "gift16_bitslice" env in
  let gift32 = Ua0.Pass.Idents.Env.find_fn_ident "gift32" env in
  let giftb_32 = Ua0.Pass.Idents.Env.find_fn_ident "gift32_bitslice" env in

  let fns = Ua0.Eval.eval prog in
  run "test-vector"
    [
      ("gift16 spec", tests_gift16 ~bitslice:false gift16 fns);
      ("gift16 bitslice", tests_gift16 ~bitslice:true giftb_16 fns);
      ("gift32 spec", tests_gift32 ~bitslice:false gift32 fns);
      ("gift32 bitslice", tests_gift32 ~bitslice:true giftb_32 fns);
    ]

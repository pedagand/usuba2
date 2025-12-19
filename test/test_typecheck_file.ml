let typecheck file =
  let file = "src/" ^ file in
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let _, ast = Ua0.Pass.Idents.of_string_ast_env ast in
  ignore @@ Ua0.Typecheck.of_ua0_prog ast

let test file =
  ( file,
    [
      Alcotest.(
        test_case file `Quick (fun () ->
            check pass ("typecheck " ^ file) () (typecheck file)));
    ] )

let () =
  let open Alcotest in
  run "Typechecking src/"
    [ test "gift_spec.ua"; test "gift_bitslice.ua"; test "gift_fixslice.ua" ]

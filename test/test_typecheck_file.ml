let filename = "test_reindex2.ua"
let test_reindex2 = Filename.concat "src" filename

(*let t_unit =
  Alcotest.testable (fun format () -> Format.fprintf format "()") Unit.equal*)

let ast file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let _, ast = Ua0.Pass.Idents.of_string_ast_env ast in
  (*  let symbole = Ua0.Pass.Idents.Env.find_fn_ident symbole env in*)
  ast

let () =
  let open Alcotest in
  let reindex2 = ast test_reindex2 in
  run
    (Printf.sprintf "typecheck - %s" test_reindex2)
    [
      ( test_reindex2,
        [
          test_case test_reindex2 `Quick (fun () ->
              Alcotest.check pass ("typecheck " ^ filename) ()
                (ignore @@ Ua0.Typecheck.of_ua0_prog reindex2));
        ] );
    ]

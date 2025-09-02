let _ast symbole file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let env, ast = Ua0.Pass.Idents.of_string_ast_env ast in
  let symbole = Ua0.Pass.Idents.Env.find_fn_ident symbole env in
  (ast, symbole)

module Subcells = struct end

let () =
  let open Alcotest in
  run "reindex wrap" []

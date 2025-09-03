let file = Filename.concat "src" "test_reindex.ua"
let fn_declaration = Alcotest.testable Uat.Pp.pp_fn Uat.Util.Eq.fn_decl

let ast file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let ua0env, ast = Ua0.Pass.Idents.of_string_ast_env ast in
  let uatenv, ast = Uat.Typecheck.of_ua0_module ast in
  (ua0env, uatenv, ast)

module Subcells = struct
  let symbole = "subcells"
  let test_symbole = "subcells_reindexed"

  let test fty f () =
    let fn_decl = f symbole in
    let fn_decl_test = f test_symbole in
    let row = fty "Row" in
    let col = fty "Col" in
    let slice = fty "Slice" in
    Alcotest.(check fn_declaration)
      "subcells reindex" fn_decl_test
      (Uat.Pass.ReindexWrap.wr_function [ col; row ] [ slice ] fn_decl)
end

let type_declaration env0 name = Ua0.Pass.Idents.Env.find_tycstr name env0

let fn_declaration env0 ast symbole =
  let symbole = Ua0.Pass.Idents.Env.find_fn_ident symbole env0 in
  Option.get
  @@ List.find_map
       (function
         | Uat.Ast.NTy _ -> None
         | NFun fn_decl ->
             if Uat.Ast.FnIdent.equal symbole fn_decl.fn_name then Some fn_decl
             else None)
       ast

let () =
  let open Alcotest in
  let env0, _env1, ast = ast file in
  run "reindex wrap"
    [
      ( "subcells",
        [
          test_case "subcells" `Quick
            (Subcells.test (type_declaration env0) (fn_declaration env0 ast));
        ] );
    ]

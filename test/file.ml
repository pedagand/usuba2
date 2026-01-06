let load filename =
  let module Eval = Ua0.Eval.Make (Ua0.Value.Bool) in
  let module Value = Eval.Value in
  let module IEnv = Ua0.Pass.Idents.Env in
  let env, ast =
    let file = filename in
    let ast =
      In_channel.with_open_bin file (fun ic ->
          let lexbuf = Lexing.from_channel ic in
          let () = Lexing.set_filename lexbuf file in
          Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
    in
    Ua0.Pass.Idents.of_string_ast_env ast
  in
  let prog = Eval.eval ast in
  let symbol s =
    let f = IEnv.find_fn_ident s env in
    Eval.Env.Functions.find f prog
  in
  symbol

let load_cost filename =
  let module Eval = Ua0.Cost.Make (Ua0.Value.Symbolical) in
  let module Value = Eval.Value in
  let module IEnv = Ua0.Pass.Idents.Env in
  let env, ast =
    let file = filename in
    let ast =
      In_channel.with_open_bin file (fun ic ->
          let lexbuf = Lexing.from_channel ic in
          let () = Lexing.set_filename lexbuf file in
          Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
    in
    Ua0.Pass.Idents.of_string_ast_env ast
  in
  let prog = Eval.eval ast in
  let symbol s =
    let f = IEnv.find_fn_ident s env in
    Eval.Env.Functions.find f prog
  in
  symbol

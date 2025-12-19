module Value = Ua0.Value
module IEnv = Ua0.Pass.Idents.Env
module EEnv = Ua0.Eval.Env

let load filename =
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
  let prog = Ua0.Eval.eval ast in
  let symbol s =
    let f = IEnv.find_fn_ident s env in
    EEnv.Functions.find f prog
  in
  symbol

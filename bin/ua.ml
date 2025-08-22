let files = Queue.create ()
let spec = Arg.align []
let positional_args = Fun.flip Queue.add files
let usage = Printf.sprintf "%s <files>" Sys.argv.(0)
let () = Arg.parse spec positional_args usage

let main file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let ast = Ua0.Pass.Idents.of_string_ast ast in
  ignore ast

let main files = match Queue.peek_opt files with None -> () | Some f -> main f
let () = main files

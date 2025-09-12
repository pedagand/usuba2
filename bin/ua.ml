let () = Printexc.record_backtrace true
let () = Printexc.print_backtrace stdout
let files = Queue.create ()
let passes = Queue.create ()

let spec =
  Arg.align
    [
      ( "-p",
        Arg.Symbol
          ( [ "let-nested" ],
            function
            | "let-nested" -> Queue.add Uat.LetUnest.lu_function passes
            | _ -> () ),
        "<pass> apply pass" );
    ]

let positional_args = Fun.flip Queue.add files
let usage = Printf.sprintf "%s <files>" Sys.argv.(0)
let () = Arg.parse spec positional_args usage

let main file =
  let ast =
    In_channel.with_open_bin file (fun ic ->
        let lexbuf = Lexing.from_channel ic in
        let () = Lexing.set_filename lexbuf file in
        Ua0.Parser.module_ Ua0.Lexer.token lexbuf)
  in
  let ast = Ua0.Pass.Idents.of_string_ast ast in
  let _, uat = Uat.Typecheck.of_ua0_prog ast in
  let uat = Queue.fold (Fun.flip Uat.Util.Prog.apply_pass) uat passes in
  Format.(fprintf std_formatter "%a\n" Uat.Pp.pp_prog uat)

let main files = match Queue.peek_opt files with None -> () | Some f -> main f
let () = main files

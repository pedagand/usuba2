open Alcotest
open Ua0

let x = Ast.TermIdent.fresh "x"
let y = Ast.TermIdent.fresh "y"
let z = Ast.TermIdent.fresh "z"

let env0 =
  let open Uat.Typecheck.Env in
  empty |> add_variable x Ast.Bool |> add_variable y Ast.Bool

let typs = Alcotest.testable Ua0.Pp.pp_ty Util.Ty.equal

let () =
  run "typesynth"
    [
      ( "var",
        [
          test_case "in" `Quick (fun () ->
              check typs "`x` has type `bool` in `env0`"
                (Uat.Typecheck.typesynth env0 (Var x))
                Ua0.Ast.Bool);
          test_case "unbound" `Quick (fun () ->
              match_raises "`z` is not bound in `env0`"
                (function Failure _ -> true | _ -> false)
                (fun () -> ignore (Uat.Typecheck.typesynth env0 (Var z))));
        ] );
    ]

open Alcotest
open Ua0

let alpha = Ast.TyIdent.fresh "'a"
let x = Ast.TermIdent.fresh "x"
let y = Ast.TermIdent.fresh "y"
let z = Ast.TermIdent.fresh "z"
let var_undef = Ast.TermIdent.fresh "_"
let f = Ast.FnIdent.fresh "f"
let _F = Ast.TyDeclIdent.fresh "F"
let _G = Ast.TyDeclIdent.fresh "G"

(* let g = Ast.FnIdent.fresh "g" *)
let fn_undef = Ast.FnIdent.fresh "_"

let ty_f =
  Ast.
    {
      fn_name = f;
      tyvars = Some alpha;
      parameters = [ (x, Ast.Bool); (y, Ast.Var alpha) ];
      return_type = Ast.Var alpha;
      body = Synth (Var y);
    }

let env0 =
  let open Uat.Typecheck.Env in
  empty |> add_variable x Ast.Bool
  |> add_variable y (Ast.Var alpha)
  |> add_variable z Ast.(App { name = _F; ty = App { name = _G; ty = Bool } })
  |> add_function ty_f

let ty = Alcotest.testable Ua0.Pp.pp_ty Util.Ty.equal

let () =
  run "typesynth"
    [
      ( "Var",
        [
          test_case "in-Bool" `Quick (fun () ->
              check ty "`x` has type `bool` in `env0`"
                (Uat.Typecheck.typesynth env0 (Var x))
                Ua0.Ast.Bool);
          test_case "in-Var" `Quick (fun () ->
              check ty "`y` has type `'a` in `env0`"
                (Uat.Typecheck.typesynth env0 (Var y))
                Ua0.Ast.(Var alpha));
          test_case "unbound" `Quick (fun () ->
              match_raises "`_` is not bound in `env0`"
                (function Failure _ -> true | _ -> false)
                (fun _ -> ignore (Uat.Typecheck.typesynth env0 (Var var_undef))));
        ] );
      ( "Fn",
        [
          test_case "in" `Quick (fun () ->
              check ty "`&f` has signatue `('a, 'a) -> 'a` in `env0`"
                (Uat.Typecheck.typesynth env0
                   Ua0.Ast.(Fn { fn_ident = f; tyresolve = None }))
                (Ua0.Ast.Fun
                   {
                     tyvars = ty_f.tyvars;
                     parameters = List.map snd ty_f.parameters;
                     return_type = ty_f.return_type;
                   }));
          test_case "unbound" `Quick (fun () ->
              match_raises "`_` is not bound in `env0`"
                (function Failure _ -> true | _ -> false)
                (fun () ->
                  ignore
                    (Uat.Typecheck.typesynth env0
                       (Ua0.Ast.Fn { fn_ident = fn_undef; tyresolve = None }))));
        ] );
      ( "Lookup",
        [
          test_case "in range" `Quick (fun () ->
              check ty "`z[2]` has type `bool` in `env0`"
                (Uat.Typecheck.typesynth env0
                   (Lookup { lterm = Var z; index = 2 }))
                Ua0.Ast.(App { name = _G; ty = Bool }));
        ] );
    ]

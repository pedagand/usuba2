open Alcotest
open Ua0

let ty = Alcotest.testable Prog.pp_ty Util.Ty.equal
let tydecl = Alcotest.testable Prog.TyDeclIdent.pp Prog.TyDeclIdent.equal
let alpha = Prog.TyIdent.fresh "'a"
let beta = Prog.TyIdent.fresh "'b"
let _F = Prog.TyDeclIdent.fresh "F"
let _G = Prog.TyDeclIdent.fresh "G"
let _H = Prog.TyDeclIdent.fresh "H"

let ty1 =
  let open Scstr in
  Ty.(app _F (app _G (app _H (v alpha))))

let () =
  let open Scstr in
  run "util"
    [
      ( "Ty",
        [
          test_case "to_spine" `Quick (fun () ->
              check
                (pair (list tydecl) ty)
                "to_spine (F (G (H alpha))) = [F; G; H], alpha"
                (Ua0.Util.Ty.to_spine ty1)
                ([ _F; _G; _H ], Ty.(v alpha)));
          test_case "from_spine" `Quick (fun () ->
              check ty "from_spine ([F; G; H], alpha) = F (G (H alpha))"
                (Ua0.Util.Ty.from_spine ([ _F; _G; _H ], Ty.(v alpha)))
                ty1);
          test_case "merge" `Quick (fun () ->
              check
                (pair (list tydecl) (list ty))
                "merge ([F; G; H], [alpha; bool]) ([F], beta)"
                (Ua0.Util.Ty.merge
                   ([ _F; _G; _H ], [ Ty.(v alpha); Ty.bool ])
                   ([ _F ], Ty.(v beta)))
                ( [ _F ],
                  [
                    Ty.(app _G (app _H (v alpha)));
                    Ty.(app _G (app _H bool));
                    Ty.(v beta);
                  ] ));
        ] );
    ]

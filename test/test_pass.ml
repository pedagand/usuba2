module Vars = Set.Make (Ua0.Ident.TyIdent)

let ty = Alcotest.testable Ua0.Ty.pp Ua0.Ty.equal
let f b = Ua0.Ty.S.(fn ~tyvars:b [] [ v b ] (v b))
let f_free b = Ua0.Ty.S.(fn [] [ v b ] (v b))

let test_free message () =
  let a = "'a" in
  let env0, _a = Ua0.Pass.Idents.Env.(add_tyvar a empty) in
  let expected = f_free _a in
  let computed = Ua0.Pass.Idents.ty env0 (f_free a) in
  Alcotest.(check ty) message expected computed

let test_bound message () =
  let a = "'a" in
  let env0, _a = Ua0.Pass.Idents.Env.(add_tyvar a empty) in
  let expected = f @@ Ua0.Ident.TyIdent.fresh "b" in
  let computed = Ua0.Pass.Idents.ty env0 (f a) in
  Alcotest.(check @@ bool) message true
  @@
  let type_var = Ua0.Ty.ty_vars computed in
  let env_vars = Vars.of_list (Ua0.Pass.Idents.Env.tyvars env0) in
  Ua0.Ty.equal expected computed
  && Option.fold
       ~none:true
         (* bound variable shouldn't be inside the bound variable of env *)
       ~some:(fun ty -> not @@ Vars.mem ty env_vars)
       type_var

let () =
  let open Alcotest in
  run "passes"
    [
      ( "Ty",
        [
          test_case "ty" `Quick
            (test_bound "'a shouldn't be the one within the env");
          test_case "ty" `Quick
            (test_free "'a should be the one within the env");
        ] );
    ]

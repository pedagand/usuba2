%{
    open Prog
    open Term
    
    let fail_at start end' fmt = 
        let range = MenhirLib.LexerUtil.range (start, end') in
        Format.kasprintf failwith ( "%s" ^^ fmt ) range
    ;;
%}

%token <string> Identifier
%token <string> TypeVariable
%token <string> TypeCstrIdentifier
%token <int> IntegerLitteral
%token LPARENT RPARENT LBRACE RBRACE LSQBRACE RSQBRACE
%token EQUAL DOT COMMA PIPE CARET EXCLAMATION COLON
%token AND LET LET_PLUS IN REINDEX CIRC FOLD
%token TRUE FALSE BOOL LIFT
%token AMPERSAND MINUS_SUP
%token FUNCTION TYPE TUPLE
%token EOF

%right IN
%left CARET
%left PIPE
%left AMPERSAND
%right EXCLAMATION


%start module_

%type <Prog.pre_prog> module_

%%


%inline parenthesis(X):
    | delimited(LPARENT, X, RPARENT) { $1 }


%inline bracketed(X):
    | delimited(LBRACE, X, RBRACE) { $1 }

%inline sqrbracketed(X):
    | delimited(LSQBRACE, X, RSQBRACE) { $1 }
    
%inline splitted(lhs, sep, rhs):
    | lhs=lhs sep rhs=rhs { lhs, rhs }



module_:
    | list(node) EOF { $1 }
    | error {
        fail_at $startpos $endpos "parser error"
    }
    
node:
    | type_decl { Prog.NTy $1 }
    | fn_decl { Prog.NFun $1 }


type_decl:
    | TYPE name=TypeCstrIdentifier EQUAL 
        TUPLE size=sqrbracketed(IntegerLitteral)  {
        { tyvar = "a"; name; size }
    }

fn_decl:
    | FUNCTION fn_name=Identifier
        tyvars=option(sqrbracketed(TypeVariable)) parameters=parenthesis(separated_list(COMMA, splitted(Identifier, COLON, ty)))
        return_type=ty EQUAL body=cterm
    { 
        let args = List.map fst parameters in
        let parameters = List.map snd parameters in
        {fn_name; signature = { tyvars; parameters; return_type}; args; body }
    }
    
ty:
    | name=TypeCstrIdentifier ty=ty {
        App {name; ty}
    }
    | TypeVariable { Var $1 }
    | BOOL { Ty.Bool }
    | FUNCTION signature {
        Ty.Fun $2
    }
    
%inline signature:
    | tyvars=option(sqrbracketed(TypeVariable)) 
        parameters=parenthesis(separated_list(COMMA, ty)) MINUS_SUP 
        return_type=ty {
        {Ty.tyvars; parameters; return_type}
    }
    
%inline fn_identifier:
    | fn_name=Identifier DOT ty_resolve=option(sqrbracketed(ty))  { 
        fn_name, ty_resolve 
    }
    
%inline identifier_typed:
    | splitted(Identifier, COLON, ty) { $1 }
    
sterm:
    | Identifier { Var $1 } 
    | AMPERSAND fn_ident=Identifier { Fn {fn_ident} }
    | lterm=sterm index=sqrbracketed(IntegerLitteral) {
        Lookup { lterm; index}
    }
    | REINDEX ls=sqrbracketed(splitted(
        nonempty_list(TypeCstrIdentifier), PIPE,
        nonempty_list(TypeCstrIdentifier)
    )) lterm=parenthesis(sterm) {
        let (lhs, rhs) = ls in
        Reindex {lhs; rhs; lterm}
    }
    | CIRC lterm=parenthesis(sterm) {
        Circ lterm
    }
    | LIFT tys=sqrbracketed(nonempty_list(TypeCstrIdentifier)) 
        func=parenthesis(sterm) {
        Lift {tys; func}
    }
    | fn=fn_identifier args=parenthesis(separated_list(COMMA, cterm)) {
        let fn_name, ty_resolve = fn in
        FnCall {fn_name = Either.Left fn_name; ty_resolve; args}
    }
    | operator {
        Operator $1
    }
    | c_ty=parenthesis(splitted(cterm, COLON, ty)) {
        let cterm, ty = c_ty in
        Ann (cterm, ty)
    }
    | FOLD i=sqrbracketed(IntegerLitteral) 
        fi=parenthesis(fi=fn_identifier const_args=option(parenthesis(separated_list(COMMA, cterm))) {fi, const_args} ) 
        args10=parenthesis(splitted(sterm, COMMA, sterm))
    {
        let acc, lterm = args10 in
        let (fn_name, ty_resolve), const_args = fi in
        let const_args = Option.fold ~none:[] ~some:Fun.id const_args in
        List.init i Fun.id |> List.fold_left (fun acc i -> 
            let args = const_args @ (Synth acc) :: (Synth (Lookup {lterm; index = i})) :: [] in
            FnCall {fn_name = Either.Left fn_name; ty_resolve; args }
        ) acc 
    }
    
cterm:
    | FALSE { False }
    | TRUE { True }
    | ty=TypeCstrIdentifier terms=sqrbracketed(separated_nonempty_list(COMMA, cterm)) {
      Constructor { ty; terms}
    }
    | LET variable=Identifier EQUAL term=sterm IN k=cterm {
        Let {variable; term; k}
    }
    | LET ty_var=identifier_typed EQUAL cterm=cterm IN k=cterm {
        let variable, ty = ty_var in 
        Let {variable; term = Ann(cterm, ty); k }
    }
    | LET_PLUS variable=Identifier EQUAL lterm=sterm 
        ands=list(preceded(AND, splitted(Identifier, EQUAL, sterm))) 
        IN term=cterm {
            LetPlus { variable; lterm; ands; term }
    }
    | sterm { Synth $1 }
    
%inline operator:
    | EXCLAMATION t=cterm { Operator.Not t }
    | lhs=cterm PIPE rhs=cterm { Operator.Or (lhs, rhs) }
    | lhs=cterm AMPERSAND rhs=cterm { Operator.And (lhs, rhs) }
    | lhs=cterm CARET rhs=cterm { Operator.Xor (lhs, rhs) }
    
/*term:
    | TRUE { TTrue }
    | FALSE { TFalse }
   
    | AMPERSAND fn_ident=Identifier { TFn {fn_ident; tyresolve = None} }
    | LET variable=Identifier EQUAL term=term IN k=term {
        TLet {variable; term; k}
    }
    | lterm=lterm index=sqrbracketed(IntegerLitteral) {
        TLookup { lterm; index}
    }
    | FOLD i=sqrbracketed(IntegerLitteral) 
        fi=parenthesis(fi=fn_identifier const_args=option(parenthesis(separated_list(COMMA, term))) {fi, const_args} ) 
        args10=parenthesis(splitted(term, COMMA, lterm))
    {
        let acc, lterm = args10 in
        let (fn_name, ty_resolve), const_args = fi in
        let const_args = Option.fold ~none:[] ~some:Fun.id const_args in
        List.init i (Fun.id) |> List.fold_left (fun acc i -> 
            let args = const_args @ acc :: (TLookup {lterm; index = i}) :: [] in
            FnCall {fn_name = Either.Left fn_name; ty_resolve; args }
        ) acc 
    }
    | HASH lterm=lterm { TThunk {lterm} }
    | fn=fn_identifier args=parenthesis(separated_list(COMMA, term)) {
        let fn_name, ty_resolve = fn in
        FnCall {fn_name = Either.Left fn_name; ty_resolve; args}
    }
    | parenthesis(term) { $1 }
    | operator {
        Operator $1
    }*/
    


/*lterm:
    | LET_PLUS variable=Identifier EQUAL lterm=lterm 
        ands=list(preceded(AND, splitted(Identifier, EQUAL, lterm))) 
        IN term=term {
            LLetPlus { variable; lterm; ands; term }
        }
    | ty=TypeCstrIdentifier terms=parenthesis(separated_nonempty_list(COMMA, term)) {
        LConstructor { ty; terms }
    }
    | RANGE ty=loption(sqrbracketed(list(TypeCstrIdentifier))) term=parenthesis(term) {
        LRange {ty; term}
    }
    | REINDEX ls=sqrbracketed(splitted(
        nonempty_list(TypeCstrIdentifier), PIPE,
        nonempty_list(TypeCstrIdentifier)
    )) lterm=parenthesis(lterm) {
        let (lhs, rhs) = ls in
        LReindex {lhs; rhs; lterm}
    }
    | CIRC lterm=parenthesis(lterm) {
        LCirc lterm
    }
    | parenthesis(lterm) { $1 }*/
    

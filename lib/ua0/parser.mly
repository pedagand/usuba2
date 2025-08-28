%{
    open Ast
%}

%token <string> Identifier
%token <string> TypeVariable
%token <string> TypeCstrIdentifier
%token <int> IntegerLitteral
%token LPARENT RPARENT LBRACE RBRACE LSQBRACE RSQBRACE
%token EQUAL DOT COMMA PIPE HASH CARET EXCLAMATION COLON
%token AND LET LET_PLUS IN RANGE REINDEX CIRC FOLD
%token TRUE FALSE BOOL
%token AMPERSAND MINUS_SUP
%token FUNCTION TYPE TUPLE
%token EOF

%right IN
%left CARET
%left PIPE
%left AMPERSAND
%right EXCLAMATION


%start module_

%type <Ast.module_ast> module_

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
    
node:
    | type_decl { Ast.NTy $1 }
    | fn_decl { Ast.NFun $1 }


type_decl:
    | TYPE name=TypeCstrIdentifier tyvar=TypeVariable EQUAL 
        TUPLE size=sqrbracketed(IntegerLitteral)  {
        { tyvar; name; size }
    }

fn_decl:
    | FUNCTION tyvars=option(terminated(TypeVariable, DOT))
        fn_name=Identifier parameters=parenthesis(separated_list(COMMA, splitted(Identifier, COLON, ty)))
        return_type=ty EQUAL body=term
    { 
        {tyvars; fn_name; parameters; return_type; body }
    }
    
ty:
    | name=TypeCstrIdentifier ty=ty {
        TyApp {name; ty}
    }
    | TypeVariable { TyVar $1 }
    | BOOL { TyBool }
    | FUNCTION signature {
        TyFun $2
    }
    
%inline signature:
    | tyvars=option(sqrbracketed(TypeVariable)) 
        parameters=parenthesis(separated_list(COMMA, ty)) MINUS_SUP 
        return_type=ty {
        {tyvars; parameters; return_type}
    }
    
%inline fn_identifier:
    | fn_name=Identifier DOT ty_resolve=option(sqrbracketed(ty))  { 
        fn_name, ty_resolve 
    }
    
term:
    | TRUE { TTrue }
    | FALSE { TFalse }
    | Identifier { TVar $1 }
    | AMPERSAND fn_ident=Identifier { TFn {fn_ident; tyresolve = None} }
    | LET variable=Identifier EQUAL term=term IN k=term {
        TLet {variable; term; k}
    }
    | lterm=lterm index=sqrbracketed(IntegerLitteral) {
        TLookup { lterm; index}
    }
    | FOLD i=sqrbracketed(IntegerLitteral) fi=parenthesis(fn_identifier) LPARENT 
        args10=splitted(term, COMMA, lterm) args=list(preceded(COMMA, term))
    RPARENT {
        let acc, lterm = args10 in
        let fn_name, ty_resolve = fi in
        List.init i (Fun.id) |> List.fold_left (fun acc i -> 
            let args = acc :: (TLookup {lterm; index = i}) :: args in
            TFnCall {fn_name = Either.Left fn_name; ty_resolve; args }
        ) acc 
    }
    | HASH lterm=lterm { TThunk {lterm} }
    | fn=fn_identifier args=parenthesis(separated_list(COMMA, term)) {
        let fn_name, ty_resolve = fn in
        TFnCall {fn_name = Either.Left fn_name; ty_resolve; args}
    }
    | parenthesis(term) { $1 }
    | operator {
        TOperator $1
    }
    
%inline operator:
    | EXCLAMATION term { ONot $2 }
    | lhs=term PIPE rhs=term { OOr (lhs, rhs) }
    | lhs=term AMPERSAND rhs=term { OAnd (lhs, rhs) }
    | lhs=term CARET rhs=term { OXor (lhs, rhs) }

lterm:
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
    | parenthesis(lterm) { $1 }
    

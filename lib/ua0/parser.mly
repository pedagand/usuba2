%{

%}

%token <string> Identifier
%token <string> TypeVariable
%token <string> TypeCstrIdentifier
%token <int> IntegerLitteral
%token LPARENT RPARENT LBRACE RBRACE LSQBRACE RSQBRACE
%token EQUAL DOT COMMA
%token LET RANGE REINDEX
%token TRUE FALSE
%token AMPERSAND
%token FUNCTION TYPE TUPLE
%token EOF


%start module_

%type <Ast.node list> module_

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
    | type_decl { failwith "" }
    | fn_decl { failwith "" }


type_decl:
    | TYPE typecst=TypeCstrIdentifier EQUAL 
        TUPLE size=sqrbracketed(IntegerLitteral) tyvars=TypeVariable {
        let () = ignore (typecst, size, tyvars) in
        failwith ""
    }

fn_decl:
    | FUNCTION tyvar=option(terminated(TypeVariable, DOT))
        fn_name=Identifier params=parenthesis(separated_list(COMMA, splitted(Identifier, COMMA, ty)))
        return_type=ty EQUAL term
    { 
        let () = ignore (tyvar, fn_name, params, return_type) in
        failwith "" 
    }
    
ty:
    | { failwith "" }
term:
    | TRUE 
    | FALSE
    { failwith "" }

lterm:
    | { failwith "" }
    

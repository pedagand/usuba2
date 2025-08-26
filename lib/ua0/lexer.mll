{
    open Parser
    open Lexing
    
    let keywords = [
        ("and", AND); ("bool", BOOL); ("circ", CIRC); ("false", FALSE); 
        ("fn", FUNCTION); ("in", IN); ("let", LET);
        ("range", RANGE);  ("reindex", REINDEX); ("tuple", TUPLE); 
        ("true", TRUE); ("type", TYPE)
    ]
    
    let keywords = Hashtbl.of_seq @@ List.to_seq keywords
    
    let fail_at lexbuf fmt = 
    let start = lexbuf.lex_start_p in
    let end' = lexbuf.lex_curr_p in
    let range =  MenhirLib.LexerUtil.range (start, end') in
    Format.kasprintf failwith ( "%s" ^^ fmt ) range

}

let digit = ['0'-'9']
let loLetter = ['a'-'z']
let upLetter = ['A'-'Z']

let identifiant = (loLetter | '_') (loLetter | upLetter | digit | "_")*
let lower_identifier = loLetter+
let type_cstr_identifier = (upLetter) (loLetter | digit | "_" | upLetter )*

let decimal_integer = digit (digit | '_')*
let hex_integer = '0' ('x' | 'X') (digit | ['a'-'f'] | ['A'-'F']) (digit | ['a'-'f'] | ['A'-'F'] | '_')*
let octal_intger = '0' ('o' | 'O') (['0'-'7']) (['0'-'7'] | '_')*
let binary_integer = '0' ('b' | 'B') ('0' | '1') ('0' | '1' | '_')*
let number = decimal_integer | hex_integer | octal_intger | binary_integer

let newline = ('\010' | '\013' | "\013\010")
let blank   = [' ' '\009' '\012']

rule token = parse
| newline {
    let () = Lexing.new_line lexbuf in
    token lexbuf
}
| blank+ { token lexbuf }
| '\'' (lower_identifier as s) { 
    TypeVariable s
}
| (number as n) {
    IntegerLitteral(int_of_string n)
}
| "let+" { LET_PLUS }
| "(" { LPARENT }
| ")" { RPARENT }
| "{" { LBRACE }
| "}" { RBRACE }
| "[" { LSQBRACE }
| "]" { RSQBRACE }
| "&" { AMPERSAND }
| "," { COMMA }
| "=" { EQUAL }
| "." { DOT }
| ":" { COLON }
| "#" { HASH }
| "|" { PIPE }
| "^"  { CARET }
| "!"  { EXCLAMATION }
| "->" { MINUS_SUP }
| "//" { single_line_comment lexbuf }
| type_cstr_identifier as s {
    TypeCstrIdentifier s
}
| identifiant as s {
    try 
        Hashtbl.find keywords s
    with Not_found -> Identifier s
}
| _ as c {
    fail_at lexbuf "invalid char : %c" c
}
| eof { EOF }

and single_line_comment = parse
| newline {  
    let () = Lexing.new_line lexbuf in
    token lexbuf 
}
| _ { single_line_comment lexbuf}
| eof { EOF }

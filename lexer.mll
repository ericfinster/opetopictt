{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse
  | "U"     { TYPE }
  | "fst"   { FST }
  | "snd"   { SND }
  | "let"   { LET }
  | "def"   { DEF }
  | "="     { EQUAL }
  | "("     { LPAR }
  | ")"     { RPAR }
  | ":"     { COLON }
  | "->"    { ARROW }
  | "*"     { STAR }
  | "\\"    { LAMBDA }
  | "."     { DOT }
  | ","     { COMMA }
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''{''}''/'',''\'']* as str) { IDENT str }
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }

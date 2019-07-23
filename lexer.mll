{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse

  (* Type Universes *)
  | "U"     { TYPE }
  | "O"     { OTYPE }

  (* Opetopic Type Structure *) 
  | "Frm"   { FRAME }
  | "Cell"  { CELL }
  | "Tree"  { TREE }
  | "Pos"   { POS }
  | "Typ"   { TYP }
  | "Inh"   { INH }

  (* Opetope constructors *)
  | "mu"    { MU }
  | "eta"   { ETA }
  | "nd"    { ND }
  | "lf"    { LF }
  | "ob"    { OB }

  (* Frame Construtors *)
  | "<>"    { FRMEMPTY }
  | "||"    { FRMEXT }
  | ">>"    { FRMHD }

  (* Source Eliminators *)
  | "ob-pos-elim"  { OBPOSELIM }
  | "lf-pos-elim"  { LFPOSELIM }
  | "nd-pos-elim"  { NDPOSELIM }
  
  (* Language Constructs *)
  | "let"   { LET }
  | "def"   { DEF }
  | "fst"   { FST }
  | "snd"   { SND }
  | "="     { EQUAL }
  | "("     { LPAR }
  | ")"     { RPAR }
  | ":"     { COLON }
  | "->"    { ARROW }
  | "*"     { STAR }
  | "\\"    { LAMBDA }
  | "."     { DOT }
  | ","     { COMMA }

  (* Identifiers *)
  | (['a'-'z''A'-'Z''0'-'9']['-''+''a'-'z''A'-'Z''0'-'9''_''@''{''}''/'',''\'']* as str) { IDENT str }

  (* Comment and layout structure *)
  | space+ { token lexbuf }
  | "#"[^'\n']* { token lexbuf }
  | "\n" { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }

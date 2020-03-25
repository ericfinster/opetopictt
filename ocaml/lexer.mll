{
  open Parser
}

let space = ' ' | '\t' | '\r'

rule token = parse

  (* Type Universes *)
  | "U"     { TYPE }
  | "O"     { OTYPE }

  (* Basic Opetopic Structure *) 
  | "Frm"   { FRAME }
  | "Cell"  { CELL }
  | "Tree"  { TREE }
  | "Pos"   { POS }
  | "Typ"   { TYP }
  | "Inh"   { INH }

  (* Frame construtors *)
  | "<>"    { FRMEMPTY }
  | "||"    { FRMEXT }
  | ">>"    { FRMHD }

  (* Opetopic constructors *)
  | "mu"    { MU }
  | "eta"   { ETA }
  | "gamma" { GAMMA }
  | "nd"    { ND }
  | "lf"    { LF }
  | "ob"    { OB }

  (* Position constructors *)
  | "ob-pos"          { OBPOS }
  | "nd-pos-here"     { NDPOSHERE }
  | "nd-pos-there"    { NDPOSTHERE }
  | "mu-pos"          { MUPOS }
  | "eta-pos"         { ETAPOS }
  | "gamma-pos-inl"   { GAMMAPOSINL }
  | "gamma-pos-inr"   { GAMMAPOSINR }
  
  (* Position eliminators *)
  | "ob-pos-elim"     { OBPOSELIM }
  | "lf-pos-elim"     { LFPOSELIM }
  | "nd-pos-elim"     { NDPOSELIM }
  | "eta-pos-elim"    { ETAPOSELIM }
  | "mu-pos-fst"      { MUPOSFST }
  | "mu-pos-snd"      { MUPOSSND }
  | "gamma-pos-elim"  { GAMMAPOSELIM }
  
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

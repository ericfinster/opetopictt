(*****************************************************************************)
(*                                                                           *)
(*                                   Lexer                                   *)
(*                                                                           *)
(*****************************************************************************)

open Parser

let space = [%sedlex.regexp? ' ' | '\t' | '\r']
let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]

(* lower lambda is reserved ... *)
let greek_lower = [%sedlex.regexp? 0x3B1 .. 0x3BA | 0x3BC .. 0x3C9]
let greek_upper = [%sedlex.regexp? 0x391 .. 0x3A9]
let subscripts = [%sedlex.regexp? 0x2080 .. 0x208E | 0x2090 .. 0x209C ]

let letter = [%sedlex.regexp? 'a'..'z'|'A'..'Z'|greek_lower|greek_upper]
let ident = [%sedlex.regexp? letter, Star (letter | subscripts | '_' | '-' | digit)]

let arrow = [%sedlex.regexp? 0x2192 ] 
let arrowpos = [%sedlex.regexp? 0x2192 , 0x209A ] 
let timespos = [%sedlex.regexp? 0xD7 , 0x209A ] 
let unitpos = [%sedlex.regexp? 0x22A4 , 0x209A ]
let emptypos = [%sedlex.regexp? 0x22A5 , 0x209A ]
let sumpos = [%sedlex.regexp? 0x2294 , 0x209A ]
let ttpos = [%sedlex.regexp? "tt" , 0x209A ]
let inlpos = [%sedlex.regexp? "inl" , 0x209A ]
let inrpos = [%sedlex.regexp? "inr" , 0x209A ]
let lambdapos = [%sedlex.regexp? 0x3BB , 0x209A ]

let topelim = [%sedlex.regexp? 0x22A4 , "-elim" ]
let botelim = [%sedlex.regexp? 0x22A5 , "-elim" ]
let sumelim = [%sedlex.regexp? 0x2294 , "-elim" ]
let sigelim = [%sedlex.regexp? 0xD7 , "-elim" ]

exception Lexing_error of ((int * int) option * string)

let get_lexing_position lexbuf =
  let (p,_) = Sedlexing.lexing_positions lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let lexing_error lexbuf msg =
  let line, column = get_lexing_position lexbuf in
  raise (Lexing_error (Some (line, column), msg))

let rec token buf =
  match%sedlex buf with

  | "let"        -> LET
  | "->"         -> ARROW
  | arrow        -> ARROW
  | arrowpos     -> ARROWPOS
  | timespos     -> TIMESPOS
  | "@"          -> APPPOS

  | unitpos      -> UNITPOS
  | emptypos     -> EMPTYPOS
  | sumpos       -> SUM
  | ttpos        -> TTPOS
  | inlpos       -> INLPOS
  | inrpos       -> INRPOS
  | lambdapos    -> LAMBDAPOS 

  | topelim      -> TOPELIM
  | botelim      -> BOTELIM
  | sumelim      -> SUMELIM 
  | sigelim      -> SIGELIM

  | "("          -> LPAR
  | ")"          -> RPAR
  | ":"          -> COLON
  | ","          -> COMMA
  | "="          -> EQUAL
  | "."          -> DOT
  | "\\"         -> LAMBDA
  | 0x03bb       -> LAMBDA
  | "Pos"        -> POS
  | "El"         -> EL 
  | "U"          -> TYPE

  | "|"          -> VBAR
  | "normalize"  -> NORMALIZE 
  | "infer"      -> INFER

  | ident -> IDENT (Sedlexing.Utf8.lexeme buf)

  | Plus space -> token buf
  | "#",Star (Compl '\n') -> token buf
  | "\n" -> token buf (* Sedlexing.new_line buf ; token buf  *)
  | eof -> EOF
  | _ -> lexing_error buf (Printf.sprintf "Unexpected character: %s" (Sedlexing.Utf8.lexeme buf))

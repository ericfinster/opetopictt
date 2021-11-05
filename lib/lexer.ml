(*****************************************************************************)
(*                                                                           *)
(*                                   Lexer                                   *)
(*                                                                           *)
(*****************************************************************************)

open Syntax
open Parser

let space = [%sedlex.regexp? ' ' | '\t' | '\r']
let digit = [%sedlex.regexp? '0'..'9']
let number = [%sedlex.regexp? Plus digit]

(* lower lambda is reserved ... *)
let upper = [%sedlex.regexp? 'A'..'Z']
let lower = [%sedlex.regexp? 'a'..'z']
let greek_lower = [%sedlex.regexp? 0x3B1 .. 0x3BA | 0x3BC .. 0x3C9]
let greek_upper = [%sedlex.regexp? 0x391 .. 0x3A9]
let subscripts = [%sedlex.regexp? 0x2080 .. 0x208E | 0x2090 .. 0x209C ]

let letter = [%sedlex.regexp? lower|upper|greek_lower|greek_upper]
let ident = [%sedlex.regexp? letter, Star (letter | subscripts | '_' | '-' | digit)]

let module_name = [%sedlex.regexp? upper, Star(lower | upper)]

exception Lexing_error of ((int * int) option * string)

let get_lexing_position lexbuf =
  let (p,_) = Sedlexing.lexing_positions lexbuf in
  let line_number = p.Lexing.pos_lnum in
  let column = p.Lexing.pos_cnum - p.Lexing.pos_bol + 1 in
  (line_number, column)

let lexing_error lexbuf msg =
  let line, column = get_lexing_position lexbuf in
  raise (Lexing_error (Some (line, column), msg))

let rec qname buf =
  match%sedlex buf with
  | module_name , '.' ->
    let mndot = Sedlexing.Utf8.lexeme buf in
    let mn = String.sub mndot 0 (String.length mndot - 1) in 
    let qn = qname buf in 
    Qual (mn,qn)
  | ident -> Name (Sedlexing.Utf8.lexeme buf)
  | _ -> lexing_error buf (Printf.sprintf "Unexpected character: %s" (Sedlexing.Utf8.lexeme buf))

let rec token buf =
  match%sedlex buf with
  
  | "import"     -> IMPORT
  | "shape"      -> SHAPE
  | "def"        -> DEF 
  | "let"        -> LET
  | "in"         -> IN
  | "module"     -> MODULE
  | "where"      -> WHERE
  | "end"        -> END
  | 0x2192       -> ARROW
  | "->"         -> ARROW
  | "("          -> LPAR
  | ")"          -> RPAR
  | "{"          -> LBR
  | "}"          -> RBR
  | "["          -> LBRKT
  | "]"          -> RBRKT
  | "@"          -> AT
  | ":"          -> COLON
  | "="          -> EQUAL
  | "\\"         -> LAMBDA
  | 0x03bb       -> LAMBDA
  | "U"          -> TYPE
  | "lf"         -> LF
  | "nd"         -> ND
  | "tt"         -> UNIT
  | "|"          -> VBAR
  | 0xd7         -> TIMES
  | ","          -> COMMA
  | "fst"        -> FST
  | "snd"        -> SND

  (* tokens for commands *)
  | "quit"       -> QUIT
  | "infer"      -> INFER
  | "normalize"  -> NORMALIZE
  | "assume"     -> ASSUME
  | ";"          -> ENDCMD 

  | ident -> IDENT (Sedlexing.Utf8.lexeme buf)
  | module_name , '.' ->
    let mndot = Sedlexing.Utf8.lexeme buf in
    let mn = String.sub mndot 0 (String.length mndot - 1) in 
    let qn = qname buf in 
    QNAME (Qual (mn,qn))
               
  | Plus space -> token buf
  | "#",Star (Compl '\n') -> token buf
  | "\n" -> token buf 
  | eof -> EOF
  | _ -> lexing_error buf (Printf.sprintf "Unexpected character: %s" (Sedlexing.Utf8.lexeme buf))

(*****************************************************************************)
(*                                                                           *)
(*                                 Commands                                  *)
(*                                                                           *)
(*****************************************************************************)

open Expr
open Syntax 
  
type cmd =
  | Quit
  | Nop 
  | Infer of expr
  | Normalize of expr
  | Assume of expr tele
  | Load of name 
  | Let of name * expr option * expr 

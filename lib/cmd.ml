(*****************************************************************************)
(*                                                                           *)
(*                                 Commands                                  *)
(*                                                                           *)
(*****************************************************************************)

open Expr
open Syntax 
  
type cmd =
  | Quit 
  | Infer of expr
  | Normalize of expr
  | Assume of expr tele


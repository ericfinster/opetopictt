(*****************************************************************************)
(*                                   Syntax                                  *)
(*****************************************************************************)

open Base

type intmap = (int,string,Int.comparator_witness) Map.t

(* Define a global meta-variable context *)
let metacontext : intmap ref =
  ref (Map.empty (module Int))

type metavar = int
  
(*****************************************************************************)
(*                                 Raw Syntax                                *)
(*****************************************************************************)

type name = string
  
type expr =
  | VarE of name
  | LamE of name * expr
  | AppE of expr * expr
  | PiE of name * expr * expr
  | TypE
  | HoleE

(*****************************************************************************)
(*                              Internal Syntax                              *)
(*****************************************************************************)

type idx = int
  
type term =
  | VarT of idx
  | LamT of name * term
  | AppT of term * term
  | PiT of name * term * term
  | TypT
  | MetaT of metavar

(*****************************************************************************)
(*                                   Values                                  *)
(*****************************************************************************)

type lvl = int

type value =
  | FlexV of metavar * spine
  | RigidV of lvl * spine
  | LamV of name * closure
  | PiV of name * value * closure 
  | TypV 

and env = value list
and spine = value list 

and closure =
  | Closure of env * term



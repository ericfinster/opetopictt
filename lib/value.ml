(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Syntax

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  (* Primitives *)
  | FlexV of mvar * spine   (* A term stuck because head is meta *)
  | RigidV of lvl * spine   (* A term stuck because head is bound variable *)
  | TopV of name * spine * value
  | LamV of name * icit * (value -> value) 
  | PiV of name * icit * value * (value -> value) 
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value * icit

let varV k = RigidV (k,EmpSp)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_value ppf v =
  match v with
  | FlexV (m,sp) ->
    pf ppf "?%d %a" m pp_spine sp
  | RigidV (i,EmpSp) -> pf ppf "%d" i
  | RigidV (i,sp) -> pf ppf "%d %a" i pp_spine sp
  | TopV (nm,sp,_) ->
    pf ppf "%s %a" nm pp_spine sp
  | LamV (nm,Expl,_) ->
    pf ppf "\\%s.<closure>" nm 
  | LamV (nm,Impl,_) ->
    pf ppf "\\{%s}.<closue>" nm 
  | PiV (nm,Expl,a,_) ->
    pf ppf "(%s : %a) -> <closure>" nm
      pp_value a 
  | PiV (nm,Impl,a,_) ->
    pf ppf "{%s : %a} -> <closure>" nm
      pp_value a 
  | TypV -> pf ppf "U"
    
and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v,Expl) ->
    pf ppf "%a %a" pp_spine sp' pp_value v
  | AppSp (sp',v,Impl) ->
    pf ppf "%a {%a}" pp_spine sp' pp_value v


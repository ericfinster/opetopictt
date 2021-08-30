(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Syntax

open Opetopes.Complex
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  | RigidV of lvl * spine 
  | TopV of name * spine * value

  (* Pi Types *)
  | LamV of name * (value -> value) 
  | PiV of name * value * (value -> value)

  (* Cell Types *)
  | CellV of value tele * value * value dep_term cmplx

  (* The Universe *)
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value 

let varV k = RigidV (k,EmpSp)

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_value ppf v =
  match v with
  | RigidV (i,EmpSp) -> pf ppf "%d" i
  | RigidV (i,sp) -> pf ppf "%d %a" i pp_spine sp
  | TopV (nm,sp,_) ->
    pf ppf "%s %a" nm pp_spine sp
  | LamV (nm,_) ->
    pf ppf "\\%s.<closure>" nm 
  | PiV (nm,a,_) ->
    pf ppf "(%s : %a) -> <closure>" nm
      pp_value a
  | CellV _ -> pf ppf "cellvalue"
  | TypV -> pf ppf "U"
    
and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v) ->
    pf ppf "%a %a" pp_spine sp' pp_value v


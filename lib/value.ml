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

  (* Sigma Types *) 
  | PairV of value * value
  | SigV of name * value * (value -> value)

  (* Cell Types *)
  | CellV of value tele * value * value dep_term cmplx
  | CompV of value tele * value * value dep_term cmplx
  | FillV of value tele * value * value dep_term cmplx
  | KanElimV of value tele * value * value dep_term cmplx * 
                   value * value * value * value * spine 

  (* The Universe *)
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value
  | FstSp of spine
  | SndSp of spine 

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
  | PairV (u,v) ->
    pf ppf "%a , %a" pp_value u pp_value v
  | SigV (nm,a,_) ->
    pf ppf "(%s : %a) \u{d7} <closure>" nm
      pp_value a 
  | CellV _ -> pf ppf "cell value"
  | CompV _ -> pf ppf "comp value"
  | FillV _ -> pf ppf "fill value"
  | KanElimV _ -> pf ppf "kan elim value"
  | TypV -> pf ppf "U"
    
and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v) ->
    pf ppf "%a %a" pp_spine sp' pp_value v
  | FstSp sp' ->
    pf ppf "fst %a" pp_spine sp'
  | SndSp sp' ->
    pf ppf "snd %a" pp_spine sp' 


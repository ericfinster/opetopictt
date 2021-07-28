(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Suite
open Syntax
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  (* Primitives *)
  | RigidV of lvl * spine  
  | TopV of name * spine * value
  | LamV of name * (value -> value) 
  | PiV of name * value * (value -> value) 
  | TypV
    
  | PosV
  | ElV of value
      
  | PosUnitV
  | PosEmptyV
  | PosSumV of value * value
  | PosSigV of name * value * (value -> value)

  | PosTtV
  | PosInlV of value
  | PosInrV of value
  | PosPairV of value * value

  | PosPiV of name * value * (value -> value)
  | PosLamV of name * (value -> value) 

and spine =
  | EmpSp
  | AppSp of spine * value 

and top_env = (name * value) suite
and loc_env = value suite

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
    pf ppf "(%s : %a) -> <closure>"
      nm pp_value a 
  | TypV -> pf ppf "U"
              
  | PosV -> pf ppf "Pos"
  | ElV v -> pf ppf "El %a" pp_value v

  | PosUnitV -> pf ppf "\u{22A4}\u{209A}"
  | PosEmptyV -> pf ppf "\u{22A5}\u{209A}"
  | PosSumV (l, r) ->
    pf ppf "%a \u{2294}\u{209A} %a" pp_value l pp_value r 
  | PosSigV (nm, a, _) ->
    pf ppf "(%s : %a)@, \u{D7}\u{209A} <closure>" nm pp_value a 
  | PosTtV -> pf ppf "tt\u{209A}"
  | PosInlV u -> pf ppf "inl\u{209A} %a" pp_value u 
  | PosInrV v -> pf ppf "inr\u{209A} %a" pp_value v
  | PosPairV (u,v) ->
    pf ppf "%a , %a" pp_value u pp_value v
      
  | PosPiV (nm,a,_) ->
    pf ppf "(%s : %a)@, \u{2192}\u{209A} <closure>" nm pp_value a 
  | PosLamV (nm,_) ->
    pf ppf "\u{03BB}\u{209A} %s, <closure>" nm


and pp_spine ppf sp =
  match sp with
  | EmpSp -> ()
  | AppSp (sp',v) ->
    pf ppf "%a %a" pp_spine sp' pp_value v

let pp_top_env = hovbox (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
let pp_loc_env = hovbox (pp_suite ~sep:comma pp_value)

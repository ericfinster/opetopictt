(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Syntax
open Suite
open Expr

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

  (* Opetopic Reflexivity *) 
  (* | ReflV of value * string cmplx *)
               
  (* The Universe *)
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value
  | FstSp of spine
  | SndSp of spine
  | ReflSp of spine * string cmplx 

let varV k = RigidV (k,EmpSp)

(* Take the non-dependent product of a list of type values *)
let rec prod tys =
  match tys with
  | [] -> failwith "empty product"
  | ty :: [] -> ty
  | ty :: tys' -> 
    SigV ("",ty,fun _ -> prod tys')

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_value ppf v =
  match v with
  
  | RigidV (i,sp) ->
    pf ppf "%a" (pp_spine Fmt.int i) sp
  | TopV (nm,sp,_) ->
    let pp_nm ppf' n = pf ppf' "%s" n in 
    pf ppf "%a" (pp_spine pp_nm nm) sp
      
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

  (* | ReflV (v',pi) -> 
   *   let open Opetopes.Idt.IdtConv in 
   *   pf ppf "[ @[%a] @ @[ %a ] ]"
   *     pp_value v' (pp_suite ~sep:(any "@,| ")
   *      (pp_tr_expr Fmt.string)) (of_cmplx pi)  *)

  | TypV -> pf ppf "U"
    
and pp_spine : 'a. 'a Fmt.t -> 'a -> spine Fmt.t =
  fun pp_a a ppf sp -> 
  match sp with
  | EmpSp ->
    pf ppf "%a" pp_a a
  | AppSp (sp',v) ->
    pf ppf "%a %a" (pp_spine pp_a a) sp' pp_value v
  | FstSp sp' ->
    pf ppf "fst %a" (pp_spine pp_a a) sp' 
  | SndSp sp' ->
    pf ppf "snd %a" (pp_spine pp_a a) sp'
  | ReflSp (sp',pi) -> 
    let open Opetopes.Idt.IdtConv in 
    pf ppf "[ @[%a] @ @[ %a ] ]"
      (pp_spine pp_a a) sp' (pp_suite ~sep:(any "@,| ")
       (pp_tr_expr Fmt.string)) (of_cmplx pi) 

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
  | CompUV of value tele * value * value dep_term cmplx * value * value
  | FillUV of value tele * value * value dep_term cmplx * value * value 

  (* The Universe *)
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value
  | FstSp of spine
  | SndSp of spine 

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

  | CellV (tl,ty,c) ->
    pp_value_cell_desc ppf (tl,ty,c)
  | CompV (tl,ty,c) ->
    pf ppf "comp %a" pp_value_cell_desc (tl,ty,c)
  | FillV (tl,ty,c) ->
    pf ppf "fill %a" pp_value_cell_desc (tl,ty,c)
  | CompUV (tl,ty,k,c,f) ->
    pf ppf "comp-unique %a %a %a" pp_value_cell_desc (tl,ty,k)
      pp_value c pp_value f
  | FillUV (tl,ty,k,c,f) ->
    pf ppf "fill-unique %a %a %a" pp_value_cell_desc (tl,ty,k)
      pp_value c pp_value f
                    
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

and pp_value_cell_desc ppf (tl,ty,c) =
  pf ppf "@[<v>[ @[%a \u{22a2} %a@]@,| %a@,]@]"
    (pp_tele pp_value) tl
    pp_value ty pp_value_cell_frame c

and pp_value_cell_frame ppf c =
  let open Suite in
  let open Expr in 
  let open Opetopes.Idt.IdtConv in 
  pf ppf "%a" (pp_suite ~sep:(any "@,| ")
                 (pp_tr_expr (pp_dep_term pp_value))) (of_cmplx c) 

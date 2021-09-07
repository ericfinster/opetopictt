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
  | CellV of name * value * value cmplx * (value -> value) * value option cmplx 
  | CompV of name * value * value cmplx * (value -> value) * value option cmplx 
  | FillV of name * value * value cmplx * (value -> value) * value option cmplx 

  (* The Unit Type *)
  | UnitV
  | TtV
    
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

  | CellV (nm,a,ca,b,cb) ->
    pp_value_cell_desc ppf (nm,a,ca,b,cb)
  | CompV (nm,a,ca,b,cb) ->
    pf ppf "comp %a" pp_value_cell_desc (nm,a,ca,b,cb)
  | FillV (nm,a,ca,b,cb) ->
    pf ppf "fill %a" pp_value_cell_desc (nm,a,ca,b,cb)

  | UnitV -> pf ppf "\u{25cf}"
  | TtV -> pf ppf "\u{2219}"
    
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

and pp_value_cell_desc ppf (nm,a,ca,_,cb) =
  let cab = match_cmplx ca cb ~f:(fun a b -> (a,b)) in 
  pf ppf "@[<v>[ @[(%s : %a) \u{22a2} <closure>@]@,| %a@,]@]"
    nm pp_value a (pp_cmplx (Fmt.pair pp_value (Fmt.option pp_value))) cab

and pp_value_cell_frame ppf c =
  let open Suite in
  let open Expr in 
  let open Opetopes.Idt.IdtConv in 
  pf ppf "%a" (pp_suite ~sep:(any "@,| ")
                 (pp_tr_expr (pp_dep_term pp_value))) (of_cmplx c) 

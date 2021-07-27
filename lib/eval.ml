(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Term
open Value
open Suite
open Syntax

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

let rec eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  match tm with
  | VarT i ->
    (try db_get i loc
     with Lookup_error ->
       raise (Eval_error (str "Index out of range: %d" i)))
  | TopT nm -> TopV (nm,EmpSp,(
      try assoc nm top
      with Lookup_error ->
        raise (Eval_error (str "Unknown id during eval: %s" nm))
    ))
  | LamT (nm,u) -> LamV (nm, Closure (top,loc,u))
  | AppT (u,v) -> appV (eval top loc u) (eval top loc v) 
  | PiT (nm,u,v) -> PiV (nm, eval top loc u, Closure (top,loc,v))
  | TypT -> TypV

and ($$) c v =
  match c with
  | Closure (top,loc,tm) -> eval top (Ext (loc,v)) tm

and appV t u =
  match t with
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u),appV tv u)
  | LamV (_,cl) -> cl $$ u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u) -> appV (runSpV v sp') u 

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

and quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match v with
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp
  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl $$ varV k))
  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl $$ varV k))
  | TypV -> TypT

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u) ->
    AppT (qcs t sp',qc u)

let quote_tele tl =
  let rec go tl =
    match tl with
    | Emp -> (Emp,0)
    | Ext (typs',(nm,ict,typ)) ->
      let (r,k) = go typs' in
      let ty_tm = quote true k typ in
      (Ext (r,(nm,ict,ty_tm)),k+1)
  in fst (go tl)

let nf top loc tm =
  quote true (length loc) (eval top loc tm)


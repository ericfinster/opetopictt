(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Term
open Meta
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
  | LamT (nm,ict,u) -> LamV (nm, ict, Closure (top,loc,u))
  | AppT (u,v,ict) -> appV (eval top loc u) (eval top loc v) ict
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval top loc u, Closure (top,loc,v))
  | CellT (jdg,frm) ->
    (* let vfrm = map_cmplx frm
     *     ~f:(fun (ts, topt) ->
     *         (map_suite ts ~f:(eval top loc),
     *          Base.Option.map topt ~f:(eval top loc))) in  *)
    CellV (TlClosure (top,loc,jdg), frm)
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT m -> appLocV loc (metaV m)

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, EmpSp)
  | Solved v -> v

and ($$) c v =
  match c with
  | Closure (top,loc,tm) -> eval top (Ext (loc,v)) tm

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,AppSp(sp,u,ict))
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u,ict))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u,ict),appV tv u ict)
  | LamV (_,_,cl) -> cl $$ u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and appLocV loc v =
  match loc with
  | Emp -> v
  | Ext (loc',u) -> appV (appLocV loc' v) u Expl

and runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u,ict) -> appV (runSpV v sp') u ict

and force_meta v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> force_meta (runSpV v sp))
  | _ -> v

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

and quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match force_meta v with
  | FlexV (m,sp) -> qcs (MetaT m) sp
  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote ufld (k+1) (cl $$ varV k))
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, qc u, quote ufld (k+1) (cl $$ varV k))
  | CellV (TlClosure (top,loc,(tl,tm,ty)),frm) ->

    let (ttl,ttm,tty) = fold_accum_cont tl (loc,k)
        (fun (nm,ict,typ) (loc',k') ->
           ((nm,ict, quote ufld k' (eval top loc' typ)),
            (Ext (loc',varV k'),k'+1)))
        (fun tl' (loc',k') ->
           (tl',
            quote ufld k' (eval top loc' tm),
            quote ufld k' (eval top loc' ty))) in
    
    CellT ((ttl,ttm,tty),frm)
      
  | TypV -> TypT

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u,ict) ->
    AppT (qcs t sp',qc u,ict)

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

(*****************************************************************************)
(*                               Free Variables                              *)
(*****************************************************************************)

(* let rec free_vars_val k v =
 *   let module S = Base.Set in
 *   let sp_vars sp = free_vars_sp k sp in
 *   match force_meta v with
 *   | FlexV (_,sp) -> sp_vars sp
 *   | RigidV (l,sp) -> S.add (sp_vars sp) (lvl_to_idx k l)
 *   | TopV (_,sp,_) -> sp_vars sp
 *   | LamV (_,_,Closure (_,loc,tm)) -> free_vars (length loc) tm
 *   | PiV (_,_,a,Closure (_,loc,b)) ->
 *     S.union (free_vars_val k a) (free_vars (length loc) b)
 *   | TypV -> fvs_empty
 * 
 * and free_vars_sp k sp =
 *   let module S = Base.Set in
 *   let fvc x = free_vars_val k x in
 *   let fvcs x = free_vars_sp k x in
 *   match sp with
 *   | EmpSp -> fvs_empty
 *   | AppSp (sp',u,_) ->
 *     S.union (fvcs sp') (fvc u) *)


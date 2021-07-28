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
  | LamT (nm,u) -> LamV (nm, fun vl -> eval top (Ext (loc,vl)) u)
  | AppT (u,v) -> appV (eval top loc u) (eval top loc v) 
  | PiT (nm,u,v) -> PiV (nm, eval top loc u, fun vl -> eval top (Ext (loc,vl)) v)
  | TypT -> TypV
    
  | PosT -> PosV
  | ElT t -> ElV (eval top loc t) 

  | PosUnitT -> PosUnitV
  | PosEmptyT -> PosEmptyV
  | PosSumT (u, v) ->
    PosSumV (eval top loc u, eval top loc v) 
  | PosSigT (nm, a, b) ->
    PosSigV (nm, eval top loc a,
             fun v -> eval top (Ext (loc, v)) b)

  | PosTtT -> PosTtV 
  | PosInlT u -> PosInlV (eval top loc u)
  | PosInrT v -> PosInrV (eval top loc v) 
  | PosPairT (u,v) ->
    PosPairV (eval top loc u, eval top loc v) 

  | PosPiT (nm,a,b) ->
    PosPiV (nm, eval top loc a,
            fun v -> eval top (Ext (loc, v)) b)
  | PosLamT (nm,b) ->
    PosLamV (nm, fun v -> eval top (Ext (loc,v)) b) 
  | PosAppT (u,v) -> posAppV (eval top loc u) (eval top loc v) 

  | PosBotElimT -> PosBotElimV
  | PosTopElimT u ->
    PosTopElimV (eval top loc u)
  | PosSumElimT (u,v) ->
    PosSumElimV (eval top loc u, eval top loc v)
  | PosSigElimT u ->
    PosSigElimV (eval top loc u) 

and appV t arg =
  match t with
  | RigidV (i,sp) -> RigidV (i, AppSp(sp,arg))
  | TopV (nm,sp,t') -> TopV (nm, AppSp(sp,arg), appV t' arg)
  | LamV (_,b) -> b arg
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and posAppV t arg =
  match t with
  | RigidV (i,sp) -> RigidV (i, PosAppSp(sp,arg))
  | TopV (nm,sp,t') -> TopV (nm, AppSp(sp,arg), posAppV t' arg)
  | PosLamV (_,b) -> b arg
  | PosTopElimV u -> posTopElimV u arg
  | PosSumElimV (u,v) -> posSumElimV u v arg
  | PosSigElimV u -> posSigElimV u arg 
  | _ -> raise (Eval_error (Fmt.str "malformed position application: %a" pp_value t))

and posTopElimV t arg =
  match arg with
  | RigidV (i,sp) -> RigidV (i, PosTopElimSp (t,sp))
  | TopV (nm,sp,arg') -> TopV (nm, PosTopElimSp(t,sp), posTopElimV t arg')
  | PosTtV -> t
  | _ -> raise (Eval_error "invalid top elim")

and posSumElimV u v arg =
  match arg with
  | RigidV (i,sp) -> RigidV (i, PosSumElimSp (u,v,sp))
  | TopV (nm,sp,arg') -> TopV (nm, PosSumElimSp (u,v,sp), posSumElimV u v arg')
  | PosInlV l -> posAppV u l
  | PosInrV r -> posAppV v r 
  | _ -> raise (Eval_error "invalid sum elim")

and posSigElimV u arg =
  match arg with
  | RigidV (i,sp) -> RigidV (i, PosSigElimSp (u,sp))
  | TopV (nm,sp,arg') -> TopV (nm, PosSigElimSp (u,sp), posSigElimV u arg')
  | PosPairV (p,q) -> posAppV (posAppV u p) q 
  | _ -> raise (Eval_error "invalid sig elim") 
  
and runSpV v sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',u) -> appV (runSpV v sp') u
  | PosAppSp (sp',u) -> posAppV (runSpV v sp') u
  | PosTopElimSp (u,sp') -> posTopElimV u (runSpV v sp')
  | PosSumElimSp (u,v,sp') -> posSumElimV u v (runSpV v sp')
  | PosSigElimSp (u,sp') -> posSigElimV u (runSpV v sp')

(*****************************************************************************)
(*                        Type Directed eta Expansion                        *)
(*****************************************************************************)

(* It seems we'll lose the names doing this.  And so on ... *)
(* Indeed, I would guess that the variables now get kind of unhinged
   from the original settings.  Have to think about this. *)
                       
let rec up (t: value) (v: value) : value =
  match t with
  | PiV (nm,a,b) -> LamV (nm, fun vl -> up (b vl) (appV v (down a vl)))
  | _ -> v 

and down (t: value) (v: value) : value =
  match t with 
  | PiV (nm,a,b) ->
    LamV (nm, fun vl ->
        let vl' = up a vl in down (b vl') (appV v vl'))
  | TypV -> down_typ v 
  | _ -> v

and down_typ (t: value): value =
  match t with
  | PiV (nm,a,b) ->
    PiV (nm, down_typ a, fun v -> down_typ (b (up a v)))
  | _ -> t 

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
  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl (varV k)))
  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | TypV -> TypT
    
  | PosV -> PosT
  | ElV v -> ElT (qc v)
               
  | PosUnitV -> PosUnitT
  | PosEmptyV -> PosEmptyT
  | PosSumV (u,v) -> PosSumT (qc u, qc v) 
  | PosSigV (nm,a,b) ->
    PosSigT (nm,qc a, quote ufld (k+1) (b (varV k)))

  | PosTtV -> PosTtT
  | PosInlV u -> PosInlT (qc u)
  | PosInrV v -> PosInlT (qc v) 
  | PosPairV (u, v) -> PosPairT (qc u, qc v) 

  | PosPiV (nm,a,b) ->
    PosPiT (nm,qc a, quote ufld (k+1) (b (varV k)))
  | PosLamV (nm,b) -> 
    LamT (nm, quote ufld (k+1) (b (varV k)))

  | PosBotElimV -> PosBotElimT
  | PosTopElimV u -> PosTopElimT (qc u) 
  | PosSumElimV (u, v) ->
    PosSumElimT (qc u, qc v)
  | PosSigElimV u ->
    PosSigElimT (qc u) 

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u) ->
    AppT (qcs t sp',qc u)
  | PosAppSp (sp', u) ->
    PosAppT (qcs t sp', qc u)
  | PosTopElimSp (u,sp') -> 
    PosAppT (PosTopElimT (qc u), qcs t sp')
  | PosSumElimSp (u,v,sp') ->
    PosAppT (PosSumElimT (qc u , qc v), qcs t sp')
  | PosSigElimSp (u,sp') ->
    PosAppT (PosSigElimT (qc u), qcs t sp')

let quote_tele tl =
  let rec go tl =
    match tl with
    | Emp -> (Emp,0)
    | Ext (typs',(nm,ict,typ)) ->
      let (r,k) = go typs' in
      let ty_tm = quote true k typ in
      (Ext (r,(nm,ict,ty_tm)),k+1)
  in fst (go tl)

(* Fix this to perform expansion ... *) 
let nf top loc tm =
  quote true (length loc) (eval top loc tm)


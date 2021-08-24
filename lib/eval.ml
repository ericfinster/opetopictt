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

(*****************************************************************************)
(*                        Type Directed eta Expansion                        *)
(*****************************************************************************)

(* TOOD: you are not really handling variable names correctly when
   they are getting expanded.  Currently, you generate based on the
   level during readback.  But this does not prevent capture.  You
   need to fix this. *)

let rec up (t: value) (v: value) : value =
  match t with
  | PiV (nm,a,b) -> LamV (nm, fun vl -> up (b vl) (appV v (down a vl)))
  | PosPiV (_,PosEmptyV,_) -> PosBotElimV
  | PosPiV (nm,PosSumV (l,r), b) ->
    let lelim = PosLamV (nm ^ "-l", fun lv ->
        up (b lv) (posAppV v (PosInlV (down_pos l lv)))) in
    let relim = PosLamV (nm ^ "-r", fun rv ->
        up (b rv) (posAppV v (PosInrV (down_pos r rv)))) in 
    PosSumElimV (lelim, relim)
  | PosPiV (nm,a,b) -> PosLamV (nm, fun vp -> up (b vp) (posAppV v (down_pos a vp)))
  | ElV a -> up_pos a v
  | _ -> v 

and down (t: value) (v: value) : value =
  match t with 
  | PiV (nm,a,b) ->
    LamV (nm, fun vl ->
        let vl' = up a vl in down (b vl') (appV v vl'))
  (* We could also eta-expand arbitrary functions out of 
     El bot by saying they are app bot-elim ... *) 
  | PosPiV (_,PosEmptyV,_) ->
    PosBotElimV
  | PosPiV (nm, PosSumV (l,r), b) ->
    (* TODO: variable renaming here is not safe *)
    let lelim = LamV (nm ^ "-l", fun lv ->
        let lv' = up_pos l lv in 
        down (b (PosInlV lv')) (posAppV v (PosInlV lv'))) in 
    let relim = LamV (nm ^ "-r", fun rv ->
        let rv' = up_pos r rv in 
        down (b (PosInrV rv')) (posAppV v (PosInrV rv'))) in 
    PosSumElimV (lelim, relim) 
  | PosPiV (nm,a,b) ->
    PosLamV (nm, fun vp ->
        let vp' = up a vp in down (b vp') (posAppV v vp'))
  | ElV a -> down_pos a v 
  | TypV -> down_typ v
  | PosV -> down_pos_typ v
  | _ -> v

and down_typ (t: value) : value =
  match t with
  | PiV (nm,a,b) ->
    PiV (nm, down_typ a, fun v -> down_typ (b (up a v)))
  | PosPiV (nm,a,b) ->
    PosPiV (nm, down_pos_typ a, fun v -> down_typ (b (up_pos a v)))
  | _ -> t 

and up_pos (t: value) (v: value) : value =
  match t with
  | PosUnitV -> PosTtV
  | _ -> v 

and down_pos (t: value) (v: value) : value =
  match t with
  | PosUnitV -> PosTtV
  | _ -> v 

and down_pos_typ (t: value) : value =
  match t with
  | PosEmptyV -> PosEmptyV
  | PosUnitV -> PosUnitV
  | PosSumV (u,v) ->
    PosSumV (down_pos_typ u, down_pos_typ v)
  | PosSigV (nm,a,b) ->
    PosSigV (nm, down_pos_typ a, fun v -> down_pos_typ (b (up_pos a v)))
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
  | LamV (nm,cl) ->
    (* TODO: this is a hack which generates new names when eta
       expansion has inserted anonymous variables but how can we be
       sure that this name is fresh for the resulting expression? *)
    let nm' = if (String.equal nm "")
      then "x" ^ (string_of_int k)
      else nm in 
    LamT (nm', quote ufld (k+1) (cl (varV k)))
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


(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Term
open Value
open Syntax
open Suite
open Reflexivity

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let rec eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  let ev t = eval top loc t in
  let ev_bnd t v = eval top (Ext (loc,v)) t in 
  match tm with
  
  | VarT i ->
    begin try db_get i loc
      with Lookup_error ->
        raise (Internal_error (Fmt.str "de Brujin index %d out of range" i))
    end
    
  | TopT nm -> TopV (nm,EmpSp,top nm)
  | LetT (_,_,tm,bdy) -> ev_bnd bdy (ev tm) 

  | PiT (nm,a,b) -> PiV (nm, ev a, ev_bnd b) 
  | LamT (nm,u) -> LamV (nm, ev_bnd u) 
  | AppT (u,v) -> app_val (ev u) (ev v) 

  | SigT (nm,a,b) -> SigV (nm, ev a, ev_bnd b) 
  | PairT (u,v) -> PairV (ev u, ev v)
  | FstT u -> fst_val (ev u)
  | SndT u -> snd_val (ev u)
      
  | ReflT (u,nm,pi) -> refl_val Emp 0 (ev u) nm pi
  | ExpT _ -> raise (Internal_error "eval on exp") 

  | TypT -> TypV

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

let rec quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match v with

  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | ExpV (l,sp) -> qcs (ExpT (lvl_to_idx k l) ) sp 

  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp

  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl (varV k)))

  | SigV (nm,u,cl) -> SigT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | PairV (u,v) -> PairT (qc u, qc v)

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
  | FstSp sp' ->
    FstT (qcs t sp')
  | SndSp sp' ->
    SndT (qcs t sp')
  | ReflSp (sp',pi_nm,pi) ->
    ReflT (qcs t sp',pi_nm,pi)



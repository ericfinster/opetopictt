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
    begin try
        db_get i loc
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
      
  | ReflT (u,pi) -> refl_val Emp 0 (ev u) pi
      
  | TypT -> TypV

(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let rec quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match v with

  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | ExpV _ -> raise (Internal_error "quoting an expvar")

  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp

  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl (varV k)))

  | SigV (nm,u,cl) -> SigT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | PairV (u,v) -> PairT (qc u, qc v)

  | TypV -> TypT

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
  | ReflSp (sp',pi) ->
    ReflT (qcs t sp',pi)



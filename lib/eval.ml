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

open Opetopes.Idt
open Opetopes.Complex


(*****************************************************************************)
(*                             Environments                                  *)
(*****************************************************************************)

exception Eval_error of string

type env =
  { values : value suite;
    at_shape : string cmplx -> value cmplx suite
  }

let empty_env =
  { values = Emp ;
    at_shape = fun _ -> Emp
  } 

let with_var lvl rho =
  let vc_at pi =
    let vc = map_cmplx (face_cmplx pi)
        ~f:(fun f ->
            if (is_obj f) then
              varV lvl
            else RigidV (lvl, ReflSp (EmpSp,f))) in 
    Ext (rho.at_shape pi,vc) in 
  { values = Ext (rho.values, varV lvl) ;
    at_shape = vc_at } 

(*****************************************************************************)
(*                                Eliminators                                *)
(*****************************************************************************)

let rec app_val t u =
  match t with
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), app_val tv u)
  | LamV (_,cl) -> cl u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

let rec app_args f args =
  match args with
  | [] -> f
  | v::vs -> app_args (app_val f v) vs 

let rec fst_val t =
  match t with
  | RigidV (i,sp) -> RigidV (i, FstSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, FstSp sp, fst_val tv)
  | PairV (u,_) -> u
  | _ -> raise (Eval_error (Fmt.str "malformed first proj: %a" pp_value t))

let rec snd_val t =
  match t with
  | RigidV (i,sp) -> RigidV (i, SndSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, SndSp sp, snd_val tv)
  | PairV (_,v) -> v
  | _ -> raise (Eval_error (Fmt.str "malformed second proj: %a" pp_value t))


(*****************************************************************************)
(*                            Opetopic Combinators                           *)
(*****************************************************************************)

(* Abstract over all the positions in a given complex and pass
   the abstracted values in complex form to the function b. *)
let rec lam_cmplx (a : 'a cmplx) (b : value cmplx -> value) : value =

  let rec do_lams nl cm =
    match nl with
    | [] -> b cm
    | addr::addrs ->
      LamV ("", fun v -> 
          do_lams addrs (replace_at cm (0,addr) v))

  in match a with
  | Base n ->
    let n' = map_nst_with_addr n
        ~f:(fun _ addr -> addr) in
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    do_lams (nodes_nst n') (Base nv)
  | Adjoin (t,n) ->
    let n' = map_nst_with_addr n
        ~f:(fun _ addr -> addr) in 
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    lam_cmplx t (fun vc -> do_lams (nodes_nst n') (Adjoin (vc,nv)))
  
(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let rec eval lvl top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  let ev t = eval lvl top loc t in
  let ev_bnd v t = eval lvl top (with_value lvl loc v) t in 
  match tm with
  
  | VarT i -> db_get i loc.values 
  | TopT nm -> TopV (nm,EmpSp,top nm)

  | LamT (nm,u) ->
    LamV (nm,fun v -> ev_bnd v u) 
  | AppT (u,v) -> app_val (ev u) (ev v) 
  | PiT (nm,a,b) -> PiV (nm, ev a, fun v -> ev_bnd v b) 

  | PairT (u,v) -> PairV (ev u, ev v)
  | FstT u -> fst_val (ev u)
  | SndT u -> snd_val (ev u)
  | SigT (nm,a,b) -> SigV (nm, ev a, fun v -> ev_bnd v b) 
      
  | ReflT (u,pi) -> refl_val lvl loc (ev u) pi 
      
  | TypT -> TypV

and expand_at lvl loc opvs v pi : value =
  match v with
  | RigidV (k,sp) ->
    let hv = head_value (nth k opvs) in
    expand_sp lvl loc opvs hv sp pi 
  | TopV (_,_,tv) -> expand_at lvl loc opvs tv pi 

  | LamV (_,bdy) ->

    lam_cmplx pi (fun vc ->
        expand_at (lvl+1) loc (Ext (opvs, vc))
          (bdy (varV lvl)) pi)

  | _ -> failwith "" 

and expand_sp lvl loc opvs v sp pi =
  match sp with
  | EmpSp -> v
  | FstSp sp' -> fst_val (expand_sp lvl loc opvs v sp' pi)
  | SndSp sp' -> snd_val (expand_sp lvl loc opvs v sp' pi)
  | AppSp _ -> failwith "app in refl_sp"
  | ReflSp (sp',pi') ->
    let v' = expand_sp lvl loc opvs v sp' pi in
    refl_val lvl loc v' pi'

and refl_val lvl loc v pi = 
  match v with
  | RigidV (k,sp) ->
    RigidV (k,ReflSp (sp,pi))
  | TopV (nm,sp,tv) ->
    TopV (nm,ReflSp (sp,pi), refl_val lvl loc tv pi)
  | _ -> expand_at lvl loc (loc.at_shape pi) v pi 

and with_value lvl loc v =
  let vshp pi =
    let vc = map_cmplx (face_cmplx pi)
        ~f:(fun f ->
            if (is_obj f) then v
            else expand_at lvl loc
                (loc.at_shape f) v f) in 
    Ext (loc.at_shape pi,vc) in
  { values = Ext (loc.values, v) ;
    at_shape = vshp } 


(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let rec quote ufld k v =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match v with

  | RigidV (l,sp) -> qcs (VarT (lvl_to_idx k l)) sp
  | TopV (_,_,tv) when ufld -> qc tv
  | TopV (nm,sp,_) -> qcs (TopT nm) sp

  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl (varV k)))
  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl (varV k)))

  | PairV (u,v) -> PairT (qc u, qc v)
  | SigV (nm,u,cl) -> SigT (nm, qc u, quote ufld (k+1) (cl (varV k)))

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



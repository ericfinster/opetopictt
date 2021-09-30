(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Term
open Value
open Syntax

       
(*****************************************************************************)
(*                         Evaluation Utilities                              *)
(*****************************************************************************)

exception Eval_error of string

let ext_loc loc v i =
  if (i <= 0) then v
  else loc (i-1)

let emp_loc _ =
  raise (Eval_error "Empty local environment")

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
(*                             Opetopic Expansion                            *)
(*****************************************************************************)

open Opetopes.Complex
       
let expand (l: lvl) (oenv : lvl -> value cmplx) (v : value)
  (c : string cmplx) (fa : face_addr) : value =
  match v with
  | RigidV (k,sp) ->
    if (k > l) then
      let var_cmplx = oenv (k - 1) in
      value_at var_cmplx fa
    else
      (* Check this ... *)
      ReflV (RigidV (k,sp) , face_at c fa)

  | _ -> failwith ""


(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let rec eval lvl top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  let ev t = eval lvl top loc t in 
  match tm with
  
  | VarT i -> loc i 
  | TopT nm -> TopV (nm,EmpSp,top nm)

  | LamT (nm,u) ->
    LamV (nm,fun v -> eval lvl top (ext_loc loc v) u)
  | AppT (u,v) -> app_val (ev u) (ev v) 
  | PiT (nm,a,b) ->
    PiV (nm, ev a, fun v -> eval lvl top (ext_loc loc v) b)

  | PairT (u,v) -> PairV (ev u, ev v)
  | FstT u -> fst_val (ev u)
  | SndT u -> snd_val (ev u)
  | SigT (nm,a,b) -> SigV (nm, ev a, fun v -> eval lvl top (ext_loc loc v) b)
      
  | ReflT (u,pi) ->
    (* TODO: Make this semantic ... *)
    ReflV (ev u, pi)
      
  | TypT -> TypV

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

  | ReflV (a,pi) ->
    ReflT (qc a, pi) 

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



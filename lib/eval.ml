(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Term
open Value
open Syntax

open Opetopes.Idt
open Opetopes.Complex

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
(*                             Opetopic Expansion                            *)
(*****************************************************************************)

(* let empty_op_env _ =
 *   raise (Eval_error "Empty opetopic environment")
 *     
 * let refl_val (lvl: lvl) (oe : lvl -> value cmplx) (v : value)
 *     (c : string cmplx) (fa : face_addr) : value =
 *   match v with
 *   | RigidV (k,sp) ->
 *     if (k > lvl) then
 *       let var_cmplx = oe (k - 1) in
 *       value_at var_cmplx fa
 *     else
 *       (\* Check this ... *\)
 *       ReflV (RigidV (k,sp) , face_at c fa)
 * 
 *   (\* Oh.  But we still have to run the spine to pick up the eliminators ... *\)
 *         
 *   | LamV (nm,bdy) ->
 * 
 *     (\* Extract the face? *\) 
 *     lam_cmplx c (fun cv -> TypV)
 * 
 *   | _ -> failwith "" *)
  
(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let empty_op_loc _ =
  raise (Eval_error "Empty opetopic environment")

let ext_op_loc loc vc i =
  if (i <= 0) then vc
    else loc (i-1)
  
let face_op_loc loc fa k =
  face_at (loc k) fa 

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
  | SigT (nm,a,b) ->
    SigV (nm, ev a, fun v -> eval lvl top (ext_loc loc v) b)
      
  | ReflT (_,_) -> failwith ""
  (* refl_val lvl empty_op_env (ev u) pi (0,[]) *)
      
  | TypT -> TypV

and refl_val lvl loc v pi : value =
  match v with
  | RigidV (k,_) ->
    (* but run the spine, too! *) 
    head_value (loc (lvl_to_idx lvl k)) 

  | LamV (_,bdy) ->

    lam_cmplx pi (fun vc ->
        refl_val (lvl+1) (ext_op_loc loc vc)
          (bdy (varV lvl)) pi)

  | _ -> failwith "" 

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



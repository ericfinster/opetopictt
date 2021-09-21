
(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Term
open Value
open Suite
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

let rec appV t u =
  match t with
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), appV tv u)
  | LamV (_,cl) -> cl u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

let rec app_to_fib v_lst ty =
  match v_lst with
  | [] -> ty
  | v::vs -> app_to_fib vs (appV ty v)

(* TODO: Combine the next two functions? *)
let rec app_vars t v i =
  match t with
  | Emp -> (v,i)
  | Ext (t',(_,_)) ->
    let (v',k) = app_vars t' v i in 
    (appV v' (varV k), k + 1)

let rec fstV t =
  match t with
  | RigidV (i,sp) -> RigidV (i, FstSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, FstSp sp, fstV tv)
  | PairV (u,_) -> u
  | _ -> raise (Eval_error (Fmt.str "malformed first proj: %a" pp_value t))

let rec sndV t =
  match t with
  | RigidV (i,sp) -> RigidV (i, SndSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, SndSp sp, sndV tv)
  | PairV (_,v) -> v
  | _ -> raise (Eval_error (Fmt.str "malformed second proj: %a" pp_value t))


(*****************************************************************************)
(*                             Opetopic Expansion                            *)
(*****************************************************************************)

let rec shiftV f v =
  match v with
  | RigidV (l,sp) -> RigidV (f l , shiftSp f sp)
  | TopV (nm,sp,tv) ->
    TopV (nm, shiftSp f sp,shiftV f tv)
  | LamV (nm,b) ->
    LamV (nm,fun v' -> shiftV f (b v'))
  | PiV (nm,a,b) ->
    PiV (nm, shiftV f a, fun v' -> shiftV f (b v'))
  | PairV (u,v) ->
    PairV (shiftV f u, shiftV f v)
  | SigV (nm, a, b) ->
    SigV (nm, shiftV f a, fun v' -> shiftV f (b v'))
  | TypV -> TypV

and shiftSp f sp =
  match sp with
  | EmpSp -> EmpSp
  | AppSp (sp',v) ->
    AppSp (shiftSp f sp', shiftV f v)
  | FstSp sp' -> FstSp (shiftSp f sp')
  | SndSp sp' -> SndSp (shiftSp f sp')

open Opetopes.Complex
let naiveExpand (v : value) (c : 'a cmplx) : value cmplx =
  let (num_c , total) = numerate c in 
  map_cmplx num_c ~f:(fun idx ->
      shiftV (fun l -> (l * total) + idx) v)

(* Probably won't be used now ... *)
(*****************************************************************************)
(*                                Substitution                               *)
(*****************************************************************************)

let rec runSp v s sp =
  match sp with
  | EmpSp -> v
  | AppSp (sp',v') ->
    appV (runSp v s sp') v'
  | FstSp sp' ->
    fstV (runSp v s sp')
  | SndSp sp' ->
    sndV (runSp v s sp') 

let rec sub v s =
  match v with
  | RigidV (l,sp) -> runSp (s l) s (subSp sp s) 
  | TopV (nm,sp,tv) ->
    TopV (nm,subSp sp s,sub tv s)
  | LamV (nm,b) ->
    (* Hmmm, modify the substitution under a binder? *) 
    LamV (nm,fun v' -> sub (b v') s)
  | PiV (nm,a,b) ->
    PiV (nm, sub a s, fun v' -> sub (b v') s)
  | PairV (u,v) ->
    PairV (sub u s, sub v s)
  | SigV (nm, a, b) ->
    SigV (nm, sub a s, fun v' -> sub (b v') s)
  | TypV -> TypV

and subSp sp s =
  match sp with
  | EmpSp -> EmpSp
  | AppSp (sp',v) ->
    AppSp (subSp sp' s, sub v s)
  | FstSp sp' -> FstSp (subSp sp' s)
  | SndSp sp' -> SndSp (subSp sp' s)
    
(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

and eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  match tm with
  | VarT i -> loc i 
  | TopT nm -> TopV (nm,EmpSp,top nm)

  | LamT (nm,u) ->
    LamV (nm,fun v -> eval top (ext_loc loc v) u)
  | AppT (u,v) -> appV (eval top loc u) (eval top loc v) 
  | PiT (nm,a,b) ->
    PiV (nm, eval top loc a,
         fun v -> eval top (ext_loc loc v) b)

  | PairT (u,v) ->
    PairV (eval top loc u, eval top loc v)
  | FstT u ->
    fstV (eval top loc u)
  | SndT u ->
    sndV (eval top loc u)
  | SigT (nm,u,v) ->
    SigV (nm, eval top loc u,
          fun x -> eval top (ext_loc loc x) v)

  | TypT -> TypV

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

  | PairV (u,v) -> PairT (qc u, qc v)
  | SigV (nm,u,cl) -> SigT (nm, qc u, quote ufld (k+1) (cl (varV k)))

  | TypV -> TypT

and quote_fib ufld k tl ty =
  match tl with
  | Emp -> (Emp , quote ufld k ty)
  | Ext (tl',(nm,ty')) ->

    let (tl_tm, ty_tm) = quote_fib ufld k tl' ty' in
    let (app_v , k') = app_vars tl ty k in

    (Ext (tl_tm,(nm,ty_tm)) , quote ufld k' app_v)

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



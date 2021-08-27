(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Term
open Value
open Syntax

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

let ext_loc loc v i =
  if (i <= 0) then v
  else loc (i-1)

let emp_loc _ =
  raise (Eval_error "Empty local environment")

let rec eval top loc tm =
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
  | TypT -> TypV

and appV t u =
  match t with
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u),appV tv u )
  | LamV (_,cl) -> cl u
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
  | LamV (nm,cl) -> LamT (nm, quote ufld (k+1) (cl (varV k)))
  | PiV (nm,u,cl) -> PiT (nm, qc u, quote ufld (k+1) (cl (varV k)))
  | TypV -> TypT

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u) ->
    AppT (qcs t sp',qc u)


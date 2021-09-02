(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Term
open Value
open Suite
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
      
  | CellT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    CellV  (tl_v , ty_v , c_v)
  | CompT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    CompV  (tl_v , ty_v , c_v)
  | FillT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    FillV  (tl_v , ty_v , c_v)

  | TypT -> TypV

and eval_cell_desc top loc tl ty c =
  let (tl_v , ty_v) = eval_fib top loc tl ty in 
  let c_v = map_cell_desc_cmplx c ~f:(eval top loc) in 
  (tl_v, ty_v, c_v)
  
and eval_fib top loc tl ty =
  match tl with
  | Emp -> (Emp , eval top loc ty)
  | Ext (tl',(nm,ty')) ->

    let (tl_v , ty_v) = eval_fib top loc tl' ty' in
    let lams = TermUtil.abstract_tele tl ty in 
    let this_ty_val = eval top loc lams in

    (Ext (tl_v,(nm,ty_v)) , this_ty_val) 

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
                       
  | CellV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    CellT (tl',ty',c')
  | CompV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    CompT (tl',ty',c')
  | FillV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    FillT (tl',ty',c')

  | TypV -> TypT

and quote_cell_desc ufld k tl ty c = 
  let (tl',ty') = quote_fib ufld k tl ty in
  let c' = map_cell_desc_cmplx c ~f:(quote ufld k)in
  (tl',ty',c')

and quote_fib ufld k tl ty =
  match tl with
  | Emp -> (Emp , quote ufld k ty)
  | Ext (tl',(nm,ty')) ->

    (* TODO: Check the logic here.  Idea is to iteratively apply the
       fibration to all the variables in the context and then quote.
       But are we quoting at the right level and everything?  Have to
       check this .... *)
    
    let rec app_vars t v =
      match t with
      | Emp -> (v,k)
      | Ext (t',(_,_)) ->
        let (v',k') = app_vars t' v in 
        (appV v' (varV k'), k' + 1)
    in

    let (tl_tm, ty_tm) = quote_fib ufld k tl' ty' in
    let (app_v , k') = app_vars tl ty in

    (Ext (tl_tm,(nm,ty_tm)) , quote ufld k' app_v)

and quote_sp ufld k t sp =
  let qc x = quote ufld k x in
  let qcs x s = quote_sp ufld k x s in
  match sp with
  | EmpSp -> t
  | AppSp (sp',u) ->
    AppT (qcs t sp',qc u)


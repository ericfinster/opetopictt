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

  | PairT (u,v) ->
    PairV (eval top loc u, eval top loc v)
  | FstT u ->
    fstV (eval top loc u)
  | SndT u ->
    sndV (eval top loc u)
  | SigT (nm,u,v) ->
    SigV (nm, eval top loc u,
          fun x -> eval top (ext_loc loc x) v)

  | CellT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    cellV tl_v ty_v c_v
  | CompT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    CompV  (tl_v , ty_v , c_v)
  | FillT (tl,ty,c) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    FillV  (tl_v , ty_v , c_v)
  | KanElimT (tl,ty,c,p,d,comp,fill) ->
    let (tl_v, ty_v, c_v) =
      eval_cell_desc top loc tl ty c in
    let pv = eval top loc p in
    let dv = eval top loc d in
    let compv = eval top loc comp in
    let fillv = eval top loc fill in
    kanElimV tl_v ty_v c_v pv dv compv fillv

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
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), appV tv u)
  | KanElimV (tl,ty,c,p,d,comp,fill,sp) ->
    KanElimV (tl,ty,c,p,d,comp,fill,AppSp(sp,u))
  | LamV (_,cl) -> cl u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

and fstV t =
  match t with
  | RigidV (i,sp) -> RigidV (i, FstSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, FstSp sp, fstV tv)
  | PairV (u,_) -> u
  | _ -> raise (Eval_error (Fmt.str "malformed first proj: %a" pp_value t))

and sndV t =
  match t with
  | RigidV (i,sp) -> RigidV (i, SndSp sp)
  | TopV (nm,sp,tv) -> TopV (nm, SndSp sp, sndV tv)
  | PairV (_,v) -> v
  | _ -> raise (Eval_error (Fmt.str "malformed second proj: %a" pp_value t))

and cellV tl ty c =
  let open Opetopes.Complex in 
  match c with
  | Base (Lf (vs,_)) -> 
    let rec app_to_fib v_lst ty =
      begin match v_lst with
        | [] -> ty
        | v::vs -> app_to_fib vs (appV ty v)
      end in
    app_to_fib (to_list vs) ty 
          
  | _ ->

    let rec sig_src_fib t v =
      begin match t with
        | [] ->
          begin match v with
            | SigV (_,a,_) -> a
            | _ -> failwith "ext_sig_src"
          end 
        | (nm,_)::tps ->
          LamV (nm,fun x ->
              let tps' = List.map tps ~f:(fun (nm,y) -> (nm,appV y x)) in
              let v' = appV v x in 
              sig_src_fib tps' v')

      end in 

    let rec sig_tgt_fib t v =
      begin match t with
        | [] ->
          begin match v with
            | SigV (nm,_,b) -> LamV (nm,b)
            | _ -> failwith "ext_sig_src"
          end 
        | (nm,_)::tps ->
          LamV (nm,fun x ->
              let tps' = List.map tps ~f:(fun (nm,y) -> (nm,appV y x)) in
              let v' = appV v x in 
              sig_tgt_fib tps' v')

      end in 
    
    let rec app_vars t v =
      match t with
      | Emp -> (v,0)
      | Ext (t',(_,_)) ->
        let (v',k) = app_vars t' v in 
        (appV v' (varV k), k + 1)
        
    in begin match app_vars tl ty with
      | (SigV (anm,_,_),_) ->
        log_msg "sigma in a cell type";

        let tlst = to_list tl in
        
        let afib = sig_src_fib tlst ty in
        let acmplx = map_cmplx c
            ~f:(fun (vs,vo) -> (vs,Option.map vo ~f:fstV)) in

        let bfib = sig_tgt_fib tlst ty in
        let tgt_typ x =
          CellV (Ext (tl,(anm,afib)),bfib,
                 map_cmplx c
                   ~f:(fun (vs,vo) ->
                       match vo with
                       | None -> (Ext (vs,x),None)
                       | Some p -> (Ext (vs,fstV p),Some (sndV p)))) in 
        
        let src_typ = CellV (tl,afib,acmplx) in 
        SigV ("",src_typ,tgt_typ)
          
      | _ -> CellV (tl,ty,c)
               
    end

and kanElimV tl ty c p d comp fill =
  match (comp,fill) with
  | (TopV (_,_,tv),_) ->
    kanElimV tl ty c p d tv fill
  | (_,TopV (_,_,tv)) ->
    kanElimV tl ty c p d comp tv
  (* TODO : What kind of check do I need here? *) 
  | (CompV (_,_,_) , FillV (_,_,_)) -> d
  | _ -> KanElimV (tl,ty,c,p,d,comp,fill,EmpSp)

(* and runSpV v sp =
 *   match sp with
 *   | EmpSp -> v
 *   | AppSp (sp',u) -> appV (runSpV v sp') u *)

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

  | CellV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    CellT (tl',ty',c')
  | CompV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    CompT (tl',ty',c')
  | FillV (tl,ty,c) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    FillT (tl',ty',c')
  | KanElimV (tl,ty,c,p,d,comp,fill,sp) ->
    let (tl',ty',c') = quote_cell_desc ufld k tl ty c in
    qcs (KanElimT (tl',ty',c',qc p, qc d, qc comp, qc fill)) sp 

  | TypV -> TypT

and quote_cell_desc ufld k tl ty c = 
  let (tl',ty') = quote_fib ufld k tl ty in
  let c' = map_cell_desc_cmplx c ~f:(quote ufld k)in
  (tl',ty',c')

and quote_fib ufld k tl ty =
  match tl with
  | Emp -> (Emp , quote ufld k ty)
  | Ext (tl',(nm,ty')) ->
    
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
  | FstSp sp' ->
    FstT (qcs t sp')
  | SndSp sp' ->
    SndT (qcs t sp') 


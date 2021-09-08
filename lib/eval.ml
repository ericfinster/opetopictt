
(*****************************************************************************)
(*                                                                           *)
(*                           Evaluation and Quoting                          *)
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Term
open Value
(* open Suite *)
open Syntax

open Opetopes.Complex
(* open Opetopes.Idt *)

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
(*                                 Evaluation                                *)
(*****************************************************************************)

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

  | CellT (nm,a,b,ca,cb) ->
    let (av,bv,cav,cbv) = eval_cell_over top loc a b ca cb in
    CellV (nm,av,cav,bv,cbv)
  | CompT (nm,a,b,ca,cb) -> 
    let (av,bv,cav,cbv) = eval_cell_over top loc a b ca cb in
    CompV (nm,av,cav,bv,cbv)
  | FillT (nm,a,b,ca,cb) -> 
    let (av,bv,cav,cbv) = eval_cell_over top loc a b ca cb in
    FillV (nm,av,cav,bv,cbv)

  | UnitT -> UnitV
  | TtT -> TtV

  | TypT -> TypV

and eval_cell_over top loc a b ca cb =
  let av = eval top loc a in
  let bv v = eval top (ext_loc loc v) b in 
  let cav = map_cmplx ca ~f:(eval top loc) in 
  let cbv = map_cmplx cb
      ~f:(fun o -> Option.map o ~f:(eval top loc)) in 
  (av,bv,cav,cbv)

and appV t u =
  match t with
  | RigidV (i,sp) -> RigidV (i,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), appV tv u)
  (* | KanElimV (tl,ty,c,p,d,comp,fill,sp) ->
   *   KanElimV (tl,ty,c,p,d,comp,fill,AppSp(sp,u)) *)
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

(* and cellV tl ty c =
 *   match c with
 *   | Base (Lf (vs,_)) ->
 *     app_to_fib (to_list vs) ty 
 * 
 *   | _ -> begin match app_vars tl ty 0 with
 * 
 *       (\* Cells in a Sigma type *\)
 *       | (SigV (anm,_,_),_) ->
 *         log_msg "sigma in a cell type";
 * 
 *         let ext_sig_src v =
 *           begin match v with
 *             | SigV (_,a,_) -> a
 *             | _ -> failwith "ext_sig_src"
 *           end in
 * 
 *         let ext_sig_tgt v = 
 *           begin match v with
 *             | SigV (nm,_,b) -> LamV (nm,b)
 *             | _ -> failwith "ext_sig_tgt"
 *           end in 
 * 
 *         let tlst = to_list tl in
 * 
 *         let afib = map_fib tlst ty ext_sig_src in
 *         let acmplx = map_cmplx c
 *             ~f:(fun (vs,vo) -> (vs,Option.map vo ~f:fstV)) in
 * 
 *         let bfib = map_fib tlst ty ext_sig_tgt in
 *         let tgt_typ x =
 *           CellV (Ext (tl,(anm,afib)),bfib,
 *                  map_cmplx c
 *                    ~f:(fun (vs,vo) ->
 *                        match vo with
 *                        | None -> (Ext (vs,x),None)
 *                        | Some p -> (Ext (vs,fstV p),Some (sndV p)))) in 
 * 
 *         let src_typ = CellV (tl,afib,acmplx) in 
 *         SigV ("",src_typ,tgt_typ)
 *           
 *       (\* Cells in a Pi type *\)
 *       | (PiV (anm,_,_),_) ->
 *         log_msg "pi in a cell type";
 * 
 *         let ext_pi_src v =
 *           begin match v with
 *             | PiV (_,a,_) -> a
 *             | _ -> failwith "ext_pi_src"
 *           end in
 * 
 *         let ext_pi_tgt v = 
 *           begin match v with
 *             | PiV (nm,_,b) -> LamV (nm,b)
 *             | _ -> failwith "ext_pi_tgt"
 *           end in 
 * 
 *         let tlst = to_list tl in
 *         let afib = map_fib tlst ty ext_pi_src in
 *         let bfib = map_fib tlst ty ext_pi_tgt in
 * 
 *         (\* zero out the complex. don't think this is required,
 *            but I'm just being cautious *\)
 *         let to_abst = map_cmplx c
 *             ~f:(fun (vs,_) -> (vs,None)) in 
 * 
 *         let k vc =
 * 
 *           let frm_c =
 *             match_cmplx (face_cmplx vc) c
 *               ~f:(fun f (ss,so) ->
 * 
 *                   let args = List.map (labels f)
 *                       (\* we allow the exception here....*\)
 *                       ~f:(fun (_,aopt) -> Option.value_exn aopt) in 
 * 
 *                   let top_arg =
 *                     Option.value_exn (snd (base_value (head_of f))) in
 *                   
 *                   (Ext (ss,top_arg),Option.map so ~f:(app_to_fib args)))
 * 
 *           in CellV (Ext (tl,(anm,afib)) , bfib , frm_c)
 *       
 *         in abst_cmplx tl afib to_abst k 
 * 
 *       (\* Cells in the universe *\)
 *       | (TypV,_) ->
 *         log_msg "u in a cell type";
 * 
 *         let c' = tail_of c in
 *         let k _ = TypV in
 *         let this_fib = cell_univ c' k in 
 *         
 *         begin match c' with
 *           | Base _ ->
 * 
 *             (\* Here, we should directly have access to the source and 
 *                target, and I think we just do things by hand ....
 *             *\)
 *             failwith "arrow case not done"
 *               
 *           | Adjoin (t,n) ->
 * 
 *             let k_nst t' =
 * 
 *               let frm_cmplx = Adjoin (t',n) in 
 *               
 *               let typ_nst = map_nst_with_addr n
 *                   ~f:(fun (_,fib_opt) addr ->
 *                       let fib = Option.value_exn fib_opt in
 * 
 *                       let f = face_at frm_cmplx (0,addr) in
 *                       let args = List.map (labels (tail_of f))
 *                           ~f:(fun (_,tm_opt) ->
 *                               Option.value_exn tm_opt) in
 *                       let this_typ = app_to_fib args fib in 
 *                       Some (addr, this_typ)) in 
 * 
 * 
 *               (\* But here we just have fibrations abstracted
 *                  over the top level.  This doesn't seem right ...*\)
 *               let cmp_vals = map_nst typ_nst
 *                   ~f:(fun opt ->
 *                       begin match opt with
 *                         | Some (addr,fib) ->
 *                           
 *                           let kan_nst = apply_at_nst typ_nst addr
 *                               (fun _ -> None) in 
 *                           let kan_nds = List.filter_opt (nodes_nst kan_nst) in
 *                           
 *                           abst_type_lst kan_nds frm_cmplx
 *                             (fun _ -> fib)
 *                             
 *                         | None -> failwith "impossible"
 *                       end) in 
 * 
 *               TypV 
 * 
 *             in cell_univ t k_nst
 *               
 *         end 
 *       
 *       | _ -> CellV (tl,ty,c)
 * 
 *     end
 * 
 * and kanElimV tl ty c p d comp fill =
 *   match (comp,fill) with
 *   | (TopV (_,_,tv),_) ->
 *     kanElimV tl ty c p d tv fill
 *   | (_,TopV (_,_,tv)) ->
 *     kanElimV tl ty c p d comp tv
 *   (\* TODO : What kind of check do I need here? *\) 
 *   | (CompV (_,_,_) , FillV (_,_,_)) -> d
 *   | _ -> KanElimV (tl,ty,c,p,d,comp,fill,EmpSp)
 * 
 * (\* TODO: Combine the next two functions? *\)
 * and app_vars t v i =
 *   match t with
 *   | Emp -> (v,i)
 *   | Ext (t',(_,_)) ->
 *     let (v',k) = app_vars t' v i in 
 *     (appV v' (varV k), k + 1)
 * 
 * and app_to_fib v_lst ty =
 *   match v_lst with
 *   | [] -> ty
 *   | v::vs -> app_to_fib vs (appV ty v)
 * 
 * and map_fib t v f =
 *   match t with
 *   | [] -> f v 
 *   | (nm,_)::tps ->
 *     LamV (nm,fun x ->
 *         let tps' = List.map tps ~f:(fun (nm,y) -> (nm,appV y x)) in
 *         let v' = appV v x in 
 *         map_fib tps' v' f)
 * 
 * and abst_type_lst nl cm k =
 *   match nl with
 *     | [] -> k cm
 *     | (addr,typ)::ns ->
 *       PiV ("", typ, fun v ->
 *           abst_type_lst ns
 *             (apply_at cm (0,addr)
 *                (fun (vs,_) -> (vs, Some v))) k)
 * 
 * (\* A general routine for abstracting over the 
 *    variables of a complex.  This maybe belongs elsewhere ... *\)
 * and abst_cmplx (tl : value tele) (ty : value)
 *     (c : value dep_term cmplx)
 *     (k : value dep_term cmplx -> value) : value =
 * 
 *   match c with
 *   | Base n ->
 * 
 *     let typ_nst = map_nst_with_addr n
 *         ~f:(fun (ts,_) addr ->
 *             let this_typ = app_to_fib (to_list ts) ty in
 *             (addr,this_typ)) in 
 * 
 *     abst_type_lst (nodes_nst typ_nst) (Base n) k 
 * 
 *   | Adjoin (t,n) -> 
 * 
 *     let k' t' = 
 *       
 *       let frm_cmplx = Adjoin (t',n) in
 * 
 *       let typ_nst = map_nst_with_addr n
 *           ~f:(fun (_,_) addr ->
 *               let f = face_at frm_cmplx (0,addr) in
 *               (\* zero our the term position just in case ... *\)
 *               let f' = with_head f
 *                   (map_nst (head_of f) ~f:(fun (vs,_) -> (vs,None))) in 
 *               let this_typ = CellV (tl,ty,f') 
 *               in (addr,this_typ))
 * 
 *       in abst_type_lst (nodes_nst typ_nst) frm_cmplx k 
 * 
 *     in abst_cmplx tl ty t k' 
 * 
 * (\* Similar to above, but abstracts over a sequence of fibrations in 
 *    the universe ...*\)
 *       
 * and cell_univ
 *     (c : value dep_term cmplx)
 *     (k : value dep_term cmplx -> value) =
 *   
 *   match c with
 *   | Base n ->
 * 
 *     let typ_nst = map_nst_with_addr n
 *         ~f:(fun (_,topt) addr ->
 *             let this_typ = Option.value_exn topt in
 *             (addr,this_typ)) in 
 * 
 *     abst_type_lst (nodes_nst typ_nst) (Base n) k
 * 
 *   | Adjoin (t,n) ->
 * 
 *     let k' t' =
 * 
 *       let frm_cmplx = Adjoin (t',n) in
 * 
 *       let typ_nst = map_nst_with_addr n
 *           ~f:(fun (_,fib_opt) addr ->
 *               let fib = Option.value_exn fib_opt in
 * 
 *               let f = face_at frm_cmplx (0,addr) in
 *               let args = List.map (labels (tail_of f))
 *                   ~f:(fun (_,tm_opt) ->
 *                       Option.value_exn tm_opt) in
 *               let this_typ = app_to_fib args fib in 
 *               (addr,this_typ))
 * 
 *       in abst_type_lst (nodes_nst typ_nst) frm_cmplx k
 * 
 *     in cell_univ t k'  *)


(*****************************************************************************)
(*                            Complex Combinators                            *)
(*****************************************************************************)

let fst_cmplx (c : value cmplx) : value cmplx
  = map_cmplx c ~f:fstV

let snd_cmplx (c : value cmplx) : value cmplx
  = map_cmplx c ~f:sndV 

(* let el_cmplx (c : value cmplx) : value
 *   = failwith "not done" 
 * 
 * let rec pi_cmplx (a : value cmplx) (b : value cmplx -> value cmplx) : value cmplx =
 *   failwith "unknown"
 * 
 * (\* Is this pointwise? Or do you insert lower-dim'l arguments? *\)
 * let rec app_cmplx (u : value cmplx) (v : value cmplx) : value cmplx =
 *   failwith "unknonw" *)

open Opetopes.Idt

(* let lam_cmplx (c : 'a cmplx) (k : value cmplx -> value) : value =
 *   match c with
 *   | Base n -> 
 *     
 *   | Adjoin _ -> failwith "not done"
 *            
 * let rec expand (c : 'a cmplx) (typ : value) : value cmplx =
 *   match c with
 *   | Base n ->
 *     Base (map_nst n ~f:(fun _ -> typ))
 *   | Adjoin (t,n) ->
 *     let tv = expand t typ in
 *     let nv = map_nst_with_addr n
 *         ~f:(fun _ _ -> TypV) in
 *     Adjoin (tv,nv) *)
    
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

  | CellV (nm,a,ac,b,bc) ->
    let (at,atc,bt,btc) = quote_cell_over ufld k a ac b bc in
    CellT (nm,at,bt,atc,btc)
  | CompV (nm,a,ac,b,bc) -> 
    let (at,atc,bt,btc) = quote_cell_over ufld k a ac b bc in
    CompT (nm,at,bt,atc,btc)
  | FillV (nm,a,ac,b,bc) -> 
    let (at,atc,bt,btc) = quote_cell_over ufld k a ac b bc in
    FillT (nm,at,bt,atc,btc)

  | UnitV -> UnitT
  | TtV -> TtT
    
  | TypV -> TypT

and quote_cell_over ufld k a ac b bc =
  let at = quote ufld k a in
  let atc = map_cmplx ac ~f:(quote ufld k) in
  let bt = quote ufld (k+1) (b (varV k)) in
  let btc = map_cmplx bc
      ~f:(fun o -> Option.map o ~f:(quote ufld k)) in 
  (at,atc,bt,btc)

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

   

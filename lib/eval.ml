
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

open Opetopes.Complex
open Opetopes.Idt

(*****************************************************************************)
(*                         Evaluation Utilities                              *)
(*****************************************************************************)

exception Eval_error of string

let ext_loc loc v i =
  if (i <= 0) then v
  else loc (i-1)

let emp_loc _ =
  raise (Eval_error "Empty local environment")

type fib_desc =
  | SigFib of name * value * value
  | PiFib of name * value * value
  | TypFib
  | NeutralFib

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

and get_fib_desc tl ty =
  match app_vars tl ty 0 with 
  | (SigV (nm,_,_),_) ->

    let ext_sig_src v =
      begin match v with
        | SigV (_,a,_) -> a
        | _ -> failwith "ext_sig_src"
      end in

    let ext_sig_tgt v = 
      begin match v with
        | SigV (nm,_,b) -> LamV (nm,b)
        | _ -> failwith "ext_sig_tgt"
      end in 

    let tlst = to_list tl in
    let a = map_fib tlst ty ext_sig_src in
    let b = map_fib tlst ty ext_sig_tgt in

    SigFib (nm,a,b)

  | (PiV (nm,_,_),_) ->

    let ext_pi_src v =
      begin match v with
        | PiV (_,a,_) -> a
        | _ -> failwith "ext_pi_src"
      end in

    let ext_pi_tgt v = 
      begin match v with
        | PiV (nm,_,b) -> LamV (nm,b)
        | _ -> failwith "ext_pi_tgt"
      end in 

    let tlst = to_list tl in
    let a = map_fib tlst ty ext_pi_src in
    let b = map_fib tlst ty ext_pi_tgt in

    PiFib (nm,a,b)

  | (TypV,_) -> TypFib
  | _ -> NeutralFib

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
  match c with
  | Base (Lf (vs,_)) ->
    app_to_fib (to_list vs) ty 
  | _ ->

    begin match get_fib_desc tl ty with

      | SigFib (nm,a,b) ->

        let src_typ = CellV (tl, a, fstC c) in
        let tgt_typ x = CellV (Ext (tl,(nm,a)), b, sndC c x)

        in SigV ("",src_typ,tgt_typ)

      | PiFib (nm,a,b) -> 

        let a_cell = cellC tl a (map_cmplx c ~f:fst) in
        piC a_cell (fun args ->
            CellV (Ext (tl, (nm, a)), b, appC c args))

      | TypFib ->
        let c' = tail_of c in
        let k _ = TypV in
        cell_univ c' k 

      (* begin match c' with
       *   | Base _ ->
       * 
       *     (\* Here, we should directly have access to the source and 
       *        target, and I think we just do things by hand ....
       *     *\)
       *     failwith "arrow case not done"
       *       
       *   | Adjoin (t,n) ->
       * 
       *     let k_nst t' =
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
       *               Some (addr, this_typ)) in 
       * 
       * 
       *       (\* But here we just have fibrations abstracted
       *          over the top level.  This doesn't seem right ...*\)
       *       let cmp_vals = map_nst typ_nst
       *           ~f:(fun opt ->
       *               begin match opt with
       *                 | Some (addr,fib) ->
       *                   
       *                   let kan_nst = apply_at_nst typ_nst addr
       *                       (fun _ -> None) in 
       *                   let kan_nds = List.filter_opt (nodes_nst kan_nst) in
       *                   
       *                   abst_type_lst kan_nds frm_cmplx
       *                     (fun _ -> fib)
       *                     
       *                 | None -> failwith "impossible"
       *               end) in 
       * 
       *       TypV 
       * 
       *     in cell_univ t k_nst *)

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

(* TODO: Combine the next two functions? *)
and app_vars t v i =
  match t with
  | Emp -> (v,i)
  | Ext (t',(_,_)) ->
    let (v',k) = app_vars t' v i in 
    (appV v' (varV k), k + 1)

and app_to_fib v_lst ty =
  match v_lst with
  | [] -> ty
  | v::vs -> app_to_fib vs (appV ty v)

and map_fib t v f =
  match t with
  | [] -> f v 
  | (nm,_)::tps ->
    LamV (nm,fun x ->
        let tps' = List.map tps ~f:(fun (nm,y) -> (nm,appV y x)) in
        let v' = appV v x in 
        map_fib tps' v' f)

and abst_type_lst nl cm k =
  match nl with
  | [] -> k cm
  | (addr,typ)::ns ->
    PiV ("", typ, fun v ->
        abst_type_lst ns
          (apply_at cm (0,addr)
             (fun (vs,_) -> (vs, Some v))) k)

(* A general routine for abstracting over the 
   variables of a complex.  This maybe belongs elsewhere ... *)
and abst_cmplx (tl : value tele) (ty : value)
    (c : value dep_term cmplx)
    (k : value dep_term cmplx -> value) : value =

  match c with
  | Base n ->

    let typ_nst = map_nst_with_addr n
        ~f:(fun (ts,_) addr ->
            let this_typ = app_to_fib (to_list ts) ty in
            (addr,this_typ)) in 

    abst_type_lst (nodes_nst typ_nst) (Base n) k 

  | Adjoin (t,n) -> 

    let k' t' = 

      let frm_cmplx = Adjoin (t',n) in

      let typ_nst = map_nst_with_addr n
          ~f:(fun (_,_) addr ->
              let f = face_at frm_cmplx (0,addr) in
              (* zero our the term position just in case ... *)
              let f' = with_head f
                  (map_nst (head_of f) ~f:(fun (vs,_) -> (vs,None))) in 
              let this_typ = CellV (tl,ty,f') 
              in (addr,this_typ))

      in abst_type_lst (nodes_nst typ_nst) frm_cmplx k 

    in abst_cmplx tl ty t k' 

(* Similar to above, but abstracts over a sequence of fibrations in 
   the universe ...*)

and cell_univ
    (c : value dep_term cmplx)
    (k : value dep_term cmplx -> value) =

  match c with
  | Base n ->

    let typ_nst = map_nst_with_addr n
        ~f:(fun (_,topt) addr ->
            let this_typ = Option.value_exn topt in
            (addr,this_typ)) in 

    abst_type_lst (nodes_nst typ_nst) (Base n) k

  | Adjoin (t,n) ->

    let k' t' =

      let frm_cmplx = Adjoin (t',n) in

      let typ_nst = map_nst_with_addr n
          ~f:(fun (_,fib_opt) addr ->
              let fib = Option.value_exn fib_opt in

              let f = face_at frm_cmplx (0,addr) in
              let args = List.map (labels (tail_of f))
                  ~f:(fun (_,tm_opt) ->
                      Option.value_exn tm_opt) in
              let this_typ = app_to_fib args fib in 
              (addr,this_typ))

      in abst_type_lst (nodes_nst typ_nst) frm_cmplx k

    in cell_univ t k' 


(*****************************************************************************)
(*                            Complex Combinators                            *)
(*****************************************************************************)

and fstC (c : value dep_term cmplx) : value dep_term cmplx
  = map_cmplx c
    ~f:(fun (vs,vo) -> (vs,Option.map vo ~f:fstV))

and sndC (c : value dep_term cmplx) (v : value) : value dep_term cmplx
  = map_cmplx c
    ~f:(fun (vs,vo) ->
        match vo with
        | None -> (Ext (vs,v),None)
        | Some p -> (Ext (vs,fstV p),Some (sndV p)))

(* This one is debateable.  Probably we should rather 
   adjoin the argument to the dep_term as a separate step ...*)
and appC (c : value dep_term cmplx) (arg_c : value cmplx) = 
  match_cmplx (face_cmplx arg_c) c
    ~f:(fun f (ss,so) ->
        let args = labels f in
        let top_arg = base_value (head_of f) in
        (Ext (ss,top_arg), Option.map so ~f:(app_to_fib args)))

(* Abstract over all the positions in a given complex and pass
   the abstracted values in complex form to the function b. *)
and lamC (a : 'a cmplx) (b : value cmplx -> value) : value =

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
    lamC t (fun vc -> do_lams (nodes_nst n') (Adjoin (vc,nv)))

(* Given the fibration a and a collection of cell values for the 
   telescopes, return the value cmplx whose cells are decorated 
   by the cell fibrations generated by a *)
and cellC (tl : value tele) (a : value) (args : value suite cmplx) : value cmplx =

  match args with
  | Base n ->

    let n' = map_nst n ~f:(fun vs -> app_to_fib (to_list vs) a) 
    in Base n'

  | Adjoin (t,n) ->

    let t' = cellC tl a t in

    let n' = map_nst_with_addr n
        ~f:(fun _ addr ->
            let f = face_at args (0,addr) in
            let f_tl = tail_of f in 
            let cell_fib = lamC f_tl (fun vc ->
                let dtc = match_cmplx vc f_tl
                    ~f:(fun v vs -> (vs,Some v)) in
                let hd = map_nst (head_of f)
                    ~f:(fun vs -> (vs,None)) in 
                CellV (tl,a, Adjoin (dtc,hd))) in
            cell_fib) in 

    Adjoin (t',n')

(* Given a "complex dependent type", extract the space 
   of sections of it with respect to the complex indexed 
   fibration b *)
and piC (a : value cmplx) (b : value cmplx -> value) : value =

  let rec do_pis nl cm =
    match nl with
    | [] -> b cm
    | (addr,typ)::ns ->
      PiV ("", typ, fun v ->
          do_pis ns (replace_at cm (0,addr) v))

  in match a with
  | Base n ->

    let n' = map_nst_with_addr n
        ~f:(fun typ addr -> (addr,typ)) in
    do_pis (nodes_nst n') a

  | Adjoin (t,n) ->

    piC t (fun vc ->

        let n' = map_nst_with_addr n
            ~f:(fun fib addr ->
                let f = face_at (Adjoin (vc,n)) (0,addr) in
                let f_tl = tail_of f in
                let typ = app_to_fib (labels f_tl) fib in 
                (addr,typ)) in

        do_pis (nodes_nst n') (Adjoin (vc,n))

      )

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



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

exception Eval_error of string

(*****************************************************************************)
(*                                Eliminators                                *)
(*****************************************************************************)

let rec app_val t u =
  match t with
  | RigidV (l,sp) -> RigidV (l,AppSp(sp,u))
  | ExpV (l,sp) -> ExpV (l,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), app_val tv u)
  | LamV (_,cl) -> cl u
  | _ -> raise (Eval_error (Fmt.str "malformed application: %a" pp_value t))

let (<@) = app_val 

let rec fst_val t =
  match t with
  | RigidV (l,sp) -> RigidV (l, FstSp sp)
  | ExpV (l,sp) -> ExpV (l, FstSp sp) 
  | TopV (nm,sp,tv) -> TopV (nm, FstSp sp, fst_val tv)
  | PairV (u,_) -> u
  | _ -> raise (Eval_error (Fmt.str "malformed first proj: %a" pp_value t))

let rec snd_val t =
  match t with
  | RigidV (l,sp) -> RigidV (l, SndSp sp)
  | ExpV (l,sp) -> ExpV (l, SndSp sp) 
  | TopV (nm,sp,tv) -> TopV (nm, SndSp sp, snd_val tv)
  | PairV (_,v) -> v
  | _ -> raise (Eval_error (Fmt.str "malformed second proj: %a" pp_value t))

(*****************************************************************************)
(*                            Opetopic Combinators                           *)
(*****************************************************************************)

let rec app_args f args =
  match args with
  | [] -> f
  | v::vs -> app_args (app_val f v) vs 

(* Abstract over all the positions in a given complex and pass
   the abstracted values in complex form to the function b. *)
let rec lam_cmplx (nm : name) (a : name cmplx) (b : value cmplx -> value) : value =

  let rec do_lams nl cm =
    match nl with
    | [] -> b cm
    | (cnm,addr)::addrs ->
      LamV (nm ^ cnm, fun v -> 
          do_lams addrs (replace_at cm (0,addr) v))

  in match a with
  | Base n ->
    let n' = map_nst_with_addr n
        ~f:(fun cnm addr -> (cnm,addr)) in
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    do_lams (nodes_nst n') (Base nv)
  | Adjoin (t,n) ->
    let n' = map_nst_with_addr n
        ~f:(fun cnm addr -> (cnm, addr)) in 
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    lam_cmplx nm t (fun vc -> do_lams (nodes_nst n') (Adjoin (vc,nv)))

(* Abstract a list of types, putting the abstracted 
   value at the appropriate address in the provided complex *)
let rec do_pis nl cm b =
  match nl with
  | [] -> b cm
  | (nm,addr,typ)::ns ->
    PiV (nm, typ, fun v ->
        do_pis ns (replace_at cm (0,addr) v) b)

(* Given a "complex dependent type", extract the space 
   of sections of it with respect to the complex indexed 
   fibration b *)
let rec pi_cmplx (nm : name) (cnms : name cmplx)
    (a : value cmplx) (b : value cmplx -> value) : value =
  
  match (a,cnms) with
  | (Base n , Base nms) ->

    let n' = match_nst_with_addr n nms
        ~f:(fun typ cnm addr -> (nm ^ cnm,addr,typ)) in 
    do_pis (nodes_nst n') a b

  | (Adjoin (t,n), Adjoin (tnms,nnms)) ->

    pi_cmplx nm tnms t (fun vc ->

        let n' = match_nst_with_addr n nnms
            ~f:(fun fib cnm addr ->
                let f = face_at (Adjoin (vc,n)) (0,addr) in
                let f_tl = tail_of f in
                let typ = app_args fib (labels f_tl) in 
                (nm ^ cnm,addr,typ)) in

        do_pis (nodes_nst n') (Adjoin (vc,n)) b

      )

  | _ -> raise (Eval_error "length mismatch in pi_cmplx")

(* b takes just the frame, leaving out the top cell ... *)
let pi_kan (nm : name) (cnms : name cmplx) 
    (addr : addr) (a : value cmplx) (b : value cmplx -> value) : value =
  
  match (a,cnms) with
  | (Base _ , _) -> failwith "Base in Kan abstraction"
  | (Adjoin (Base n , _) , Adjoin (Base nms , _)) ->

    let n' = match_nst_with_addr n nms
        ~f:(fun typ cnm addr -> (nm ^ cnm,addr,typ)) in 
    do_pis (nodes_nst_except n' addr) (Base n) b

  | (Adjoin (Adjoin (t,n),_) , Adjoin (Adjoin (tnms,nnms),_)) ->

    pi_cmplx nm tnms t (fun vc ->

        let n' = match_nst_with_addr n nnms
            ~f:(fun fib cnm addr ->
                let f = face_at (Adjoin (vc,n)) (0,addr) in
                let f_tl = tail_of f in
                let typ = app_args fib (labels f_tl) in 
                (nm ^ cnm,addr,typ)) in

        do_pis (nodes_nst_except n' addr) (Adjoin (vc,n)) b

      )

  | _ -> failwith "uneven complex in pi_kan"


(*****************************************************************************)
(*                         Implementation of Sigma                           *)
(*****************************************************************************)

let sig_fib afib bfib nm pi =
  lam_cmplx nm (tail_of pi) (fun pc ->
      
      (* extract the base values given in the abstraction *)
      let fstc = map_cmplx pc ~f:fst_val in
      
      (* apply them to the fibration to get at type *) 
      let atyp = app_args afib (labels fstc) in
      
      (* now sum over the result *)
      SigV (nm ^ (head_value pi), atyp, fun afst ->
          let sndc = map_cmplx pc ~f:snd_val in
          app_args (bfib (Adjoin (fstc, Lf afst))) (labels sndc)))

(*****************************************************************************)
(*                           Implementation of Pi                            *)
(*****************************************************************************)

let pi_fib acmplx bcmplx nm pi =
  lam_cmplx "f" (tail_of pi) (fun sc ->
      pi_cmplx nm pi acmplx (fun vc ->
          
          (* apply the arguments to the sections on the boundary *)
          let appc = match_cmplx sc (face_cmplx (tail_of vc))
              ~f:(fun s argc -> app_args s (labels argc)) in

          (* feed these to the fibration *) 
          app_args (bcmplx vc) (labels appc)))

(* let pi_comp acmplx bcmplx nm pi =
 *   failwith "not done ..."  *)

(*****************************************************************************)
(*                       Implementation of the Universe                      *)
(*****************************************************************************)

let typ_fib pi = 
  lam_cmplx "" (tail_of pi) (fun vc ->

      let cnms = map_cmplx pi ~f:(fun nm -> "el" ^ nm) in
      
      let dim = dim_cmplx vc in 
      let fst_vc = map_cmplx_with_addr vc
          ~f:(fun v (cd,_) ->
              if (cd = dim) then v else fst_val v) in 
      
      let fib = pi_cmplx "" (tail_of cnms) fst_vc (fun _ -> TypV) in
      
      (* FIXME: Dummy top cell to satsify pi_kan ...*)
      let comp = pi_kan "" cnms [] (Adjoin (fst_vc, Lf TypV)) (fun kc ->
          let cface = face_at kc (0,[]) in 
          let cfib = head_value cface in
          if (is_obj cface) then head_value cface
          else app_args cfib (labels (tail_of cface))) in
      
      let fill fibv compv = pi_kan "" cnms [] (Adjoin (fst_vc, Lf TypV)) (fun kc ->

          let kargs = 
            match kc with
            | Base n ->
              nodes_nst_except n [] 
            | Adjoin (t, n) ->
              List.append (labels t)
                (nodes_nst_except n [])
          in
          
          let kc' = replace_at kc (0,[]) (app_args compv kargs) in 
          app_args fibv (labels kc')

        ) in 

      
      SigV ("fib", fib, fun fibv ->
          SigV ("cmp", comp, fun compv ->
              fill fibv compv))
        
    )

type 'a cmplx_opt =
  | Obj of 'a
  | Arr of 'a * 'a * 'a
  | Cell of 'a cmplx * 'a nst * 'a

let get_cmplx_opt pi =
  match pi with
  | Base (Lf a) -> Obj a
  | Adjoin (Base (Nd (t, Nd (Lf s, Lf ()))), Lf a) ->
    Arr (s,t,a)
  | Adjoin (Adjoin (t,n), Lf a) ->
    Cell (t,n,a) 
  | _ -> failwith "complex match error"

let new_typ_fib o =
  let open ValSyntax in 
  match get_cmplx_opt o with
  | Obj _ -> TypV
  | Arr _ ->

    let efib atyp btyp = val_of (
        let* _ = pi "a" atyp in
        let* _ = pi "b" btyp in
        ret TypV 
      ) in
    
    let to_cmp atyp btyp _ = val_of (
        let* _ = pi "a" atyp in
        ret btyp 
      ) in 

    let to_fill atyp _ eqv cmp = val_of (
        let* a = pi "a" atyp in
        ret (eqv <@ a <@ (cmp <@ a))
      ) in 

    (* let to_cmpu atyp btyp eqv cmp fill =
     *   PiV ("a", atyp, fun a ->
     *       PiV ("b", btyp, fun b ->
     *           PiV ("e", app_val (app_val eqv a) b, fun e ->
     *               
     *               (\* So here I need the identity type, right ? *\)
     *               
     *               TypV) *)
    
    
    (* let from_cmp atyp btyp eqv = PiV ("b", btyp , fun _ -> atyp) in *)
    (* let from_fill atyp btyp eqv cmp =
     *   PiV ("b", btyp , fun b ->
     *       app_val (app_val eqv (app_val cmp b)) b) in *)

    val_of (
      let* atyp = lam "A" in
      let* btyp = lam "b" in
      let* eqv = sigma "E" (efib atyp btyp) in
      let* cmp = sigma "to_cmp" (to_cmp atyp btyp eqv) in
      let* _ = sigma "to_fill" (to_fill atyp btyp eqv cmp) in 
      ret TypV 
    )

  | Cell _ -> TypV
    
(*****************************************************************************)
(*                               Reflexivity                                 *)
(*****************************************************************************)

let rec refl_val opvs olvl v pi =
  (* log_val "refl_val/v" v pp_value; *)
  match v with
  
  | RigidV (k,sp) ->
    
    let init = if (is_obj pi) then EmpSp
      else ReflSp (EmpSp,pi) in
    let sp' = refl_sp opvs olvl init sp pi in
    RigidV (k,sp')
      
  | ExpV (k,sp) ->
    let sp' = refl_sp opvs olvl EmpSp sp pi in 
    run_sp (head_value (nth k opvs)) sp'
      
  | TopV (nm,sp,tv) ->
    TopV (nm,ReflSp (sp,pi), refl_val opvs olvl tv pi)

  | LamV (nm,bdy) ->

    if (is_obj pi) then v else 
    
      lam_cmplx nm pi (fun vc ->
          refl_val (Ext (opvs,vc)) (olvl+1)
            (bdy (expV olvl)) pi)

  | PairV (a,b) ->
          
    if (is_obj pi) then v else 

      let a' = refl_val opvs olvl a pi in
      let b' = refl_val opvs olvl b pi in
      PairV (a',b') 

  | PiV (nm,a,b) ->

    if (is_obj pi) then v else 

      let dim = dim_cmplx pi in 
      let acmplx = map_cmplx_with_addr
          (refl_faces opvs olvl a pi)
          ~f:(fun v (cd,_) ->
              if (cd = dim) then v
              else fst_val v) in

      let bcmplx vc = fst_val
          (refl_val (Ext (opvs,vc)) (olvl+1)
             (b (expV olvl)) pi) in

      mk_cell (pi_fib acmplx bcmplx nm pi)
        TypV TypV 

  | SigV (nm,a,b) -> 

    if (is_obj pi) then v else 

      let afib = fst_val (refl_val opvs olvl a pi) in
      let bfib vc = fst_val
          (refl_val (Ext (opvs, vc)) (olvl+1)
             (b (expV olvl)) pi) in

      mk_cell (sig_fib afib bfib nm pi)
        TypV TypV 

  | TypV ->

    if (is_obj pi) then v else
      
      mk_cell (typ_fib pi)
        TypV TypV 

and refl_sp opvs olvl init sp pi = 
  match sp with
  | EmpSp -> init
  | FstSp sp' -> FstSp (refl_sp opvs olvl init sp' pi)
  | SndSp sp' -> SndSp (refl_sp opvs olvl init sp' pi)
  | AppSp (sp',arg) -> 
    let sp'' = refl_sp opvs olvl init sp' pi in
    let argc = refl_faces opvs olvl arg pi in
    List.fold (labels argc) ~init:sp''
      ~f:(fun spa arg -> AppSp (spa,arg))
  | ReflSp (sp',pi') ->
    let sp'' = refl_sp opvs olvl init sp' pi in
    ReflSp (sp'',pi')

and run_sp v sp =
  match sp with
  | EmpSp -> v
  | FstSp sp' -> fst_val (run_sp v sp')
  | SndSp sp' -> snd_val (run_sp v sp')
  | AppSp (sp',arg) -> app_val (run_sp v sp') arg
  | ReflSp (sp',pi) -> refl_val Emp 0 (run_sp v sp') pi 

and refl_faces opvs olvl v pi =
  map_cmplx_with_addr pi
    ~f:(fun _ fa ->
        let face_env = map_suite opvs
            ~f:(fun c -> face_at c fa) in
        refl_val face_env olvl v (face_at pi fa))

and mk_cell fib comp fill =
  PairV (fib, PairV (comp,fill))

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let rec eval lvl top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  let ev t = eval lvl top loc t in
  let ev_bnd t v = eval lvl top (Ext (loc,v)) t in 
  match tm with
  
  | VarT i -> db_get i loc

  | TopT nm -> TopV (nm,EmpSp,top nm)

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
  | ExpV _ -> raise (Eval_error "quoting an expvar")

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



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
(*                           Opetopic Utilities                              *)
(*****************************************************************************)

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


(* convert a complex of cells in the universe to a complex of fibrations by projecting
   out the fibration in appropriate dimensions *)
let ucells_to_fib ucs =
  let dim = dim_cmplx ucs in 
  map_cmplx_with_addr ucs
    ~f:(fun v (cd,_) ->
        if (cd = dim) then v
        else fst_val v)


let rec app_args f args =
  match args with
  | [] -> f
  | v::vs -> app_args (app_val f v) vs 

let appc v vc = app_args v (labels vc)

(*****************************************************************************)
(*                            Opetopic Combinators                           *)
(*****************************************************************************)

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


let pi_pd (nm : name)
    (atnms : name cmplx) (at : value cmplx)
    (ahnms : name nst) (ah : value nst)
    (b : value cmplx * value nst -> value) : value = 
  let open ValSyntax in val_of (

    let frm = Adjoin (at,ah) in 
    let* vc = pi_cmplx nm atnms at in

    let ah' = match_nst_with_addr ah ahnms
        ~f:(fun fib cnm addr ->
            let f = face_at frm (0,addr) in
            let typ = appc fib (tail_of f) in
            (nm ^ cnm, addr, typ)
          ) in 
    
    ret (do_pis (nodes_nst_except ah' []) (Adjoin (vc,ah))
           (fun vc' -> b (tail_of vc',head_of vc')))

  )

(* value monad smart constructors *)
let lamc (nm : name) (a : name cmplx) : value cmplx valm =
  lam_cmplx nm a 

let pic (nm : name) (cnms : name cmplx) (a : value cmplx) : value cmplx valm =
  pi_cmplx nm cnms a 

let pic_kan (nm : name) (cnms : name cmplx) (addr : addr) (a : value cmplx) : value cmplx valm =
  pi_kan nm cnms addr a 
    
    
(*****************************************************************************)
(*                         Implementation of Sigma                           *)
(*****************************************************************************)

let sig_fib afib bfib nm pi =
  let open ValSyntax in val_of (
    
    let* pc = lamc nm (tail_of pi) in
    let fstc = map_cmplx pc ~f:fst_val in
    let atyp = appc (fst_val afib) fstc in
    let* afst = sigma (nm ^ head_value pi) atyp in
    let sndc = map_cmplx pc ~f:snd_val in
    let bres = fst_val (bfib (Adjoin (fstc, Lf afst))) in
    ret (appc bres sndc)

  )

(*****************************************************************************)
(*                           Implementation of Pi                            *)
(*****************************************************************************)

let pi_fib acmplx bcmplx nm pi =
  let open ValSyntax in val_of (

    let* sc = lamc "f" (tail_of pi) in
    let* vc = pic nm pi (ucells_to_fib acmplx) in
    let bargs = match_cmplx sc (face_cmplx (tail_of vc)) ~f:appc in
    ret (appc (fst_val (bcmplx vc)) bargs)

  )

(*****************************************************************************)
(*                               Reflexivity                                 *)
(*****************************************************************************)

let rec refl_val opvs olvl v pi =
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
    TopV (nm, ReflSp (sp,pi), refl_val opvs olvl tv pi)

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

      let acmplx = refl_faces opvs olvl a pi in
      let bcmplx vc = refl_val (Ext (opvs,vc)) (olvl+1)
                          (b (expV olvl)) pi in 

      mk_cell (pi_fib acmplx bcmplx nm pi)
        TypV TypV TypV 

  | SigV (nm,a,b) -> 

    if (is_obj pi) then v else 

      let afib = refl_val opvs olvl a pi in
      let bfib vc = refl_val (Ext (opvs, vc)) (olvl+1)
             (b (expV olvl)) pi in

      mk_cell (sig_fib afib bfib nm pi)
        TypV TypV TypV

  | TypV ->

    if (is_obj pi) then v else 
      mk_cell (typ_fib pi)
        TypV TypV TypV

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

and mk_cell fib comp fill unique =
  PairV (fib, PairV (comp,PairV (fill,unique)))

(* The identity type on a type value *) 
and id_typ v =
  let arr = arr_cmplx "x" "y" "p" in 
  fst_val (refl_val Emp 0 v arr)

(*****************************************************************************)
(*                       Implementation of the Universe                      *)
(*****************************************************************************)
    
and typ_fib o =
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

    let to_unique atyp btyp eqv cmp fill = val_of (
        let* a = pi "a" atyp in
        let* b = pi "b" btyp in
        let* e = pi "e" (eqv <@ a <@ b) in

        ret (id_typ
               (SigV ("b'", btyp, fun b' -> eqv <@ a <@ b'))
             <@ PairV (cmp <@ a, fill <@ a)
             <@ PairV (b,e))

      ) in 

    let from_cmp atyp btyp _ = val_of (
        let* _ = pi "b" btyp in
        ret atyp 
      ) in 

    let from_fill _ btyp eqv cmp = val_of (
        let* b = pi "b" btyp in
        ret (eqv <@ (cmp <@ b) <@ b)
      ) in 

    let from_unique atyp btyp eqv cmp fill = val_of (
        let* a = pi "a" atyp in
        let* b = pi "b" btyp in
        let* e = pi "e" (eqv <@ a <@ b) in

        ret (id_typ
               (SigV ("a'", atyp, fun a' -> eqv <@ a' <@ b))
             <@ PairV (cmp <@ b, fill <@ b)
             <@ PairV (a,e))

      ) in 

    val_of (
      let* atyp = lam "A" in
      let* btyp = lam "B" in
      let* eqv = sigma "E" (efib atyp btyp) in
      let* tcmp = sigma "to_cmp" (to_cmp atyp btyp eqv) in
      let* tfill = sigma "to_fill" (to_fill atyp btyp eqv tcmp) in
      let* _ = sigma "to_unique" (to_unique atyp btyp eqv tcmp tfill) in 
      let* fcmp = sigma "from_cmp" (from_cmp atyp btyp eqv) in
      let* ffill = sigma "from_fill" (from_fill atyp btyp eqv fcmp) in
      ret (from_unique atyp btyp eqv fcmp ffill)
    )

  | Cell (t,n,a) -> 

    let tnms = map_cmplx t ~f:(fun nm -> "el" ^ nm) in
    let nnms = map_nst n ~f:(fun nm -> "el" ^ nm) in
    let fnms = Adjoin (tnms,nnms) in 
    let frm = Adjoin (t,n) in

    let open ValSyntax in val_of (

      let* vc = lam_cmplx "" frm in
      let fibt = pic "" fnms vc (fun _ -> TypV) in

      let comp = val_of (

          let* (tv,hv) = pi_pd "" tnms (tail_of vc) nnms (head_of vc) in
          
          let cface = face_at (Adjoin (tv,hv)) (0,[]) in
          let cfib = head_value cface in
          
          ret (appc cfib (tail_of cface))

        ) in 

      let fill fib cmp = val_of (

          let* (tv,hv) = pi_pd "" tnms (tail_of vc) nnms (head_of vc) in

          let pd_args = List.append (labels tv)
              (nodes_nst_except hv []) in
          let hv' = with_base_value hv
              (app_args cmp pd_args)  in 

          ret (appc fib (Adjoin (tv,hv'))) 

        ) in 
      
      let unique fib cmp fil = val_of (

          let* els = pic "" (Adjoin (fnms,Lf ("el" ^ a))) (Adjoin (vc,Lf fib)) in

          let f = head_value els in
          let cface = face_at els (1,[]) in 
          let c = head_value cface in

          let cmpt = appc (head_value vc) (tail_of cface) in

          let tv = tail_of (tail_of els) in
          let hv = head_of (tail_of els) in
          let pd_args = List.append (labels tv)
              (nodes_nst_except hv []) in

          let cmp_el = app_args cmp pd_args in
          let fil_el = app_args fil pd_args in 

          ret (id_typ
                 (SigV ("c'", cmpt, fun c' ->
                      appc fib (replace_at (tail_of els) (0,[]) c')))

               <@ PairV (cmp_el , fil_el)
               <@ PairV (c,f))
            
        ) in 
      
      let* fib = sigma "fib" fibt in
      let* cmp = sigma "cmp" comp in
      let* fil = sigma "fil" (fill fib cmp) in 
      ret (unique fib cmp fil)

    ) 

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

let rec eval top loc tm =
  (* pr "Evaluating: %a@," pp_term tm; *)
  let ev t = eval top loc t in
  let ev_bnd t v = eval top (Ext (loc,v)) t in 
  match tm with
  
  | VarT i -> db_get i loc

  | TopT nm -> TopV (nm,EmpSp,top nm)
  | LetT (_,_,tm,bdy) -> ev_bnd bdy (ev tm) 

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



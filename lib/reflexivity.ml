(*****************************************************************************)
(*                                                                           *)
(*                              Reflexivity                                  *) 
(*                                                                           *)
(*****************************************************************************)

open Base
    
open Value
open Syntax
open Suite

open Opetopes.Idt
open Opetopes.Complex

open ValSyntax
    
(*****************************************************************************)
(*                    Preliminary Definitions and Lemmas                     *)
(*****************************************************************************)

let rec id_typ v =
  let arr = arr_cmplx "x" "y" "p" in 
  fst_val (refl_val Emp 0 v "arr" arr)

and is_contr tA = val_of (
    let* a = sigma "a" tA in
    let* b = pi "b" tA in
    ret (id_typ tA <@ a <@ b) 
  )

and has_all_paths tA = val_of (
    let* a = pi "a" tA in
    let* b = pi "b" tA in
    ret (id_typ tA <@ a <@ b)
  )

(*****************************************************************************)
(*                         Implementation of Sigma                           *)
(*****************************************************************************)

(* 
 * aeq is a cell in the universe of shape pi
 * beq is a fibration over that of the same shape
 *)

and sig_fib aeq beq nm pi = val_of (

    let* pc = lamc nm (tail_of pi) in
    let fstc = map_cmplx pc ~f:fst_val in
    let atyp = appc (fst_val aeq) fstc in
    let* afst = sigma (nm ^ head_value pi) atyp in
    let sndc = map_cmplx pc ~f:snd_val in
    let bres = fst_val (beq (Adjoin (fstc, Lf afst))) in
    ret (appc bres sndc)

  )
        
and sig_kan aeq beq _ pi = 
  match get_cmplx_opt pi with
  | Obj _ -> raise (Internal_error "Sigma kan on object")
  | Arr (snm,_,_) -> val_of (

      (* so, ab is the incoming pair ... *) 
      let* ab = lam snm in
      
      let a0 = fst_val ab in
      let b0 = snd_val ab in 

      let a_out_cont = fst_val (snd_val aeq) <@ a0 in
      
      let a = fst_val (fst_val a_out_cont) in
      let p = snd_val (fst_val a_out_cont) in

      let b_out_contr = fst_val (snd_val (beq (arr_cmplx a0 a p))) <@ b0 in 

      let b = fst_val (fst_val b_out_contr) in
      let q = snd_val (fst_val b_out_contr) in

      ret (PairV (PairV (a, b), PairV (p, q)))
      
    )
  | _ -> raise (Internal_error "higher sigma kan ops unimplemented")

(*****************************************************************************)
(*                           Implementation of Pi                            *)
(*****************************************************************************)

and pi_fib acmplx bcmplx nm pi = val_of (

    let* sc = lamc "f" (tail_of pi) in
    let* vc = pic nm pi (ucells_to_fib acmplx) in
    let bargs = match_cmplx sc (face_cmplx (tail_of vc)) ~f:appc in
    ret (appc (fst_val (bcmplx vc)) bargs)

  )

(*****************************************************************************)
(*                       Implementation of the Universe                      *)
(*****************************************************************************)

and univ_fib o =
  match get_cmplx_opt o with
  | Obj _ -> TypV
  | Arr _ -> val_of (

      let* atyp = lam "A" in
      let* btyp = lam "B" in
      
      let* e = sigma "E" (val_of (
          let* _ = pi "a" atyp in
          let* _ = pi "b" btyp in
          ret TypV)) in

      let u = val_of (
          let* a = pi "a" atyp in
          ret (is_contr (val_of (
              let* b = sigma "b" btyp in
              ret (e <@ a <@ b)
            )))) in

      let v = val_of (
          let* b = pi "b" btyp in
          ret (is_contr (val_of (
              let* a = sigma "a" atyp in
              ret (e <@ a <@ b)
            )))) in 
      
      ret (prod u v)

    ) 

  | Cell (t,n,_) -> 

    (* TODO: This needs more testing now that it has been rewritten 
             in this newer, more succinct style ... *) 
    let tnms = map_cmplx t ~f:(fun nm -> "el" ^ nm) in
    let nnms = map_nst n ~f:(fun nm -> "el" ^ nm) in
    let fnms = Adjoin (tnms,nnms) in 
    let frm = Adjoin (t,n) in

    val_of (

      let* vc = lam_cmplx "" frm in
      let fvc = ucells_to_fib vc in

      let* e = sigma "E" (val_of (
          let* _ = pic "" fnms fvc in
          ret TypV
        )) in 

      let* (tv,hv) = pi_pd "" tnms (tail_of fvc) nnms (head_of fvc) in

      let cface = face_at (Adjoin (tv,hv)) (0,[]) in
      let cfib = head_value cface in

      ret (is_contr (val_of (

          let* cmp = sigma "cmp" (appc cfib (tail_of cface)) in
          let hv' = with_base_value hv cmp in 
          ret (appc e (Adjoin (tv,hv')))

        )))

    ) 

(*****************************************************************************)
(*                               Reflexivity                                 *)
(*****************************************************************************)

and refl_val opvs olvl v pi_nm pi =
  (* log_val "v" v pp_value ;
   * log_val "olvl" olvl Fmt.int ;  *)
  match v with

  | RigidV (k,sp) ->
    let sp' = refl_sp opvs olvl (not (is_obj pi)) sp pi_nm pi in
    RigidV (k,sp')

  | ExpV (k,sp) ->

    begin try 
        let sp' = refl_sp opvs olvl false sp pi_nm pi in 
        run_sp (head_value (nth k opvs)) sp'
      with Lookup_error ->
        let msg = Fmt.str
            "@[<v>Impossible exp level: %d@,
                  pi: %a@,
                  olvl: %d@]"
            k (pp_cmplx Fmt.string) pi olvl in
        
        raise (Internal_error msg)
    end
    

  | TopV (nm,sp,tv) ->
    let sp' = refl_sp opvs olvl (not (is_obj pi)) sp pi_nm pi in
    TopV (nm, sp', refl_val opvs olvl tv pi_nm pi)

  | LamV (nm,bdy) ->

    if (is_obj pi) then v else 
      lam_cmplx nm pi (fun vc ->
          refl_val (Ext (opvs,vc)) (olvl+1)
            (bdy (expV olvl)) pi_nm pi)

  | PairV (a,b) ->

      let a' = refl_val opvs olvl a pi_nm pi in
      let b' = refl_val opvs olvl b pi_nm pi in
      PairV (a',b') 

  | PiV (nm,a,b) ->

    if (is_obj pi) then v else
      
      let acmplx = refl_faces opvs olvl a pi in
      let bcmplx vc = refl_val (Ext (opvs,vc)) (olvl+1)
          (b (expV olvl)) pi_nm pi in 

      mk_cell (pi_fib acmplx bcmplx nm pi)
        TypV TypV TypV 

  | SigV (nm,a,b) -> 

    if (is_obj pi) then v else
      
      let afib = refl_val opvs olvl a pi_nm pi in
      let bfib vc = refl_val (Ext (opvs, vc)) (olvl+1)
          (b (expV olvl)) pi_nm pi in

      mk_cell (sig_fib afib bfib nm pi)
        TypV TypV TypV

  | TypV ->

    if (is_obj pi) then v else 
      mk_cell (univ_fib pi)
        TypV TypV TypV

and refl_sp opvs olvl ext sp pi_nm pi = 
  match sp with
  | EmpSp -> if ext then ReflSp (EmpSp,pi_nm,pi) else EmpSp 
  | FstSp sp' -> FstSp (refl_sp opvs olvl ext sp' pi_nm pi)
  | SndSp sp' -> SndSp (refl_sp opvs olvl ext sp' pi_nm pi)
  | AppSp (sp',arg) -> 
    let sp'' = refl_sp opvs olvl ext sp' pi_nm pi in
    let argc = refl_faces opvs olvl arg pi in
    List.fold (labels argc) ~init:sp''
      ~f:(fun spa arg -> AppSp (spa,arg))
  | ReflSp _ as rsp ->
    if ext then ReflSp (rsp,pi_nm,pi) else rsp 

and run_sp v sp =
  match sp with
  | EmpSp -> v
  | FstSp sp' -> fst_val (run_sp v sp')
  | SndSp sp' -> snd_val (run_sp v sp')
  | AppSp (sp',arg) -> app_val (run_sp v sp') arg
  | ReflSp (sp',pi_nm,pi) -> refl_val Emp 0 (run_sp v sp') pi_nm pi 

and refl_faces opvs olvl v pi =
  map_cmplx_with_addr pi
    ~f:(fun _ fa ->
        let face_env = map_suite opvs
            ~f:(fun c -> face_at c fa) in
        refl_val face_env olvl v "" (face_at pi fa))

and mk_cell fib comp fill unique =
  PairV (fib, PairV (comp,PairV (fill,unique)))


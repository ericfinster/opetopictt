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
  fst_val (refl_val Emp 0 v arr)

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

and sig_fib afib bfib nm pi = val_of (

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

and refl_val opvs olvl v pi =
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
    (* We treat top here just like rigid above.  This seems to have
       fixed some un-evaluated exp vars.  But I'm not 100% sure on
       this .... *) 
    let init = if (is_obj pi) then EmpSp
      else ReflSp (EmpSp,pi) in
    let sp' = refl_sp opvs olvl init sp pi in
    TopV (nm, sp', refl_val opvs olvl tv pi)

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
      mk_cell (univ_fib pi)
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


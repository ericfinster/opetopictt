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

    val_of (

      let* vc = lam_cmplx "" frm in
      let fvc = ucells_to_fib vc in 
      let fibt = pic "" fnms fvc (fun _ -> TypV) in

      let comp = val_of (

          let* (tv,hv) = pi_pd "" tnms (tail_of fvc) nnms (head_of fvc) in

          let cface = face_at (Adjoin (tv,hv)) (0,[]) in
          let cfib = head_value cface in

          ret (appc cfib (tail_of cface))

        ) in 

      let fill fib cmp = val_of (

          let* (tv,hv) = pi_pd "" tnms (tail_of fvc) nnms (head_of fvc) in

          let pd_args = List.append (labels tv)
              (nodes_nst_except hv []) in
          let hv' = with_base_value hv
              (app_args cmp pd_args)  in 

          ret (appc fib (Adjoin (tv,hv')))

        ) in 

      (* TODO: I'm worried about the application of "fst"s to the fibrations here .. *)
      let unique fib cmp fil = val_of (

          let* els = pic "" (Adjoin (fnms,Lf ("el" ^ a))) (Adjoin (fvc,Lf fib)) in

          let f = head_value els in
          let cface = face_at els (1,[]) in 
          let c = head_value cface in

          let cmpt = appc (head_value fvc) (tail_of cface) in

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


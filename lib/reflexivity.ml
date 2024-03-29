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

and refl_sig aeq beq nm pi =

  (* The relation in a sigma type for positive dimensional cells *) 
  let sig_rel _ = val_of (

      let* pc = lamc nm (tail_of pi) in
      let fstc = map_cmplx pc ~f:fst_val in
      let atyp = appc (fst_val aeq) fstc in
      let* afst = sigma (nm ^ head_value pi) atyp in
      let sndc = map_cmplx pc ~f:snd_val in
      let bres = fst_val (beq (Adjoin (fstc, Lf afst))) in
      ret (appc bres sndc)

  ) in 
  
  begin match get_cmplx_opt pi with
    
    | Obj nm -> val_of (
        
        let* a = sigma nm aeq in
        ret (beq (Base (Lf a)))
          
      )
        
    | Arr (_,_,_) ->

      (* let to_kan = val_of (
       * 
       *     let* ab = lam snm in
       * 
       *     let a0 = fst_val ab in
       *     let b0 = snd_val ab in 
       * 
       *     let a_out_cont = fst_val (snd_val aeq) <@ a0 in
       * 
       *     let a = fst_val (fst_val a_out_cont) in
       *     let p = snd_val (fst_val a_out_cont) in
       * 
       *     let b_out_contr = fst_val (snd_val (beq (arr_cmplx a0 a p))) <@ b0 in 
       * 
       *     let b = fst_val (fst_val b_out_contr) in
       *     let q = snd_val (fst_val b_out_contr) in
       * 
       *     let exists = PairV (PairV (a, b), PairV (p, q)) in
       *     let unique = TypV in
       *     
       *     ret (PairV (exists, unique))
       * 
       *   ) in  *)

      let to_kan = TypV in 
      let from_kan = TypV in
      let is_kan = PairV (to_kan, from_kan) in 
      PairV (sig_rel (), is_kan)
    
    | Cell _ ->

      let is_kan = TypV in
      PairV (sig_rel (), is_kan)
        
  end
  
(*****************************************************************************)
(*                           Implementation of Pi                            *)
(*****************************************************************************)

and refl_pi acmplx bcmplx nm op =

  let pi_rel _ = val_of (

      (* assumes pi is not an object ... *) 
      let* sc = lamc "f" (tail_of op) in
      let* vc = pic nm op (ucells_to_fib acmplx) in
      let bargs = match_cmplx sc (face_cmplx (tail_of vc)) ~f:appc in
      ret (appc (fst_val (bcmplx vc)) bargs)

  ) in

  begin match get_cmplx_opt op with
    
    | Obj _ -> val_of (
        let* a = pi nm (head_value acmplx) in
        ret (bcmplx (Base (Lf a)))
      )
        
    | Arr _ ->

      let to_kan = TypV in
      let from_kan = TypV in 
      let is_kan = PairV (to_kan, from_kan) in
      PairV (pi_rel () , is_kan)
        
    | Cell _ ->

      let is_kan = TypV in
      PairV (pi_rel () , is_kan)

  end

(*****************************************************************************)
(*                       Implementation of the Universe                      *)
(*****************************************************************************)

and refl_univ o =
  match get_cmplx_opt o with
  | Obj _ -> TypV
  | Arr _ ->

    let arr_fib = val_of (

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

    ) in

    let to_kan = TypV in
    let from_kan = TypV in 
    let is_kan = PairV (to_kan, from_kan) in
    PairV (arr_fib , is_kan)

  | Cell (t,n,_) -> 

    (* TODO: This needs more testing now that it has been rewritten 
             in this newer, more succinct style ... *) 
    let tnms = map_cmplx t ~f:(fun nm -> "el" ^ nm) in
    let nnms = map_nst n ~f:(fun nm -> "el" ^ nm) in
    let fnms = Adjoin (tnms,nnms) in 
    let frm = Adjoin (t,n) in

    let cell_fib = val_of (

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

    ) in

    let is_kan = TypV in
    
    PairV (cell_fib , is_kan) 

(*****************************************************************************)
(*                               Reflexivity                                 *)
(*****************************************************************************)

and refl_val opvs olvl v pi_nm pi =
  (* Fmt.pr "@[<v>v: %a@;olvl: %d@;opvs: %a@]@;"
   *   pp_value v olvl (Fmt.vbox (pp_suite ~sep:(Fmt.cut) (pp_cmplx pp_value))) opvs ; *)
  (* log_val "v" v pp_value ;
   * log_val "olvl" olvl Fmt.int ;
   * log_val "opvs" opvs (Fmt.vbox (pp_suite ~sep:(Fmt.cut) (pp_cmplx pp_value))) ;  *)
  match v with

  | RigidV (k,sp) ->

    (* log_msg "RIGID"; *)
    
    let sp' = refl_sp opvs olvl
        (not (is_obj pi)) sp pi_nm pi in
    
    RigidV (k,sp')

  | ExpV (k,sp) ->

    (* log_msg "EXPVAR"; *)
    
    begin try
        (* We *never* accumulate the refl in this case, since the value
           should already be of the correct cell type.  Rather here we
           just want to re-run refl on the spine .... *) 
        let sp' = refl_sp opvs olvl false sp pi_nm pi in 
        run_sp (head_value (nth k opvs)) sp'
      with Lookup_error ->
        let msg = Fmt.str "@[<v>Impossible exp level: %d@,pi: %a@,olvl: %d@]"
            k (pp_cmplx Fmt.string) pi olvl in
        
        raise (Internal_error msg)
    end
    

  | TopV (_,_,tv) ->

    (* log_msg "TOP" ;  *)
    (* log_msg "in top, running spine";
     * let sp' = refl_sp opvs olvl (not (is_obj pi)) sp pi_nm pi in
     * log_msg "spine finished, running ufold"; *)
    let tv' = refl_val opvs olvl tv pi_nm pi in
    (* log_msg "unfold completed"; *)
    (* TopV (nm, sp', tv') *)
    tv'

  | LamV (nm,bdy) ->

    (* log_msg "LAM" ;  *)
    
    let r = lam_cmplx nm pi (fun vc ->
        (* log_val "vc" vc (pp_cmplx pp_value) ;  *)
        refl_val (Ext (opvs,vc)) (olvl+1)
          (bdy (expV olvl)) pi_nm pi) in
      
    r

  | PairV (a,b) ->

    (* log_msg "PAIR" ; *)
    
    let a' = refl_val opvs olvl a pi_nm pi in
    let b' = refl_val opvs olvl b pi_nm pi in
    PairV (a',b') 

  | PiV (nm,a,b) ->

    (* log_msg "PI" ;  *)
    
    if (is_obj pi) then v else 
      let acmplx = refl_faces opvs olvl a pi in
      let bcmplx vc = refl_val (Ext (opvs,vc)) (olvl+1)
          (b (expV olvl)) pi_nm pi in 
      
      let r = refl_pi acmplx bcmplx nm pi in
      r

  | SigV (nm,a,b) -> 

    (* log_msg "SIG" ; *)
    
    let aeq = refl_val opvs olvl a pi_nm pi in
    let beq vc = refl_val (Ext (opvs, vc)) (olvl+1)
        (b (expV olvl)) pi_nm pi in

    refl_sig aeq beq nm pi

  | TypV ->
    (* log_msg "TYP" ; *)
    refl_univ pi 

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
        (* log_val "face_env" face_env (Fmt.vbox (pp_suite ~sep:(Fmt.cut) (pp_cmplx pp_value))) ;  *)
        refl_val face_env olvl v "" (face_at pi fa))

and mk_cell fib comp fill unique =
  PairV (fib, PairV (comp,PairV (fill,unique)))


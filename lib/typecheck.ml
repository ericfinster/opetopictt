(*****************************************************************************)
(*                                                                           *)
(*                           Typechecking Routines                           *)
(*                                                                           *)
(*****************************************************************************)

open Fmt

open Base
open Suite
open Expr
open Term
open Value
open Eval
open Syntax

open Opetopes.Idt
open Opetopes.Complex

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type ctx = {
  top : (name * (value * value)) suite;
  loc : (name * (value * value)) suite;
  lvl : lvl;
}

let empty_ctx = {
  top = Emp;
  loc = Emp;
  lvl = 0;
}

let empty_loc gma = {
  top = gma.top;
  loc = Emp;
  lvl = 0;
}

let bind gma nm ty =
  let l = gma.lvl in {
    loc = Ext (gma.loc, (nm , (varV l , ty)));
    top = gma.top;
    lvl = l+1;
  }

let define gma nm tm ty = {
  loc = gma.loc;
  top = Ext (gma.top,(nm,(tm,ty)));
  lvl = gma.lvl;
}

let names gma =
  map_suite gma.loc ~f:fst

(* TODO: Use different error reporting here? *)

let loc_lookup gma i =
  try fst (snd (db_get i gma.loc))
  with Lookup_error ->
    raise (Eval_error (str "Index out of range: %d" i))

let top_lookup gma nm = 
  try fst (assoc nm gma.top)
  with Lookup_error ->
    raise (Eval_error (str "Unknown id during eval: %s" nm))

(*****************************************************************************)
(*                               Typing Errors                               *)
(*****************************************************************************)
           
type typing_error = [
  | `NameNotInScope of name
  | `TypeMismatch of expr * expr * expr
  | `NotImplemented of string
  | `InferrenceFailed of expr
  | `ExpectedFunction of expr
  | `ExpectedProduct of expr 
  | `InvalidShape of string 
  | `InternalError of string 
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm ->
    
    Fmt.pf ppf "Name not in scope: %s" nm
      
  | `TypeMismatch (e,exp,inf) ->

    Fmt.pf ppf "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
    Fmt.pf ppf "@[<v>has type: @,@, @[%a@]@,@,@]" pp_expr inf;
    Fmt.pf ppf "@[<v>but was expected to have type: @,@, @[%a@]@,@]" pp_expr exp;

  | `NotImplemented f ->

    Fmt.pf ppf "Feature not implemented: %s" f
      
  | `InferrenceFailed e ->

    Fmt.pf ppf "Failed to infer the type of: %a" pp_expr e
      
  | `ExpectedFunction e -> 

    Fmt.pf ppf "The expression @,@, @[%a@] @,@," pp_expr e ;
    Fmt.pf ppf "was expected to be a function but isn.t"

  | `ExpectedProduct e -> 

    Fmt.pf ppf "The expression @,@, @[%a@] @,@," pp_expr e ;
    Fmt.pf ppf "was expected to be a product but isn.t"

  | `InvalidShape msg -> pf ppf "Shape error: %s" msg 

  | `InternalError msg -> Fmt.pf ppf "Internal Error: %s" msg 


(*****************************************************************************)
(*                            Typechecking Monad                             *)
(*****************************************************************************)

type 'a tcm = ctx -> ('a , typing_error) Result.t

module TcmBasic = 
  struct

    type 'a t = 'a tcm
        
    let return a _ = Ok a
    let bind m ~f:f gma =
      match m gma with
      | Ok x -> f x gma 
      | Error e -> Error e

    let map m ~f:f gma =
      Result.map (m gma) ~f:f

    let map = `Custom map

    let apply mf ma =
      bind mf ~f:(fun f ->
          bind ma ~f:(fun a ->
              return (f a)))
      
  end
  
module TcmMonad = Monad.Make(TcmBasic) 
module TcmApplicative = Applicative.Make(TcmBasic)
module TcmTraverse = TreeTraverse(TcmBasic) 
module TcmComplexTraverse = ComplexTraverse(TcmBasic)

let (let*) m f = TcmMonad.bind m ~f 
let tcm_ok = TcmMonad.return 
let tcm_fail e _ = Error e 

let tcm_ctx : ctx tcm =
  fun gma -> Ok gma
      
let tcm_eval (t : term) : value tcm =
  let* gma = tcm_ctx in
  tcm_ok (eval (top_lookup gma)
            (loc_lookup gma) t)

let tcm_quote (v : value) : term tcm =
  let* gma = tcm_ctx in
  tcm_ok (quote false gma.lvl v)

let tcm_in_ctx g m _ = m g 

let tcm_with_binding nm ty m =
  let* gma = tcm_ctx in
  tcm_in_ctx (bind gma nm ty) m 

let rec tcm_extract_pi (v: value) =
  match v with
  | PiV (_,a,b) -> tcm_ok (a, b)
  | TopV (_,_,v') -> tcm_extract_pi v'
  | _ ->
    let* gma = tcm_ctx in 
    let e = term_to_expr (names gma) (quote false gma.lvl v) in 
    tcm_fail (`ExpectedFunction e) 

let rec tcm_extract_sig (v: value) =
  match v with
  | SigV (_,a,b) -> tcm_ok (a, b)
  | TopV (_,_,v') -> tcm_extract_sig v'
  | _ ->
    let* gma = tcm_ctx in 
    let e = term_to_expr (names gma) (quote false gma.lvl v) in 
    tcm_fail (`ExpectedProduct e) 

let tcm_ensure (b : bool) (e : typing_error) : unit tcm =
  if b then tcm_ok ()
  else tcm_fail e
      
(*****************************************************************************)
(*                            Typechecking Rules                             *)
(*****************************************************************************)

let rec tcm_check (e : expr) (t : value) : term tcm =

  match (e , t) with

  | (e , TopV (_,_,tv)) -> tcm_check e tv

  | (LamE (nm,e) , PiV (_,a,b)) ->
    let* gma = tcm_ctx in
    tcm_in_ctx (bind gma nm a)
      begin
        let* bdy = tcm_check e (b (varV gma.lvl)) in
        tcm_ok (LamT (nm,bdy))
      end

  | (PairE (u,v) , SigV (_,a,b)) ->
    let* u' = tcm_check u a in
    let* uv = tcm_eval u' in
    let* v' = tcm_check v (b uv) in
    tcm_ok (PairT (u',v')) 

  | (e, expected) ->

    let* gma = tcm_ctx in 
    let* (e',inferred) = tcm_infer e in

    let inferred_nf = quote true gma.lvl inferred in
    let expected_nf = quote true gma.lvl expected in

    if (not (term_eq expected_nf inferred_nf)) 
    then
      let exp_e = term_to_expr (names gma) expected_nf in
      let inf_e = term_to_expr (names gma) inferred_nf in
      tcm_fail (`TypeMismatch (e,exp_e,inf_e))
    else tcm_ok e'

and tcm_infer (e : expr) : (term * value) tcm =

  match e with

  | VarE nm ->
    let* gma = tcm_ctx in
    begin try
        let (idx,(_,ty)) = assoc_with_idx nm gma.loc in
        tcm_ok (VarT idx, ty)
      with Lookup_error ->
        begin try 
            let (_, ty) = assoc nm gma.top in
            tcm_ok (TopT nm, ty)
          with Lookup_error -> tcm_fail (`NameNotInScope nm)
        end
    end

  | AppE (u,v) ->

    let* (u',ut) = tcm_infer u in
    let* (a , b) = tcm_extract_pi ut in
    let* v' = tcm_check v a in
    let* vv = tcm_eval v' in 
    tcm_ok (AppT (u',v') , b vv)

  | PiE (nm,a,b) ->
    let* a' = tcm_check a TypV in
    let* av = tcm_eval a' in
    let* b' = tcm_with_binding nm av
        (tcm_check b TypV) in 

    tcm_ok (PiT (nm,a',b') , TypV)

  | FstE u ->
    let* (u',ut) = tcm_infer u in
    let* (a, _) = tcm_extract_sig ut in
    tcm_ok (FstT u', a)

  | SndE u ->
    let* (u',ut) = tcm_infer u in
    let* (_, b) = tcm_extract_sig ut in
    let* uv = tcm_eval u' in
    tcm_ok (SndT u', b (fstV uv))

  | SigE (nm,a,b) ->
    let* a' = tcm_check a TypV in
    let* av = tcm_eval a' in
    let* b' = tcm_with_binding nm av
        (tcm_check b TypV) in 

    tcm_ok (SigT (nm,a',b') , TypV)

  | CellE (tl,ty,c) ->

    let* (tm_tl, tm_ty, val_tl, val_ty) =
      tcm_check_fib tl ty in
    
    let* c' = tcm_to_cmplx c in 
    let* (c'',_) = tcm_check_cmplx val_tl val_ty c' in

    let* _ = tcm_ensure ((List.length (empty_addrs (head_of c''))) = 1)
        (`InternalError "top dim not empty in cell") in
    
    tcm_ok (CellT (tm_tl,tm_ty,c''), TypV)

  | CompE (tl,ty,c) ->

    let* (tm_tl,tm_ty,tm_c,val_tl,val_ty,val_c,kan_addr) =
      tcm_check_kan tl ty c in

    let cmp_face = face_at val_c (1,kan_addr) in
    let cmp_ty = cellV val_tl val_ty cmp_face in 
    
    tcm_ok (CompT (tm_tl,tm_ty,tm_c) , cmp_ty)

  | FillE (tl,ty,c) ->

    let* (tm_tl,tm_ty,tm_c,val_tl,val_ty,val_c,kan_addr) =
      tcm_check_kan tl ty c in

    let cmp_tm = CompT (tm_tl,tm_ty,tm_c) in
    let* cmp_val = tcm_eval cmp_tm in
    let val_c' = apply_at val_c (1,kan_addr)
        (fun (vs,_) -> vs, Some cmp_val) in
    let fill_ty = CellV (val_tl,val_ty,val_c') in 
    
    tcm_ok (FillT (tm_tl,tm_ty,tm_c) , fill_ty)

  | KanElimE (tl,ty,c,p,d,comp,fill) ->

    let* (tm_tl,tm_ty,tm_c,val_tl,val_ty,val_c,kan_addr) =
      tcm_check_kan tl ty c in
    
    let cmp_face = face_at val_c (1,kan_addr) in
    let cmp_ty = cellV val_tl val_ty cmp_face in 

    let fill_fib v = 
      let fill_cmplx = apply_at val_c (1,kan_addr)
          (fun (vs,_) -> vs , Some v) in
      cellV val_tl val_ty fill_cmplx in 

    let p_ty =
      PiV ("c", cmp_ty,
           fun c ->
             PiV ("f", fill_fib c, fun _ -> TypV)) in
    
    let* p' = tcm_check p p_ty in
    let* pv = tcm_eval p' in

    let canon_comp_val = CompV (val_tl,val_ty,val_c) in
    let canon_fill_val = FillV (val_tl,val_ty,val_c) in

    let* d' = tcm_check d (appV (appV pv canon_comp_val)
                             canon_fill_val) in

    let* comp' = tcm_check comp cmp_ty in
    let* comp_val = tcm_eval comp' in 
    
    let* fill' = tcm_check fill (fill_fib comp_val) in 
    let* fill_val = tcm_eval fill' in 
    
    tcm_ok (KanElimT (tm_tl,tm_ty,tm_c,p',d',comp',fill'),
            appV (appV pv comp_val) fill_val)

  | TypE -> tcm_ok (TypT , TypV)

  | _ -> tcm_fail (`InferrenceFailed e) 

and tcm_to_cmplx c =
  let open IdtConv in 
  try let c' = to_cmplx c in
    let _ = validate_opetope c' in 
    tcm_ok c' 
  with TreeExprError msg -> tcm_fail (`InvalidShape msg)
     | ShapeError msg -> tcm_fail (`InvalidShape msg) 

and tcm_check_dep_term (s : expr list) (tm_opt : expr option)
    (tl : value list) (ty : value) : (term list * term option) tcm =
  log_msg (Fmt.str "checking dependent term: @[%a \u{22a2} %a@]"
             (Fmt.list ~sep:(any " ; ") pp_expr) s 
             (Fmt.option pp_expr) tm_opt); 
  match (s,tl) with
  | ([],[]) ->
    begin match tm_opt with
      | None -> tcm_ok ([],None)
      | Some tm ->
        let* t = tcm_check tm ty in 
        tcm_ok ([],Some t)
    end
  | (e::es , v::vs) ->
    let* t = tcm_check e v in
    let* tv = tcm_eval t in
    let vs' = List.map vs ~f:(fun v -> appV v tv) in
    let* (ltm, dtm) = tcm_check_dep_term es tm_opt vs' (appV ty tv) in
    tcm_ok (t::ltm,dtm)

  (* TODO: this should be named ... *)
  | _ -> tcm_fail (`InternalError "context mismatch in check_dep_term")

and tcm_check_cmplx (tl : value tele) (ty : value) (c : expr dep_term cmplx)
  : (term dep_term cmplx * value dep_term cmplx) tcm =

  match c with
  | Base n ->

    let* n' = TcmTraverse.traverse_nst n
        ~f:(fun (e_suite,e_opt) ->
            let* (tm_list,tm_opt) = tcm_check_dep_term (to_list e_suite)
                e_opt (to_list (map_suite tl ~f:snd)) ty in
            let tm_suite = from_list tm_list in
            let* gma = tcm_ctx in
            let eval_tm = eval (top_lookup gma) (loc_lookup gma) in 
            let val_suite = map_suite tm_suite ~f:eval_tm in 
            let val_opt = Option.map tm_opt ~f:eval_tm in 
            tcm_ok ((tm_suite,tm_opt),(val_suite,val_opt))) in 

    let (nt,nv) = unzip_nst n' in 
    tcm_ok (Base nt , Base nv)

  | Adjoin (t,n) ->
    
    let* (tt,tv) = tcm_check_cmplx tl ty t in
    
    (* Let's check that the top guys is full here ... *)
    let eaddrs = empty_addrs (head_of tt) in 
    let* _ = tcm_ensure (List.is_empty eaddrs)
        (`InternalError "fullness error") in

    let* (tm_n , val_c) = tcm_check_extension tl ty tv n in
    tcm_ok (Adjoin (tt,tm_n) , val_c) 

and tcm_check_extension (tl : value tele) (ty : value) (tv : value dep_term cmplx)
    (n : expr dep_term nst)
  : (term dep_term nst * value dep_term cmplx) tcm =

  let* gma = tcm_ctx in 

  (* Okay, now we build the next typing problem *) 
  let fibs = sub_teles tl ty in
  let tele_args t = map_with_lvl t ~f:(fun l _ -> varV (gma.lvl + l)) in 
  let dep_vars = map_suite fibs
      ~f:(fun (tys,_) -> (tele_args tys, None)) in 
  let ts = map_cmplx tv ~f:sub_terms in
  let ntms = map_nst n ~f:(fun _ -> dep_vars) in
  let tv_cmplx = Adjoin (ts,ntms) in

  let t_cmplx = map_cmplx tv_cmplx
      ~f:(fun dep_tms -> map_with_lvl dep_tms
             ~f:(fun l (v_suite,v_opt) ->
                 let t_suite = map_suite v_suite ~f:(quote false (gma.lvl + l)) in
                 let t_opt = Option.map v_opt ~f:(quote false (gma.lvl + l)) in
                 (t_suite,t_opt)
               )) in

  let tm_fibs = map_with_lvl fibs
      ~f:(fun l (v_tl,v_ty) ->
          quote_fib false (gma.lvl + l) v_tl v_ty) in 

  (* We now traverse the expression nesting and try to set up 
   * a list of typing problems for each face *) 
  let* r = TcmTraverse.traverse_nst_with_addr n
      ~f:(fun (es,eo) addr ->

          (* log_msg "in face problem";
           * log_val "e" (es,eo) (pp_dep_term pp_expr); *)

          let f = face_at t_cmplx (0,addr) in
          match (split_cmplx f tm_fibs (fun x _ -> x) , tm_fibs) with
          | (Ext (p,q) , Ext (tm_fibs',(qtl,qty))) -> 

            (* Oh. since we've matched on one value for f, we have 
               to do the same for fibs and tl I think .... *)
            let cell_tl = map_suite (zip (zip tl tm_fibs') p)
                ~f:(fun (((nm,_),(ltl,lty)),c) -> (nm,CellT (ltl,lty,c))) in

            (* log_val "cell_tl" cell_tl (pp_tele pp_term); *)

            let (val_tl, val_ty) =
              eval_fib (top_lookup gma) (loc_lookup gma) cell_tl (CellT (qtl,qty,q)) in
            let val_lst = to_list (map_suite val_tl ~f:snd) in 

            (* log_msg "calling check_dep_term"; *)
            let* (tlst,topt) = tcm_check_dep_term (to_list es) eo val_lst val_ty in

            let t_suite = from_list tlst in
            let eval_tm = eval (top_lookup gma) (loc_lookup gma) in 
            let val_suite = map_suite t_suite ~f:eval_tm in 
            let val_opt = Option.map topt ~f:eval_tm in 

            tcm_ok ((t_suite,topt),(val_suite,val_opt))

          | _ -> failwith "impossible"

        ) in 

  let (rt,rv) = unzip_nst r in 
  tcm_ok (rt , Adjoin (tv,rv))


and tcm_check_kan tl ty c = 

    let* (tm_tl, tm_ty, val_tl, val_ty) =
      tcm_check_fib tl ty in

    let* c' = tcm_to_cmplx c in 
    
    begin match c' with
      | Base _ -> tcm_fail (`InvalidShape "No kan conditions dim 0")
      | Adjoin (t,n) ->

        let* (tt,tv) = tcm_check_cmplx val_tl val_ty t in

        begin match empty_addrs (head_of tt) with
          | kan_addr :: [] ->

            let* (nt,cv) = tcm_check_extension val_tl val_ty tv n in

            let* _ = tcm_ensure ((List.length (empty_addrs nt)) = 1)
                (`InternalError "top dim not empty in kan description") in

            tcm_ok (tm_tl,tm_ty, Adjoin (tt,nt),
                    val_tl, val_ty, cv, kan_addr)
            
          | _ ->
            let msg = "comp must have exactly one empty boundary position" in 
            tcm_fail (`InvalidShape msg)

        end

    end



(* TODO: Perhaps this should return the fibration to make things more efficient ? *)
and tcm_in_tele (tl : expr tele)
    (k : term tele -> 'a tcm) : 'a tcm =

  match tl with
  | Emp -> k Emp
  | Ext (tl',(id,ty)) ->
    tcm_in_tele tl' (fun tt -> 
        let* ty_tm = tcm_check ty TypV in
        let* ty_val = tcm_eval ty_tm in
        let* gma = tcm_ctx in
        tcm_in_ctx (bind gma id ty_val)
          (k (Ext (tt,(id,ty_tm)))))

and tcm_check_fib tl ty =
  
    let* (tm_tl, tm_ty) =
      tcm_in_tele tl (fun tt ->
          let* tyt = tcm_check ty TypV in
          tcm_ok (tt,tyt)) in 

    let* gma = tcm_ctx in 
    let (val_tl , val_ty) =
      eval_fib (top_lookup gma) (loc_lookup gma) tm_tl tm_ty in 

    tcm_ok (tm_tl, tm_ty, val_tl, val_ty) 

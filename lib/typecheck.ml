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
  | `TypeMismatch of expr * term * term 
  | `NotImplemented of string
  | `InferrenceFailed of expr
  | `ExpectedFunction of expr
  | `InvalidShape of string 
  | `InternalError
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm ->
    
    Fmt.pf ppf "Name not in scope: %s" nm
      
  | `TypeMismatch (e,exp,inf) ->

    Fmt.pf ppf "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
    Fmt.pf ppf "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_term inf;
    Fmt.pf ppf "@[<v>but was expected to have type: @,@, @[%a@]@,@]" pp_term exp;

  | `NotImplemented f ->

    Fmt.pf ppf "Feature not implemented: %s" f
      
  | `InferrenceFailed e ->

    Fmt.pf ppf "Failed to infer the type of: %a" pp_expr e
      
  | `ExpectedFunction e -> 

    Fmt.pf ppf "The expression @,@, @[%a@] @,@," pp_expr e ;
    Fmt.pf ppf "was expected to be a function but isn.t"

  | `InvalidShape msg -> pf ppf "Shape error: %s" msg 

  | `InternalError -> Fmt.pf ppf "Internal Error"


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
        
    let apply mf mx =
      bind mf ~f:(fun f ->
          bind mx ~f:(fun x ->
              return (f x)))
      
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

  | (e, expected) ->
    
    let* gma = tcm_ctx in 
    let* (e',inferred) = tcm_infer e in

    let inferred_nf = quote true gma.lvl inferred in
    let expected_nf = quote true gma.lvl expected in

    if (Poly.(<>) expected_nf inferred_nf)
    then tcm_fail (`TypeMismatch (e,expected_nf,inferred_nf))
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

  | CellE (tl,ty,c) ->

    (* So, you could modify tcm_in_tele to progressively evaluate the
       fibration as you do in eval_fib so that you don't evaluate
       everybody twice ...*)
    
    let* (tm_tl, ty_tm) =
      tcm_in_tele tl (fun tt ->
          let* tyt = tcm_check ty TypV in
          (* let* tyv = tcm_eval tyt in *)
          tcm_ok (tt,tyt)) in 

    let* gma = tcm_ctx in 
    let (val_tl , val_ty) =
      eval_fib (top_lookup gma) (loc_lookup gma)
        tm_tl ty_tm in 
    
    let* c' = tcm_to_cmplx c in 
    let* c'' = tcm_check_cmplx val_tl val_ty c' in 
    
    tcm_ok (CellT (tm_tl,ty_tm,c''), TypV)

  | TypE -> tcm_ok (TypT , TypV)

  | _ -> tcm_fail (`InferrenceFailed e) 

and tcm_to_cmplx c =
  let open IdtConv in 
  try let c' = to_cmplx c in
    let _ = validate_opetope c' in 
    tcm_ok c' 
    with TreeExprError msg -> tcm_fail (`InvalidShape msg)
       | ShapeError msg -> tcm_fail (`InvalidShape msg) 


and tcm_check_dep_term (s : expr list) (tm : expr) (tl : value list) (ty : value) : (term list * term) tcm =
  match (s,tl) with
  | ([],[]) ->
    let* t = tcm_check tm ty in 
    tcm_ok ([],t)
  | (e::es , v::vs) ->
    let* t = tcm_check e v in
    let* tv = tcm_eval t in
    let vs' = List.map vs ~f:(fun v -> appV v tv) in
    let* (ltm, dtm) = tcm_check_dep_term es tm vs' (appV ty tv) in
    tcm_ok (t::ltm,dtm)

  (* TODO: this should be named ... *)
  | _ -> tcm_fail `InternalError


and tcm_check_cmplx (_ : value tele) (_ : value)
    (c : expr dep_term cmplx) : term dep_term cmplx tcm =

  
  match c with
  | Base n -> failwith "not done" 
    (* let* n' = TcmTraverse.traverse_nst n
     *     ~f:(fun (es,eop) -> tcm_check e ty) in 
     * tcm_ok (Base n') *)
  | Adjoin (t,n) -> failwith "not done"
    (* let* t' = tcm_check_cmplx ty t in
     * let* tv = TcmComplexTraverse.traverse_cmplx t'
     *     ~f:(fun tm -> tcm_eval tm) in 
     * let c' = Adjoin (tv,map_nst n ~f:(fun _ -> TypV)) in 
     * let cfs = face_cmplx c' in
     * tcm_fail `InternalError *)

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


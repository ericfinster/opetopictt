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
  | `TypeMismatch of string
  | `NotImplemented of string
  | `InferrenceFailed of string
  | `ExpectedFunction of string
  | `InternalError
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg  
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
  | `InferrenceFailed msg -> Fmt.pf ppf "%s" msg
  | `ExpectedFunction msg -> Fmt.pf ppf "%s" msg
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
    let msg = Fmt.str "The expression %a is not a function." pp_expr e in 
    tcm_fail (`ExpectedFunction msg) 

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
    
    (* let nms = names gma in *)
    (* let inferred_nf_expr = term_to_expr nms inferred_nf in
     * let expected_nf_expr = term_to_expr nms expected_nf in *)

    if (Poly.(<>) expected_nf inferred_nf)
       
    then let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
                                   str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_term inferred_nf;
                                   str "@[<v>but was expected to have type: @,@, @[%a@]@,@]"
                                     pp_term expected_nf ]

      in tcm_fail (`TypeMismatch msg)
        
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
    
  | TypE -> tcm_ok (TypT , TypV)

  (* TODO: inferrence error *)
  | _ -> tcm_fail
           (`InferrenceFailed
              (Fmt.str "Could not infer the type of: %a" pp_expr e))

and tcm_in_tele (tl : expr tele)
    (k : value tele -> term tele -> 'a tcm) : 'a tcm =
  
  match tl with
  | Emp -> k Emp Emp
  | Ext (tl',(id,ty)) ->
    tcm_in_tele tl' (fun vt tt -> 
        let* ty_tm = tcm_check ty TypV in
        let* ty_val = tcm_eval ty_tm in
        let* gma = tcm_ctx in
        tcm_in_ctx (bind gma id ty_val)
          (k (Ext (vt,(id,ty_val)))
             (Ext (tt,(id,ty_tm)))))


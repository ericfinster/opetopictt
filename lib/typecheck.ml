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
open Meta
open Eval
open Unify
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
  | `IcityMismatch of icit * icit
  | `TypeMismatch of string
  | `InvalidShape of string
  | `NotImplemented of string
  | `InternalError
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `IcityMismatch (_, _) -> Fmt.pf ppf "Icity mismatch"
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg  
  | `InvalidShape msg -> Fmt.pf ppf "Invalid shape: %s" msg
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
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

let tcm_in_ctx g m _ = m g 

let tcm_with_binding nm ty m =
  let* gma = tcm_ctx in
  tcm_in_ctx (bind gma nm ty) m 
  
(*****************************************************************************)
(*                          Meta Variable Utilities                          *)
(*****************************************************************************)

let tcm_fresh_meta _ =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  (* pr "next meta set to: %d@," (! next_meta); *)
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  let* gma = tcm_ctx in
  (* 
   * TODO: Check the variable application direction here ....
   *) 
  let rec app_vars i t =
    if (i <= 0) then t
      else app_vars (i-1) (AppT (VarT i, t, Expl)) in
  tcm_ok (app_vars gma.lvl (MetaT m))

let rec tcm_insert' m =
  let* (tm,ty) = m in 
  match force_meta ty with
  | PiV (_,Impl,_,b) ->
    let* m = tcm_fresh_meta () in
    let* mv = tcm_eval m in
    tcm_insert' (tcm_ok (AppT (tm,m,Impl) , b mv))
  | _ -> tcm_ok (tm, ty)
  
let tcm_insert m =
  let* (tm,ty) = m in 
  match tm with
  | LamT (_,Impl,_) -> tcm_ok (tm, ty)
  | _ -> tcm_insert' (tcm_ok (tm, ty))

(*****************************************************************************)
(*                            Typechecking Rules                             *)
(*****************************************************************************)

let rec tcm_check (e : expr) (t : value) : term tcm =

  match (e , force_meta t) with

  | (e , TopV (_,_,tv)) -> tcm_check e tv

  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    let* gma = tcm_ctx in
    tcm_in_ctx (bind gma nm a)
      begin
        let* bdy = tcm_check e (b (varV gma.lvl)) in
        tcm_ok (LamT (nm,i,bdy))
      end

  | (t , PiV (nm,Impl,a,b)) ->
    let* gma = tcm_ctx in
    tcm_in_ctx (bind gma nm a)
      begin
        let* bdy = tcm_check t (b (varV gma.lvl)) in
        tcm_ok (LamT (nm,Impl,bdy))
      end

  | (HoleE , _) -> tcm_fresh_meta ()

  | (e , expected) ->

    let* gma = tcm_ctx in 
    let* (e',inferred) = tcm_insert (tcm_infer e) in 
    try unify OneShot (top_lookup gma) gma.lvl expected inferred ; tcm_ok e'
    with Unify_error msg ->
      pr "Unification error: %s\n" msg;
      (* I guess the unification error will have more information .... *)
      let nms = names gma in
      let inferred_nf = term_to_expr nms (quote false gma.lvl inferred) in
      let expected_nf = term_to_expr nms (quote true gma.lvl expected) in
      let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
                                str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_expr inferred_nf;
                                str "@[<v>but was expected to have type: @,@, @[%a@]@,@]"
                                  pp_expr expected_nf ]

      in tcm_fail (`TypeMismatch msg)
    

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

  | LamE (nm,ict,e) ->
    let* m = tcm_fresh_meta () in
    let* mv = tcm_eval m in
    let* gma = tcm_ctx in 
    let* (e',t) = tcm_insert
        (tcm_in_ctx (bind gma nm mv) (tcm_infer e)) in
    let t_tm = quote false (gma.lvl + 1) t in
    let cl v = eval (top_lookup gma) (ext_loc (loc_lookup gma) v) t_tm in 
    tcm_ok (LamT (nm,ict,e'), PiV (nm,ict,mv,cl))

  | AppE (u,v,ict) ->
    let* (u',ut) = match ict with
      | Impl -> tcm_infer u
      | Expl -> tcm_insert' (tcm_infer u)
    in
  
    let* (a,b) = match force_meta ut with
      | PiV (_,ict',a,b) ->
        if (Poly.(<>) ict ict') then
          tcm_fail (`IcityMismatch (ict,ict'))
        else tcm_ok (a,b)
      | _ ->
        let* gma = tcm_ctx in 
        let* am = tcm_fresh_meta () in 
        let* bm = tcm_fresh_meta () in 
        let* a = tcm_eval am in
        let b _ = eval (top_lookup gma) (loc_lookup gma) bm in
        unify OneShot (top_lookup gma) gma.lvl ut (PiV ("x",ict,a,b));
        tcm_ok (a,b)
    in let* v' = tcm_check v a in
    let* vv = tcm_eval v' in 
    tcm_ok (AppT (u', v', ict) , b vv)

  | PiE (nm,ict,a,b) ->
    let* a' = tcm_check a TypV in
    let* av = tcm_eval a' in
    let* b' = tcm_with_binding nm av
        (tcm_check b TypV) in 

    tcm_ok (PiT (nm,ict,a',b') , TypV)
    
  | TypE -> tcm_ok (TypT , TypV)

  | HoleE ->
    let* m = tcm_fresh_meta () in
    let* mv = tcm_eval m in
    let* t = tcm_fresh_meta () in
    tcm_ok (t, mv)

and tcm_in_tele (tl : expr tele)
    (k : value tele -> term tele -> 'a tcm) : 'a tcm =
  
  match tl with
  | Emp -> k Emp Emp
  | Ext (tl',(id,ict,ty)) ->
    tcm_in_tele tl' (fun vt tt -> 
        let* ty_tm = tcm_check ty TypV in
        let* ty_val = tcm_eval ty_tm in
        let* gma = tcm_ctx in
        tcm_in_ctx (bind gma id ty_val)
          (k (Ext (vt,(id,ict,ty_val)))
             (Ext (tt,(id,ict,ty_tm)))))


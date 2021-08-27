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
           
  (* | VarE nm -> (
   *     try
   *       let (idx,(b,typ)) = assoc_with_idx nm gma.types in
   *       match b with
   *       | Bound -> Ok (VarT idx, typ)
   *       | Defined -> Ok (TopT nm, typ)
   *     with Lookup_error -> Error (`NameNotInScope nm)
   *   ) *)

  (* | LamE (nm,ict,e) ->
   *   let a = eval gma.top gma.loc (fresh_meta ()) in
   *   let* (e', t) = insert gma (infer (bind gma nm a) e) in
   *   let cl = Closure (gma.top,gma.loc,quote false (gma.lvl + 1) t) in
   *   Ok (LamT (nm,ict,e') , PiV (nm,ict,a,cl)) *)

  (* | AppE (u,v,ict) ->
   *   let* (u',ut) = match ict with
   *     | Impl -> infer gma u
   *     | Expl -> insert' gma (infer gma u)
   *   in
   * 
   *   let* (a,b) = match force_meta ut with
   *     | PiV (_,ict',a,b) ->
   *       if (Poly.(<>) ict ict') then
   *         Error (`IcityMismatch (ict,ict'))
   *       else Ok (a,b)
   *     | _ ->
   *       let a = eval gma.top gma.loc (fresh_meta ()) in
   *       let b = Closure (gma.top,gma.loc,fresh_meta ()) in
   *       unify OneShot gma.top gma.lvl ut (PiV ("x",ict,a,b));
   *       Ok (a,b)
   *   in let* v' = check gma v a in
   *   Ok (AppT (u', v', ict) , b $$ eval gma.top gma.loc v') *)

  (* | PiE (nm,ict,a,b) ->
   *   let* a' = check gma a TypV in
   *   let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
   *   Ok (PiT (nm,ict,a',b') , TypV) *)
    
  (* | TypE -> Ok (TypT , TypV) *)

  (* | HoleE ->
   *   let a = eval gma.top gma.loc (fresh_meta ()) in
   *   let t = fresh_meta () in
   *   Ok (t , a) *)

  (* | FrmE (t, c) ->
   *   let* t' = check gma t TypV in
   *   let* c' = check_frame c in 
   *   Ok (FrmT (t', c') , TypV) *)

  (* | CellE (t,c,f) ->
   *   let* t' = check gma t TypV in
   *   let* c' = check_frame c in
   *   let tv = eval gma.top gma.loc t' in 
   *   let* f' = check gma f (FrmV (tv,c')) in 
   *   Ok (CellT (t', c', f') , TypV) *)

  (* | FrmElE _ ->
   * 
   *   Error (`NotImplemented "frame elements") *)

  | _ -> tcm_fail `InternalError


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

(*****************************************************************************)
(*                            Typechecking Rules                             *)
(*****************************************************************************)
                            
(* let rec check gma expr typ =
 *   (\* let typ_tm = quote false gma.lvl typ in
 *    * let typ_expr = term_to_expr (names gma) typ_tm in
 *    * pr "Checking @[%a@] has type @[%a@]@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *\)
 * 
 *   let (let*\) m f = Base.Result.bind m ~f in 
 *   
 *   match (expr, force_meta typ) with
 * 
 *   | (e , TopV (_,_,tv)) ->
 *     check gma e tv
 * 
 *   | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
 *     let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
 *     Ok (LamT (nm,i,bdy))
 * 
 *   | (t , PiV (nm,Impl,a,b)) ->
 *     let* bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
 *     Ok (LamT (nm,Impl,bdy))
 * 
 *   | (HoleE , _) -> (\* pr "fresh meta@,"; *\)
 *     let mv = fresh_meta () in Ok mv
 * 
 *   | (e, expected) ->
 *     
 *     let* (e',inferred) = insert gma (infer gma e) in
 *     try unify OneShot gma.top gma.lvl expected inferred ; Ok e'
 *     with Unify_error msg ->
 *       pr "Unification error: %s\n" msg;
 *       (\* I guess the unification error will have more information .... *\)
 *       let nms = names gma in
 *       let inferred_nf = term_to_expr nms (quote false gma.lvl inferred) in
 *       let expected_nf = term_to_expr nms (quote true gma.lvl expected) in
 *       let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
 *                                 str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_expr inferred_nf;
 *                                 str "@[<v>but was expected to have type: @,@, @[%a@]@,@]"
 *                                   pp_expr expected_nf ]
 * 
 *       in Error (`TypeMismatch msg)
 * 
 * 
 * and infer gma expr =
 *   (\* pr "@[<v>Inferring type of: @[%a@]@,@]"
 *    *   pp_expr_with_impl expr ; *\)
 * 
 *   let (let*\) m f = Base.Result.bind m ~f in 
 *   
 *   match expr with
 * 
 *   | VarE nm -> (
 *       try
 *         let (idx,(b,typ)) = assoc_with_idx nm gma.types in
 *         match b with
 *         | Bound -> Ok (VarT idx, typ)
 *         | Defined -> Ok (TopT nm, typ)
 *       with Lookup_error -> Error (`NameNotInScope nm)
 *     )
 * 
 *   | LamE (nm,ict,e) ->
 *     let a = eval gma.top gma.loc (fresh_meta ()) in
 *     let* (e', t) = insert gma (infer (bind gma nm a) e) in
 *     let cl = Closure (gma.top,gma.loc,quote false (gma.lvl + 1) t) in
 *     Ok (LamT (nm,ict,e') , PiV (nm,ict,a,cl))
 * 
 *   | AppE (u,v,ict) ->
 *     let* (u',ut) = match ict with
 *       | Impl -> infer gma u
 *       | Expl -> insert' gma (infer gma u)
 *     in
 * 
 *     let* (a,b) = match force_meta ut with
 *       | PiV (_,ict',a,b) ->
 *         if (Poly.(<>) ict ict') then
 *           Error (`IcityMismatch (ict,ict'))
 *         else Ok (a,b)
 *       | _ ->
 *         let a = eval gma.top gma.loc (fresh_meta ()) in
 *         let b = Closure (gma.top,gma.loc,fresh_meta ()) in
 *         unify OneShot gma.top gma.lvl ut (PiV ("x",ict,a,b));
 *         Ok (a,b)
 *     in let* v' = check gma v a in
 *     Ok (AppT (u', v', ict) , b $$ eval gma.top gma.loc v')
 * 
 *   | PiE (nm,ict,a,b) ->
 *     let* a' = check gma a TypV in
 *     let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
 *     Ok (PiT (nm,ict,a',b') , TypV)
 *     
 *   | TypE -> Ok (TypT , TypV)
 * 
 *   | HoleE ->
 *     let a = eval gma.top gma.loc (fresh_meta ()) in
 *     let t = fresh_meta () in
 *     Ok (t , a)
 * 
 *   | FrmE (t, c) ->
 *     let* t' = check gma t TypV in
 *     let* c' = check_frame c in 
 *     Ok (FrmT (t', c') , TypV)
 * 
 *   | CellE (t,c,f) ->
 *     let* t' = check gma t TypV in
 *     let* c' = check_frame c in
 *     let tv = eval gma.top gma.loc t' in 
 *     let* f' = check gma f (FrmV (tv,c')) in 
 *     Ok (CellT (t', c', f') , TypV)
 * 
 *   | FrmElE _ ->
 * 
 *     Error (`NotImplemented "frame elements")
 *       
 * and check_frame c =
 * 
 *   let (let*\) m f = Base.Result.bind m ~f in 
 *   
 *     let open IdtConv in 
 *     
 *     let* c' =
 *       begin try
 *           let c' = to_cmplx c in
 *           let _ = validate_frame c' in
 *           Ok c'
 *         with TreeExprError msg -> Error (`InvalidShape msg)
 *            | ShapeError msg -> Error (`InvalidShape msg) 
 * 
 *       end in Ok c' 
 * 
 * and with_tele : 'a . ctx -> expr tele
 *   -> (ctx -> value tele -> term tele -> ('a,typing_error) Result.t)
 *   -> ('a,typing_error) Result.t = fun gma tl m ->
 * 
 *   let (let*\) m f = Base.Result.bind m ~f in 
 * 
 *   match tl with
 *   | Emp -> m gma Emp Emp
 *   | Ext (tl',(id,ict,ty)) ->
 *     with_tele gma tl' (fun g tv tt ->
 *         let* ty_tm = check g ty TypV in
 *         let ty_val = eval g.top g.loc ty_tm in
 *         m (bind g id ty_val)
 *           (Ext (tv,(id,ict,ty_val)))
 *           (Ext (tt,(id,ict,ty_tm)))) *)

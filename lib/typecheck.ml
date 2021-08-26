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

(* open Opetopes.Idt *)
       
(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type bd =
  | Bound
  | Defined

type ctx = {
  top : top_env;
  loc : loc_env;
  lvl : lvl;
  types : (name * (bd * value)) suite;
}

let empty_ctx = {
  top = Emp;
  loc = Emp;
  lvl = 0;
  types = Emp;
}

let empty_loc gma = {
  top = gma.top;
  loc = Emp;
  lvl = 0;
  types = filter gma.types
      (fun (_,(bd,_)) ->
         match bd with
         | Defined -> true
         | Bound -> false)

}

let bind gma nm ty =
  let l = gma.lvl in {
    loc = Ext (gma.loc, varV l);
    top = gma.top;
    lvl = l+1;
    types = Ext (gma.types,(nm,(Bound,ty)));
  }

let define gma nm tm ty = {
  loc = gma.loc;
  top = Ext (gma.top,(nm,tm));
  lvl = gma.lvl;
  types = Ext (gma.types,(nm,(Defined,ty)));
}

let names gma =
  map_suite gma.types ~f:fst

(*****************************************************************************)
(*                                   Debug                                   *)
(*****************************************************************************)

let rec quote_types ufld typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, (Defined,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm,typ_tm)),l)
  | Ext (typs', (nm, (_,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm, typ_tm)),l+1)

let dump_ctx ufld gma =
  let (tl,_) = quote_types ufld gma.types in
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

(*****************************************************************************)
(*                          Meta Variable Utilities                          *)
(*****************************************************************************)
    
let fresh_meta _ =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  (* pr "next meta set to: %d@," (! next_meta); *)
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  InsMetaT m

let rec insert' gma m =
  let* (tm, ty) = m in
  match force_meta ty with
  | PiV (_,Impl,_,b) ->
    let m = fresh_meta () in
    let mv = eval gma.top gma.loc m in
    insert' gma (Ok (AppT (tm,m,Impl) , b $$ mv))
  | _ -> Ok (tm, ty)

let insert gma m =
  let* (tm, ty) = m in
  match tm with
  | LamT (_,Impl,_) -> Ok (tm, ty)
  | _ -> insert' gma (Ok (tm, ty))

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

(* (\*****************************************************************************\)
 * (\*                              Opetopic Typing                              *\)
 * (\*****************************************************************************\)
 * 
 * (\* open Opetopes.Idt
 *  * open Opetopes.Complex *\)
 * 
 * (\* let rec tele_prefixes (tl : 'a tele) (ty : 'a) : ('a tele * 'a) suite =
 *  *     match tl with
 *  *     | Emp -> Ext (Emp, (Emp, ty))
 *  *     | Ext (tl',(_,_,ty')) ->
 *  *       let pfxs = tele_prefixes tl' ty' in
 *  *       let new_pr = (tl , ty) in
 *  *       Ext (pfxs, new_pr)
 *  * 
 *  * module OpetopicUtils (S : Syntax) = struct *\)
 * 
 *   (\* open S *\)
 *   open SyntaxUtil(S)
 * 
 *   (\* let opetopic_tele (tl : s tele) (ty : s) (frm : occ cmplx) : s tele =
 *    * 
 *    *   let _ = faces (numerate frm) in
 *    *   let _ = ty in
 *    * 
 *    *   let tl_args tl = Suite.map_with_idx tl
 *    *       ~f:(fun (_,ict,_) i -> (ict, VarT i)) in 
 *    * 
 *    *   let do_tl op_tl tl ty =
 *    *     let do_face f =
 *    *       let typ =
 *    *         if (is_base f) then
 *    *           let open TermUtil in
 *    *           let args = Suite.map_suite tl
 *    *               ~f:(fun (nm,ict,_) -> (ict, VarT (level_of op_tl nm))) in 
 *    *           app_args (abstract_tele tl ty) args
 *    *         else CellT ((tl,ty,TypT), map_cmplx f ~f:(fun _ -> Full))
 *    *       in f
 *    *     in ()
 *    *   in tl *\)
 * 
 * end *)

(*****************************************************************************)
(*                             Typechecking Rules                            *)
(*****************************************************************************)
                            
let rec check gma expr typ =
  (* let typ_tm = quote false gma.lvl typ in
   * let typ_expr = term_to_expr (names gma) typ_tm in
   * pr "Checking @[%a@] has type @[%a@]@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *)

  match (expr, force_meta typ) with

  | (e , TopV (_,_,tv)) ->
    check gma e tv

  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    Ok (LamT (nm,i,bdy))

  | (t , PiV (nm,Impl,a,b)) ->
    let* bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
    Ok (LamT (nm,Impl,bdy))

  | (HoleE , _) -> (* pr "fresh meta@,"; *)
    let mv = fresh_meta () in Ok mv

  | (e, expected) ->
    
    let* (e',inferred) = insert gma (infer gma e) in
    try unify OneShot gma.top gma.lvl expected inferred ; Ok e'
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

      in Error (`TypeMismatch msg)


and infer gma expr =
  (* pr "@[<v>Inferring type of: @[%a@]@,@]"
   *   pp_expr_with_impl expr ; *)
  match expr with

  | VarE nm -> (
      try
        let (idx,(b,typ)) = assoc_with_idx nm gma.types in
        match b with
        | Bound -> Ok (VarT idx, typ)
        | Defined -> Ok (TopT nm, typ)
      with Lookup_error -> Error (`NameNotInScope nm)
    )

  | LamE (nm,ict,e) ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let* (e', t) = insert gma (infer (bind gma nm a) e) in
    let cl = Closure (gma.top,gma.loc,quote false (gma.lvl + 1) t) in
    Ok (LamT (nm,ict,e') , PiV (nm,ict,a,cl))

  | AppE (u,v,ict) ->
    let* (u',ut) = match ict with
      | Impl -> infer gma u
      | Expl -> insert' gma (infer gma u)
    in

    let* (a,b) = match force_meta ut with
      | PiV (_,ict',a,b) ->
        if (Poly.(<>) ict ict') then
          Error (`IcityMismatch (ict,ict'))
        else Ok (a,b)
      | _ ->
        let a = eval gma.top gma.loc (fresh_meta ()) in
        let b = Closure (gma.top,gma.loc,fresh_meta ()) in
        unify OneShot gma.top gma.lvl ut (PiV ("x",ict,a,b));
        Ok (a,b)
    in let* v' = check gma v a in
    Ok (AppT (u', v', ict) , b $$ eval gma.top gma.loc v')

  | PiE (nm,ict,a,b) ->
    let* a' = check gma a TypV in
    let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
    Ok (PiT (nm,ict,a',b') , TypV)
    
  | TypE -> Ok (TypT , TypV)

  | HoleE ->
    let a = eval gma.top gma.loc (fresh_meta ()) in
    let t = fresh_meta () in
    Ok (t , a)


and with_tele : 'a . ctx -> expr tele
  -> (ctx -> value tele -> term tele -> ('a,typing_error) Result.t)
  -> ('a,typing_error) Result.t = fun gma tl m ->
  match tl with
  | Emp -> m gma Emp Emp
  | Ext (tl',(id,ict,ty)) ->
    with_tele gma tl' (fun g tv tt ->
        let* ty_tm = check g ty TypV in
        let ty_val = eval g.top g.loc ty_tm in
        m (bind g id ty_val)
          (Ext (tv,(id,ict,ty_val)))
          (Ext (tt,(id,ict,ty_tm))))


let rec check_defs gma defs =
  let module E = ExprUtil in
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = E.abstract_tele_with_type tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in
    pr "Checking complete for %s@," id;
    (* let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
     * let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in *)
    (* pr "Type: @[%a@]@," pp_expr ty_nf; *)
    (* pr "Term: @[%a@]@," pp_expr tm_nf; *)
    check_defs (define gma id tm_val ty_val) ds

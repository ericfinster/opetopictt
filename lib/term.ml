(*****************************************************************************)
(*                                                                           *)
(*                              Internal Syntax                              *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Expr
open Suite
open Syntax

open Opetopes.Complex
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type term =

  (* Primitives *)
  | VarT of idx
  | TopT of name
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | CellT of term judgmt * (term suite * term option) cmplx
  | MetaT of mvar
  | InsMetaT of mvar
  | TypT

(*****************************************************************************)
(*                              DeBrujin Lifting                             *)
(*****************************************************************************)

(* let rec db_lift_by l k tm =
 *   let lft = db_lift_by l k in
 *   match tm with
 *   | VarT i ->
 *     if (i >= l) then VarT (k+i) else VarT i
 *   | TopT nm -> TopT nm
 *   | LamT (nm,ict,tm) ->
 *     LamT (nm, ict, db_lift_by (l+1) k tm)
 *   | AppT (u,v,ict) -> AppT (lft u, lft v, ict)
 *   | PiT (nm,ict,a,b) ->
 *     PiT (nm,ict,lft a, db_lift_by (l+1) k b)
 *   | CellT (a,frm) ->
 *     CellT (lft a, map_cmplx frm ~f:lft)
 *   | MetaT m -> MetaT m
 *   | InsMetaT m -> InsMetaT m
 *   | TypT -> TypT
 * 
 * let db_lift l t = db_lift_by l 1 t *)

(*****************************************************************************)
(*                            Terms to Expressions                           *)
(*****************************************************************************)

let rec term_to_expr nms tm =
  let tte = term_to_expr in
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,ict,bdy) ->
    LamE (nm, ict, tte (Ext (nms,nm)) bdy)
  | AppT (u,v,ict) ->
    AppE (tte nms u, tte nms v, ict)
  | PiT (nm,ict,a,b) ->
    PiE (nm, ict, tte nms a, tte (Ext (nms,nm)) b)
  | CellT ((tl,typ),frm) ->
    let (etl, etyp) = fold_accum_cont tl Emp
        (fun (nm,ict,ty) nms ->
           ((nm,ict,term_to_expr nms ty),Ext (nms,nm)))
        (fun tl' nms -> (tl', term_to_expr nms typ)) in 
    let efrm = map_cmplx frm
        ~f:(fun (ts,topt) ->
            (map_suite ts ~f:(tte nms),
             Option.map topt ~f:(tte nms))) in 
    CellE ((etl,etyp), of_cmplx efrm)
  | MetaT _ -> HoleE
  (* Somewhat dubious, since we lose the implicit application ... *)
  | InsMetaT _ -> HoleE
  | TypT -> TypE

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let rec tele_to_pi tl ty =
  match tl with
  | Emp -> ty
  | Ext (tl',(nm,ict,ty_tm)) ->
    tele_to_pi tl' (PiT (nm,ict,ty_tm,ty))

let pi_to_tele ty =
  let rec go tl ty =
    match ty with
    | PiT (nm,ict,a,b) ->
      go (Ext (tl,(nm,ict,a))) b
    | _ -> (tl,ty)
  in go Emp ty

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let is_app_tm tm =
  match tm with
  | AppT (_,_,_) -> true
  | _ -> false

let is_pi_tm tm =
  match tm with
  | PiT (_,_,_,_) -> true
  | _ -> false

let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm pp_term t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,_,Impl) ->
    (* pf ppf "%a {%a}" pp_term u pp_term v *)
    pf ppf "%a" pp_term u
  | AppT (u,v,Expl) ->
    (* Need's a generic lookahead for parens routine ... *)
    let pp_v = if (is_app_tm v) then
        parens pp_term
      else pp_term in
    pf ppf "%a %a" pp_term u pp_v v
  | PiT (nm,Impl,a,p) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_term a pp_term p
  | PiT (nm,Expl,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens pp_term
      else pp_term in
    pf ppf "%a -> %a"
      pp_a a pp_term p
  | PiT (nm,Expl,a,p) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_term a pp_term p
  | CellT _ -> pf ppf "cell term"
  | MetaT _ -> pf ppf "_"
  (* Again, misses some implicit information ... *)
  | InsMetaT _ -> pf ppf "*_*"
  | TypT -> pf ppf "U"

(*****************************************************************************)
(*                               Free Variables                              *)
(*****************************************************************************)

(* let fvs_empty = Set.empty (module Int)
 * let fvs_singleton k = Set.singleton (module Int) k
 * 
 * let rec free_vars k tm =
 *   match tm with
 *   | VarT i when i >= k -> fvs_singleton i
 *   | VarT _ -> fvs_empty
 *   | TopT _ -> fvs_empty
 *   | LamT (_,_,bdy) -> free_vars (k+1) bdy
 *   | AppT (u,v,_) ->
 *     Set.union (free_vars k u) (free_vars k v)
 *   | PiT (_,_,a,b) ->
 *     Set.union (free_vars k a) (free_vars (k+1) b)
 *   | TypT -> fvs_empty
 *   | MetaT _ -> fvs_empty
 *   | InsMetaT _ -> fvs_empty *)

(*****************************************************************************)
(*                         Term Syntax Implmentations                        *)
(*****************************************************************************)

module TermSyntax = struct
  type s = term
  let var k l _ = VarT (lvl_to_idx k l)
  let lam nm ict bdy = LamT (nm,ict,bdy)
  let app u v ict = AppT (u,v,ict)
  let pi nm ict dom cod = PiT (nm,ict,dom,cod)
  let pp_s = pp_term
end

module TermUtil = SyntaxUtil(TermSyntax)

(*****************************************************************************)
(*                                                                           *)
(*                              User Expressions                             *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Syntax
open Suite

open Opetopes.Idt
open IdtConv
open Opetopes.Complex

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type expr =

  (* Variables *)
  | VarE of name

  (* Pi Types *)
  | LamE of name * expr
  | AppE of expr * expr
  | PiE of name * expr * expr

  (* Sigma Types *)
  | PairE of expr * expr
  | FstE of expr
  | SndE of expr
  | SigE of name * expr * expr 

  (* Cell types *) 
  | CellE of expr tele * expr * expr dep_term tr_expr suite
  | CompE of expr tele * expr * expr dep_term tr_expr suite
  | FillE of expr tele * expr * expr dep_term tr_expr suite
  | CompUE of expr tele * expr * expr dep_term tr_expr suite * expr * expr
  | FillUE of expr tele * expr * expr dep_term tr_expr suite * expr * expr

  (* The Universe *) 
  | TypE

(* and dep_term = expr suite * expr option *)


(*****************************************************************************)
(*                          Parsing Tree Expressions                         *)
(*****************************************************************************)

let rec to_cmplx (s : 'a tr_expr suite) : 'a cmplx =
  match s with
  | Emp -> failwith "empty suite in to_cmplx"
  | Ext (Emp,n) -> Base (to_nst n)
  | Ext (s',n) ->  Adjoin (to_cmplx s', to_nst n)

let rec of_cmplx (c : 'a cmplx) : 'a tr_expr suite =
  match c with
  | Base n -> Ext (Emp, of_nst n)
  | Adjoin (frm,n) ->
    Ext (of_cmplx frm, of_nst n)

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)

let rec pp_expr ppf expr =
  let ppe = pp_expr in
  match expr with
  | VarE nm -> string ppf nm
                 
  | LamE (nm,bdy) -> pf ppf "\u{03bb} %s. %a" nm ppe bdy
  | AppE (u, v) ->
    pf ppf "@[%a@]@, @[%a@]" ppe u
      (expr_app_parens v) v
      
  | PiE (nm,a,b) when Poly.(=) nm "" ->
    pf ppf "@[%a@]@, \u{2192} @[%a@]"
      (expr_pi_parens a) a ppe b
  | PiE (nm,dom,cod) ->
    pf ppf "(%s : @[%a@])@, \u{2192} @[%a@]" nm
      ppe dom ppe cod

  | PairE (u,v) ->
    pf ppf "%a , %a" pp_expr u pp_expr v
  | FstE u ->
    pf ppf "fst %a" pp_expr u
  | SndE u ->
    pf ppf "snd %a" pp_expr u
  | SigE (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{d7} %a"
      nm pp_expr a pp_expr b 

  | CellE (tl,ty,c) ->
    pp_expr_cell_desc ppf (tl,ty,c)
  | CompE (tl,ty,c) ->
    pf ppf "comp %a" pp_expr_cell_desc (tl,ty,c)
  | FillE (tl,ty,c) -> 
    pf ppf "fill %a" pp_expr_cell_desc (tl,ty,c)
  | CompUE (tl,ty,k,c,f) ->
    pf ppf "comp-unique %a %a %a"
      pp_expr_cell_desc (tl,ty,k)
      pp_expr c pp_expr f
  | FillUE (tl,ty,k,c,f) -> 
    pf ppf "fill-unique %a %a %a" 
      pp_expr_cell_desc (tl,ty,k)
      pp_expr c pp_expr f

  | TypE -> pf ppf "U"

and pp_expr_cell_desc ppf (tl,ty,c) =
  pf ppf "@[<v>[ @[%a \u{22a2} %a@]@,| %a@,]@]"
    (pp_tele pp_expr) tl
    pp_expr ty
    (pp_suite ~sep:(any "@,| ")
       (pp_tr_expr (pp_dep_term pp_expr))) c 

and expr_app_parens e =
  match e with
  | PiE _ -> parens pp_expr
  | AppE _ -> parens pp_expr
  | LamE _ -> parens pp_expr
  | PairE _ -> parens pp_expr
  | FstE _ -> parens pp_expr
  | SndE _ -> parens pp_expr
  | SigE _ -> parens pp_expr
  | CompE _ -> parens pp_expr
  | FillE _ -> parens pp_expr
  | CompUE _ -> parens pp_expr
  | FillUE _ -> parens pp_expr
  | _ -> pp_expr

and expr_pi_parens e =
  match e with
  | PiE _ -> parens pp_expr
  | _ -> pp_expr
    
(*****************************************************************************)
(*                         Expr Syntax Implmentations                        *)
(*****************************************************************************)

module ExprSyntax = struct
  type s = expr
  let var _ _ nm = VarE nm 
  let app u v = AppE (u,v)
  let lam nm bdy = LamE (nm,bdy)
  let pi nm dom cod = PiE (nm,dom,cod)
  let pp_s = pp_expr
end

module ExprUtil = SyntaxUtil(ExprSyntax)

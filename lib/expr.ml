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

  (* Cell types *) 
  | CellE of expr tele * expr * expr dep_term tr_expr suite
  | CompE of expr tele * expr * expr dep_term tr_expr suite
  | FillE of expr tele * expr * expr dep_term tr_expr suite
  | CellElimE of expr tele * expr * expr dep_term tr_expr suite *
                 name * name * expr * expr 

  (* For cell elim: we have a kan situation.  Then we bind two
     variables of the type of the missing cells.  Then we have a type
     valid in the context with these variables bound to the
     appropriate types.  Then we have a term of this fibration with
     the variables substituted for the two Kan cells. *)

  (* I mean, alternatively, just type the first expression as a Pi
     type into the universe, and then the lambda can take care of
     binding the variables.... *)

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

let is_pi e =
  match e with
  | PiE _ -> true
  | _ -> false
    
let app_parens e =
  match e with
  | PiE _ -> true
  | AppE _ -> true
  | LamE _ -> true
  | _ -> false

let rec pp_expr ppf expr =
  let ppe = pp_expr in
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,bdy) -> pf ppf "\\%s. %a" nm ppe bdy
  | AppE (u, v) ->
    let pp_v = if (app_parens v) then
        parens ppe
      else ppe in
    pf ppf "%a@, %a" ppe u pp_v v
  | PiE (nm,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in
    pf ppf "%a -> %a"
      pp_a a ppe b
  | PiE (nm,dom,cod) ->
    if (is_pi cod) then
      pf ppf "(%s : %a)@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "(%s : %a)@, -> %a" nm
        ppe dom ppe cod

  | CellE _ -> pf ppf "cell" 
  | CompE _ -> pf ppf "comp"
  | FillE _ -> pf ppf "fill"
  | CellElimE _ -> pf ppf "cell-elim" 

  | TypE -> pf ppf "U"

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

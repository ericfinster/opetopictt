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

  (* Pi Types *) 
  | LamT of name * term
  | AppT of term * term 
  | PiT of name * term * term

  (* Cell Types *)
  | CellT of term tele * term * term dep_term cmplx

  | TypT

type 'a cell_desc = 'a dep_term cmplx 

let map_cell_desc (c : 'a cell_desc) ~f:(f : 'a -> 'b) : 'b cell_desc =
  map_cmplx c ~f:(fun (tms,topt) ->
      (map_suite tms ~f:f,
       Option.map topt ~f:f))

(*****************************************************************************)
(*                            Terms to Expressions                           *)
(*****************************************************************************)

let rec term_to_expr nms tm =
  let tte = term_to_expr in
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,bdy) ->
    LamE (nm, tte (Ext (nms,nm)) bdy)
  | AppT (u,v) ->
    AppE (tte nms u, tte nms v)
  | PiT (nm,a,b) ->
    PiE (nm,tte nms a, tte (Ext (nms,nm)) b)
  | CellT (tl,ty,c) ->

    let (etl, ety) = fold_accum_cont tl nms
        (fun (nm,typ) nms ->
           ((nm,term_to_expr nms typ),Ext (nms,nm)))
        (fun etl nms -> (etl, term_to_expr nms ty)) in

    let c' = map_cell_desc c ~f:(tte nms) in 
    
    CellE (etl,ety, of_cmplx c')
    
  | TypT -> TypE

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let rec tele_to_pi tl ty =
  match tl with
  | Emp -> ty
  | Ext (tl',(nm,ty_tm)) ->
    tele_to_pi tl' (PiT (nm,ty_tm,ty))

let pi_to_tele ty =
  let rec go tl ty =
    match ty with
    | PiT (nm,a,b) ->
      go (Ext (tl,(nm,a))) b
    | _ -> (tl,ty)
  in go Emp ty

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm
                 
  | LamT (nm,t) ->
    pf ppf "\u{03bb} %s . %a" nm pp_term t
  | AppT (u,v) ->
    pf ppf "%a %a" pp_term u (term_app_parens v) v
      
  | PiT (nm,a,p) when Poly.(=) nm "" ->
    pf ppf "%a \u{2192} %a"
      (term_pi_parens a) a pp_term p
  | PiT (nm,a,p) ->
    pf ppf "(%s : %a) \u{2192} %a" nm
      pp_term a pp_term p
      
  | CellT (tl,ty,c) ->
    let open Opetopes.Idt.IdtConv in 
    pf ppf "@[<v>[ @[%a \u{22a2} %a@]@,| %a@,]@]"
      (pp_tele pp_term) tl
      pp_term ty
      (pp_suite ~sep:(any "@,| ")
         (pp_tr_expr (pp_dep_term pp_term))) (of_cmplx c) 
                 
  | TypT -> pf ppf "U"

and term_app_parens t =
  match t with
  | PiT _ -> parens pp_term
  | AppT _ -> parens pp_term
  | LamT _ -> parens pp_term
  | _ -> pp_term

and term_pi_parens t =
  match t with
  | PiT _ -> parens pp_term
  | _ -> pp_term
  

(*****************************************************************************)
(*                         Term Syntax Implmentations                        *)
(*****************************************************************************)

module TermSyntax = struct
  type s = term
  let var k l _ = VarT (lvl_to_idx k l)
  let lam nm bdy = LamT (nm,bdy)
  let app u v = AppT (u,v)
  let pi nm dom cod = PiT (nm,dom,cod)
  let pp_s = pp_term
end

module TermUtil = SyntaxUtil(TermSyntax)

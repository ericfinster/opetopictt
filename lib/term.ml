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
  | CompT of term tele * term * term dep_term cmplx
  | FillT of term tele * term * term dep_term cmplx 

  | TypT

(* TODO : this terminology is now superseded by that below *)
(* type 'a cell_desc = 'a dep_term cmplx  *)

let map_cell_desc_cmplx (c : 'a dep_term cmplx)
    ~f:(f : 'a -> 'b) : 'b dep_term cmplx =
  map_cmplx c ~f:(fun (tms,topt) ->
      (map_suite tms ~f:f,
       Option.map topt ~f:f))

(*****************************************************************************)
(*                               Term Equality                               *)
(*****************************************************************************)

let rec term_eq s t =
  match (s,t) with
  | (VarT i , VarT j) -> i = j
  | (TopT m , TopT n) -> String.equal m n
  | (LamT (_,u) , LamT (_,v)) -> term_eq u v
  | (AppT (u,v) , AppT (a,b)) ->
    if (term_eq u a) then
      term_eq v b
    else false
  | (PiT (_,u,v) , PiT (_,a,b)) ->
    if (term_eq u a) then
      term_eq v b
    else false
      
  | (CellT (tla,tya,ca), CellT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
  | (CompT (tla,tya,ca), CellT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
  | (FillT (tla,tya,ca), CellT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
      
  | (TypT , TypT) -> true
  | _ -> false 

and cell_desc_eq (tla,tya,ca) (tlb,tyb,cb) = 
    if (term_eq tya tyb) then
      if (tele_sem_eq term_eq tla tlb) then
        cmplx_eq (dep_term_eq term_eq) ca cb 
      else false
    else false
    
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
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    CellE (tle,tye,ce)
  | CompT (tl,ty,c) ->
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    CompE (tle,tye,ce)
  | FillT (tl,ty,c) ->
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    FillE (tle,tye,ce)
      
  | TypT -> TypE

and cell_desc_to_expr nms tl ty c =
    let (etl, ety) = fold_accum_cont tl nms
        (fun (nm,typ) nms ->
           ((nm,term_to_expr nms typ),Ext (nms,nm)))
        (fun etl nms -> (etl, term_to_expr nms ty)) in

    let c' = map_cell_desc_cmplx c ~f:(term_to_expr nms) in
    
    (etl,ety, of_cmplx c')
  
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
    pp_term_cell_desc ppf (tl,ty,c)
  | CompT (tl,ty,c) ->
    pf ppf "comp %a" pp_term_cell_desc (tl,ty,c)
  | FillT (tl,ty,c) ->
    pf ppf "fill %a" pp_term_cell_desc (tl,ty,c)
                 
  | TypT -> pf ppf "U"

and pp_term_cell_desc ppf (tl,ty,c) =
    let open Opetopes.Idt.IdtConv in 
    pf ppf "@[<v>[ @[%a \u{22a2} %a@]@,| %a@,]@]"
      (pp_tele pp_term) tl
      pp_term ty
      (pp_suite ~sep:(any "@,| ")
         (pp_tr_expr (pp_dep_term pp_term))) (of_cmplx c) 
  

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

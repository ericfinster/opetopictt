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

  (* Variables and Definitions *)
  | VarT of idx
  | TopT of name

  (* Pi Types *) 
  | LamT of name * term
  | AppT of term * term 
  | PiT of name * term * term

  (* Sigma Types *) 
  | PairT of term * term
  | FstT of term
  | SndT of term
  | SigT of name * term * term
            
  (* Cell Types *)
  | CellT of term tele * term * term dep_term cmplx
  | CompT of term tele * term * term dep_term cmplx
  | FillT of term tele * term * term dep_term cmplx 
  | CompUT of term tele * term * term dep_term cmplx * term * term
  | FillUT of term tele * term * term dep_term cmplx * term * term

  (* The Universe *) 
  | TypT

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

  | (PairT (ua,va), PairT (ub,vb)) ->
    if (term_eq ua ub) then
      term_eq va vb
    else false
  | (FstT ua, FstT ub) ->
    term_eq ua ub
  | (SndT ua, SndT ub) ->
    term_eq ua ub
  | (SigT (_,ua,va),SigT (_,ub,vb)) ->
    if (term_eq ua ub) then
      term_eq va vb
    else false

  | (CellT (tla,tya,ca), CellT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
  | (CompT (tla,tya,ca), CompT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
  | (FillT (tla,tya,ca), FillT (tlb,tyb,cb)) ->
    cell_desc_eq (tla,tya,ca) (tlb,tyb,cb)
  | (CompUT (tla,tya,ka,ca,fa), CompUT (tlb,tyb,kb,cb,fb)) ->
    if cell_desc_eq (tla,tya,ka) (tlb,tyb,kb) then
      if (term_eq ca cb) then
        term_eq fa fb
      else false
    else false
  | (FillUT (tla,tya,ka,ca,fa), FillUT (tlb,tyb,kb,cb,fb)) ->
    if cell_desc_eq (tla,tya,ka) (tlb,tyb,kb) then
      if (term_eq ca cb) then
        term_eq fa fb
      else false
    else false


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

(* So: what you can do for naming is have a flag which tags those
   names which may have been generated.  Then, while converting back
   to expressions, you will know which ones you need to generate. *)
      
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
    (* this is a heuristic but not completely safe ... *)
    let nm' = 
      if (String.equal nm "") then
        "x" ^ (Int.to_string (length nms)) 
      else nm in 
    PiE (nm',tte nms a, tte (Ext (nms,nm')) b)

  | PairT (u,v) ->
    PairE (tte nms u, tte nms v)
  | FstT u ->
    FstE (tte nms u)
  | SndT u ->
    SndE (tte nms u)
  | SigT (nm,u,v) ->
    let nm' = 
      if (String.equal nm "") then
        "x" ^ (Int.to_string (length nms)) 
      else nm in 
    SigE (nm',tte nms u, tte (Ext (nms,nm')) v)

  | CellT (tl,ty,c) ->
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    CellE (tle,tye,ce)
  | CompT (tl,ty,c) ->
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    CompE (tle,tye,ce)
  | FillT (tl,ty,c) ->
    let (tle,tye,ce) = cell_desc_to_expr nms tl ty c in 
    FillE (tle,tye,ce)
  | CompUT (tl,ty,k,c,f) ->
    let (tle,tye,ke) = cell_desc_to_expr nms tl ty k in 
    CompUE (tle,tye,ke,tte nms c,tte nms f)
  | FillUT (tl,ty,k,c,f) ->
    let (tle,tye,ke) = cell_desc_to_expr nms tl ty k in 
    FillUE (tle,tye,ke,tte nms c,tte nms f)

  | TypT -> TypE

and cell_desc_to_expr nms tl ty c =
  let (etl, ety) = fold_accum_cont tl nms
      (fun (nm,typ) nms ->
         let nm' = 
           if (String.equal nm "") then
             "x" ^ (Int.to_string (length nms)) 
           else nm in 
         ((nm',term_to_expr nms typ),Ext (nms,nm')))
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

  | PairT (u,v) ->
    pf ppf "%a , %a" pp_term u pp_term v
  | FstT u ->
    pf ppf "fst %a" pp_term u
  | SndT u ->
    pf ppf "snd %a" pp_term u
  | SigT (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{d7} %a"
      nm pp_term a pp_term b 

  | CellT (tl,ty,c) ->
    pp_term_cell_desc ppf (tl,ty,c)
  | CompT (tl,ty,c) ->
    pf ppf "comp %a" pp_term_cell_desc (tl,ty,c)
  | FillT (tl,ty,c) ->
    pf ppf "fill %a" pp_term_cell_desc (tl,ty,c)
  | CompUT (tl,ty,k,c,f) ->
    pf ppf "comp-unique %a %a %a" pp_term_cell_desc (tl,ty,k)
      pp_term c pp_term f
  | FillUT (tl,ty,k,c,f) ->
    pf ppf "fill-unique %a %a %a" pp_term_cell_desc (tl,ty,k)
      pp_term c pp_term f

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
  | PairT _ -> parens pp_term
  | FstT _ -> parens pp_term
  | SndT _ -> parens pp_term
  | SigT _ -> parens pp_term
  | CompT _ -> parens pp_term
  | FillT _ -> parens pp_term
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

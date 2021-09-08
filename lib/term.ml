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
  | CellT of (name * term * term cmplx) option * term * term option cmplx
  | CompT of (name * term * term cmplx) option * term * term option cmplx
  | FillT of (name * term * term cmplx) option * term * term option cmplx

  (* The Unit Type *)
  | UnitT 
  | TtT

  (* The Universe *) 
  | TypT

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

  | (CellT (a,b,bc) , CellT (u,v,vc)) ->
    cell_desc_eq (a,b,bc) (u,v,vc)
  | (CompT (a,b,bc) , CompT (u,v,vc)) ->
    cell_desc_eq (a,b,bc) (u,v,vc)
  | (FillT (a,b,bc) , FillT (u,v,vc)) ->
    cell_desc_eq (a,b,bc) (u,v,vc)
      
  | (TypT , TypT) -> true
  | _ -> false 

and cell_desc_eq (a,b,bc) (u,v,vc) =
  let base_eq (_,a,ac) (_,b,bc) =
    if (term_eq a b) then
      cmplx_eq term_eq ac bc
    else false
  in if (Option.equal base_eq a u) then
    if (term_eq b v) then
      cmplx_eq (Option.equal term_eq) bc vc 
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
    SigE (nm,tte nms u, tte (Ext (nms,nm)) v)

  | CellT (a,b,bc) ->
    let (ea,eb,eab) = cell_desc_to_expr nms a b bc in 
    CellE (ea,eb,eab)
  (* | CompT (nm,ta,tb,ca,cb) ->
   *   let (ea,eb,eab) = cell_desc_to_expr nms nm ta tb ca cb in 
   *   CompE (nm,ea,eb,eab)
   * | FillT (nm,ta,tb,ca,cb) ->
   *   let (ea,eb,eab) = cell_desc_to_expr nms nm ta tb ca cb in 
   *   FillE (nm,ea,eb,eab) *)

  | UnitT -> UnitE
  | TtT -> TtE 

  | TypT -> TypE

and cell_desc_to_expr nms a b bc =
  match a with
  | None ->
    let eb = term_to_expr nms b in
    let eab = map_cmplx bc
        ~f:(fun topt -> (None,Option.map topt ~f:(term_to_expr nms))) in
    (None,eb,of_cmplx eab)
  | Some _ ->
    

    failwith ""
  
  (* let ea = term_to_expr nms ta in
   * let eb = term_to_expr (Ext (nms,nm)) tb in
   * let eca = map_cmplx ca ~f:(term_to_expr nms) in
   * let ecb = map_cmplx cb ~f:(fun o -> Option.map o ~f:(term_to_expr nms)) in
   * let eab = match_cmplx eca ecb ~f:(fun a b -> (a,b)) in 
   * (ea,eb,of_cmplx eab) *)
  
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

  | CellT (nm,a,b,ca,cb) ->
    pp_term_cell_desc ppf (nm,a,b,ca,cb)
  | CompT (nm,a,b,ca,cb) ->
    pf ppf "comp %a" pp_term_cell_desc (nm,a,b,ca,cb)
  | FillT (nm,a,b,ca,cb) ->
    pf ppf "fill %a" pp_term_cell_desc (nm,a,b,ca,cb)

  | UnitT -> pf ppf "\u{25cf}"
  | TtT -> pf ppf "\u{2219}"

  | TypT -> pf ppf "U"

and pp_term_cell_desc ppf (nm,a,b,ca,cb) =
  let open Opetopes.Idt.IdtConv in
  let cab = of_cmplx (match_cmplx ca cb ~f:(fun a b -> (a,b))) in 
    pf ppf "@[<v>[ @[(%s : %a) \u{22a2} %a@]@,| %a@,]@]"
      nm pp_term a pp_term b
    (pp_suite ~sep:(any "@,| ")
       (pp_tr_expr (pair ~sep:(any "\u{22a2}")
                      pp_term (Fmt.option ~none:(any "\u{2205}") pp_term)))) cab
  

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

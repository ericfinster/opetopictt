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

  (* Opetopic Reflexivity *)
  | ReflT of term * string cmplx 

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

  | (ReflT (a,pi), ReflT (b,rho)) ->
    if (term_eq a b) then
      (* ignore namings .. *) 
      cmplx_eq (fun _ _ -> true) pi rho
    else false

  | (TypT , TypT) -> true
  | _ -> false 

    
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

  | ReflT (a,pi) ->
    ReflE (tte nms a, of_cmplx pi)

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

  | PairT (u,v) ->
    pf ppf "%a , %a" pp_term u pp_term v
  | FstT u ->
    pf ppf "fst %a" pp_term u
  | SndT u ->
    pf ppf "snd %a" pp_term u
  | SigT (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{d7} %a"
      nm pp_term a pp_term b 

  | ReflT (a,pi) ->
    let open Opetopes.Idt.IdtConv in 
    pf ppf "[ @[%a] @ @[ %a ] ]"
      pp_term a (pp_suite ~sep:(any "@,| ")
       (pp_tr_expr Fmt.string)) (of_cmplx pi) 

  | TypT -> pf ppf "U"

and term_app_parens t =
  match t with
  | PiT _ -> parens pp_term
  | AppT _ -> parens pp_term
  | LamT _ -> parens pp_term
  | PairT _ -> parens pp_term
  | FstT _ -> parens pp_term
  | SndT _ -> parens pp_term
  | SigT _ -> parens pp_term
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

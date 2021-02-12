(*****************************************************************************)
(*                                   Syntax                                  *)
(*****************************************************************************)

open Base
open Suite


(*****************************************************************************)
(*                                 Raw Syntax                                *)
(*****************************************************************************)

type name = string
  
type expr =
  | VarE of name
  | LamE of name * expr
  | AppE of expr * expr
  | PiE of name * expr * expr
  | TypE
  | HoleE

(*****************************************************************************)
(*                              Internal Syntax                              *)
(*****************************************************************************)

type idx = int
type mvar = int
  
type term =
  | VarT of idx
  | LamT of name * term
  | AppT of term * term
  | PiT of name * term * term
  | TypT
  | MetaT of mvar

(*****************************************************************************)
(*                                   Values                                  *)
(*****************************************************************************)

type lvl = int

type value =
  | FlexV of mvar * spine
  | RigidV of lvl * spine
  | LamV of name * closure
  | PiV of name * value * closure 
  | TypV 

and env = value suite
and spine = value suite

and closure =
  | Closure of env * term

(*****************************************************************************)
(*                            Metavarible Context                            *)
(*****************************************************************************)

type meta_entry =
  | Solved of value
  | Unsolved

type intmap = (mvar,meta_entry,Int.comparator_witness) Map.t

let metacontext : intmap ref =
  ref (Map.empty (module Int))

exception Meta_error of string
    
let lookup_meta m =
  let mctx = ! metacontext in
  match Map.find mctx m with
  | Some mentry -> mentry
  | None -> raise (Meta_error "unrecognized metavariable")

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

let rec eval rho tm =
  match tm with
  | VarT i -> nth i rho
  | LamT (nm,u) -> LamV (nm, Closure (rho,u))
  | AppT (u,v) -> appV (eval rho u) (eval rho v)
  | PiT (nm,u,v) -> PiV (nm, eval rho u, Closure (rho,v))
  | TypT -> TypV
  | MetaT m -> metaV m 

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, Emp)
  | Solved v -> v 

and ($$) c v =
  match c with
  | Closure (rho,tm) -> eval (Ext (rho,v)) tm 

and appV t u =
  match t with
  | FlexV (m,sp) -> FlexV (m,Ext(sp,u))
  | RigidV (i,sp) -> RigidV (i,Ext(sp,u))
  | LamV (_,cl) -> cl $$ u 
  | _ -> raise (Eval_error "malformed app")

let rec appSpV v sp =
  match sp with
  | Emp -> v
  | Ext (sp',u) -> appV (appSpV v sp') u

let rec mforce v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> mforce (appSpV v sp))
  | _ -> v
       

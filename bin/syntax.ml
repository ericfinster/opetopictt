(*****************************************************************************)
(*                                   Syntax                                  *)
(*****************************************************************************)

open Fmt
    
open Base
open Suite

(*****************************************************************************)
(*                                 Raw Syntax                                *)
(*****************************************************************************)

type icit =
  | Impl
  | Expl

type name = string
  
type expr =
  | VarE of name
  | LamE of name * icit * expr
  | AppE of expr * expr * icit
  | PiE of name * icit * expr * expr
  | TypE
  | HoleE

type tele = (name * icit * expr) suite
    
type defn =
  | Def of name * tele * expr * expr

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)
           
let is_app e =
  match e with
  | AppE (_, _, _) -> true
  | _ -> false

let is_pi e =
  match e with
  | PiE (_,_,_,_) -> true
  | _ -> false
    
let rec pp_expr ppf expr =
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,Impl,bdy) -> pf ppf "\\{%s}. %a" nm pp_expr bdy
  | LamE (nm,Expl,bdy) -> pf ppf "\\%s. %a" nm pp_expr bdy
  | AppE (u, v, Impl) ->
    pf ppf "%a {%a}" pp_expr u pp_expr v
  | AppE (u, v, Expl) ->
    let pp_v = if (is_app v) then
        parens pp_expr
      else pp_expr in 
    pf ppf "%a %a" pp_expr u pp_v v
  | PiE (nm,Impl,dom,cod) ->
    pf ppf "{%s : %a} -> %a" nm
      pp_expr dom pp_expr cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens pp_expr
      else pp_expr in 
    pf ppf "%a -> %a" 
      pp_a a pp_expr b
  | PiE (nm,Expl,dom,cod) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_expr dom pp_expr cod
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"
  
(*****************************************************************************)
(*                              Internal Syntax                              *)
(*****************************************************************************)

type idx = int
type mvar = int

type bd =
  | Bound
  | Defined

type term =
  | VarT of idx
  | LamT of name * icit * term
  | AppT of term * term * icit
  | PiT of name * icit * term * term
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar * bd suite

(*****************************************************************************)
(*                      Pretty printing internal syntax                      *)
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
  | LamT (nm,Impl,t) ->
    pf ppf "\\{%s}. %a" nm pp_term t
  | LamT (nm,Expl,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,v,Impl) ->
    pf ppf "%a {%a}" pp_term u pp_term v
  | AppT (u,v,Expl) ->
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
  | TypT -> pf ppf "U"
  | MetaT _ -> pf ppf "_"
  | InsMetaT _ -> pf ppf "_"

let pp_bd ppf b =
  match b with
  | Bound -> pf ppf "bnd"
  | Defined -> pf ppf "dfd"
                 
(*****************************************************************************)
(*                                   Values                                  *)
(*****************************************************************************)

type lvl = int

type value =
  | FlexV of mvar * spine
  | RigidV of lvl * spine
  | LamV of name * icit * closure
  | PiV of name * icit * value * closure 
  | TypV 

and env = value suite
and spine = (value * icit) suite

and closure =
  | Closure of env * term

(* let rec pp_value ppf v =
 *   match v with
 *   | FlexV (i,sp) -> pf ppf "?%d%a" i (pp_suite pp_value) sp
 *   | RigidV (l,sp) -> pf ppf "%d%a" l (pp_suite pp_value) sp
 *   | LamV (nm,_) -> pf ppf "\\%s.<>" nm
 *   | PiV (nm,v,_) -> pf ppf "(%s : %a) -> <>" nm pp_value v
 *   | TypV -> pf ppf "U" *)

(*****************************************************************************)
(*                           Metavariable Context                            *)
(*****************************************************************************)

type meta_entry =
  | Solved of value
  | Unsolved

type metamap = (mvar,meta_entry,Int.comparator_witness) Map.t

let next_meta : int ref = ref 0
    
let metacontext : metamap ref =
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
  | VarT i -> db_get i rho
  | LamT (nm,ict,u) -> LamV (nm, ict, Closure (rho,u))
  | AppT (u,v,ict) -> appV (eval rho u) (eval rho v) ict
  | PiT (nm,ict,u,v) -> PiV (nm, ict, eval rho u, Closure (rho,v))
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT (m,bds) -> appBdsV rho (metaV m) bds

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, Emp)
  | Solved v -> v 

and ($$) c v =
  match c with
  | Closure (rho,tm) -> eval (Ext (rho,v)) tm 

and appV t u ict =
  match t with
  | FlexV (m,sp) -> FlexV (m,Ext(sp,(u,ict)))
  | RigidV (i,sp) -> RigidV (i,Ext(sp,(u,ict)))
  | LamV (_,_,cl) -> cl $$ u 
  | _ -> raise (Eval_error "malformed app")

and appBdsV rho v bds =
  match (rho , bds) with
  | (Emp,Emp) -> v
  | (Ext (rho',u),Ext (bds',Bound)) -> appV (appBdsV rho' v bds') u Expl
  | (Ext (rho',_),Ext (bds',Defined)) -> appBdsV rho' v bds'
  | _ -> raise (Eval_error "malfomed bounding mask")

let rec appSpV v sp =
  match sp with
  | Emp -> v
  | Ext (sp',(u,ict)) -> appV (appSpV v sp') u ict
    
let rec mforce v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> mforce (appSpV v sp))
  | _ -> v
       
(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let varV k = RigidV (k,Emp)
    
let rec quote k v =
  match v with
  | FlexV (m,sp) -> quote_sp k (MetaT m) sp
  | RigidV (l,sp) -> quote_sp k (VarT (lvl_to_idx k l)) sp
  | LamV (nm,ict,cl) -> LamT (nm, ict, quote (k+1) (cl $$ varV k))
  | PiV (nm,ict,u,cl) -> PiT (nm, ict, quote k u, quote (k+1) (cl $$ varV k))
  | TypV -> TypT

and quote_sp k t sp =
  match sp with
  | Emp -> t
  | Ext (sp',(u,ict)) ->
    AppT (quote_sp k t sp',quote k u,ict)

let nf rho tm =
  quote (length rho) (eval rho tm) 

(*****************************************************************************)
(*                                Unification                                *)
(*****************************************************************************)

let fresh_meta bds =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  InsMetaT (m,bds)

type perm = (lvl,lvl,Int.comparator_witness) Map.t
                       
type partial_ren = {
  dom : lvl;
  cod : lvl;
  ren : perm;
}

let lift pren = {
  dom = pren.dom + 1;
  cod = pren.cod + 1;
  ren = Map.set pren.ren ~key:pren.cod ~data:pren.dom; 
}

exception Unify_error of string
    
let invert cod sp =
  let rec go = function
    | Emp -> (0, Map.empty (module Int))
    | Ext (sp',(u,_)) ->
      let (dom, ren) = go sp' in
      (match mforce u with
       | RigidV (l,Emp) ->
         (match Map.add ren ~key:l ~data:dom  with
          | `Ok ren' -> (dom + 1,ren')
          | `Duplicate -> raise (Unify_error "non-linear pattern"))
       | _ -> raise (Unify_error "meta-var applied to non-bound-variable")) in 
  let (dom,ren) = go sp in
  { dom = dom ; cod = cod ; ren = ren }

let rename m pren v =

  let rec goSp pr v = function
    | Emp -> v
    | Ext (sp,(u,ict)) -> AppT (goSp pr v sp, go pr u, ict)

  and go pr v = match mforce v with
    | FlexV (m',sp) ->
      if (m <> m') then
        goSp pr (MetaT m') sp
      else raise (Unify_error "failed occurs check")
    | RigidV (i,sp) ->
      (match Map.find pr.ren i with
       | Some l -> goSp pr (VarT (lvl_to_idx pr.dom l)) sp 
       | None -> raise (Unify_error "escaped variable"))
    | LamV (nm,ict,a) -> LamT (nm, ict, go (lift pr) (a $$ varV pr.cod))
    | PiV (nm,ict,a,b) -> PiT (nm, ict, go pr a, go (lift pr) (b $$ varV pr.cod))
    | TypV -> TypT

  in go pren v

let lams icts t =
  let rec go k icts t =
    match icts with
    | Emp -> t
    | Ext (is,i) -> 
      let nm = Printf.sprintf "x%d" (k+1) in
      LamT (nm, i, go (k+1) is t) 
  in go 0 icts t

let solve k m sp v =
  let pr = invert k sp in
  let rhs = rename m pr v in
  let sol = eval Emp (lams (rev (map snd sp)) rhs) in
  let mctx = ! metacontext in
  metacontext := Map.update mctx m ~f:(fun _ -> Solved sol)

let rec unify l t u =
  match (mforce t , mforce u) with
  | (LamV (_,_,a) , LamV (_,_,a')) -> unify (l+1) (a $$ varV l) (a' $$ varV l)
  | (t' , LamV(_,i,a')) -> unify (l+1) (appV t' (varV l) i) (a' $$ varV l)
  | (LamV (_,i,a) , t') -> unify (l+1) (a $$ varV l) (appV t' (varV l) i)
  | (TypV , TypV) -> ()
  | (PiV (_,ict,a,b) , PiV (_,ict',a',b')) when Poly.(=) ict ict' ->
    unify l a a' ;
    unify (l+1) (b $$ varV l) (b' $$ varV l)
  | (PiV (_,_,_,_) , PiV (_,_,_,_)) ->
    raise (Unify_error "wrong icity")
  | (RigidV (i,sp) , RigidV (i',sp')) when i = i' -> unifySp l sp sp'
  | (RigidV (i,_) , RigidV (i',_)) ->
    raise (Unify_error (str "Rigid mismatch: %d =/= %d" (lvl_to_idx l i) (lvl_to_idx l i')))
  | (FlexV (m,sp) , FlexV (m',sp')) when m = m' -> unifySp l sp sp' 
  | (FlexV (m,_) , FlexV (m',_)) -> 
    raise (Unify_error (str "Flex mismatch: %d =/= %d" m m'))
  | (t' , FlexV (m,sp)) -> solve l m sp t'
  | (FlexV (m,sp) , t') -> solve l m sp t'
  | _ -> raise (Unify_error "could not unify")

and unifySp l sp sp' =
  match (sp,sp') with
  | (Emp,Emp) -> ()
  | (Ext (s,(u,_)),Ext(s',(u',_))) ->
    unifySp l s s';
    unify l u u'
  | _ -> raise (Unify_error "spine mismatch")

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type ctx = {
  rho : env;
  lvl : lvl;
  types : (name * value) suite;
  bds : bd suite;
}
    
(* let pp_ctx =
 *   record [
 *     field "rho"   (fun g -> g.rho)   (pp_suite pp_value) ;
 *     field "lvl"   (fun g -> g.lvl)   (int) ;
 *     field "types" (fun g -> g.types) (pp_suite (pair string pp_value));
 *     field "bds"   (fun g -> g.bds)   (pp_suite pp_bd)
 *   ] *)

let rec quote_tele typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, typ)) ->
    let (res_typs, l) = quote_tele typs' in
    let typ_tm = quote l typ in
    (Ext (res_typs,(nm, typ_tm)),l+1)
    
let dump_ctx gma =
  let (tl,_) = quote_tele gma.types in 
  (* let tl = map (fun (nm,typ) -> (nm , quote gma.lvl typ)) gma.types in  *)
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

let empty_ctx = {
  rho = Emp;
  lvl = 0;
  types = Emp;
  bds = Emp;
}
 
let bind gma nm ty =
  let l = gma.lvl in 
  { rho = Ext (gma.rho, varV l);
    lvl = l+1;
    types = Ext (gma.types,(nm,ty));
    bds = Ext (gma.bds,Bound) }

let define gma nm tm ty =
  { rho = Ext (gma.rho,tm);
    lvl = gma.lvl+1;
    types = Ext (gma.types,(nm,ty));
    bds = Ext (gma.bds,Defined) }

let rec insert' gma (tm,ty) =
  match mforce ty with
  | PiV (_,Impl,_,b) ->
    let m = fresh_meta (gma.bds) in
    let mv = eval gma.rho m in
    insert' gma (AppT (tm,m,Impl) , b $$ mv)
  | _ -> (tm, ty)

let insert gma (tm, ty) =
  match tm with
  | LamT (_,Impl,_) -> (tm, ty)
  | _ -> insert' gma (tm, ty)

let rec term_to_expr nms tm = 
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | LamT (nm,ict,bdy) ->
    LamE (nm, ict, term_to_expr (Ext (nms,nm)) bdy)
  | AppT (u,v,ict) ->
    AppE (term_to_expr nms u, term_to_expr nms v, ict)
  | PiT (nm,ict,a,b) ->
    PiE (nm, ict, term_to_expr nms a, term_to_expr (Ext (nms,nm)) b)
  | TypT -> TypE
  | MetaT _ -> HoleE
  | InsMetaT (_, _) -> HoleE

exception Typing_error of string

let rec check gma expr typ =
  (* let typ_tm = quote gma.lvl typ in 
   * pr "@,Checking %a has type %a@," pp_expr expr pp_term typ_tm ;
   * dump_ctx gma; *)
  match (expr, mforce typ) with
  
  | (LamE (nm,i,e) , PiV (_,i',a,b)) when Poly.(=) i i' ->
    let bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    LamT (nm,i,bdy)


  | (t , PiV (nm,Impl,a,b)) ->
    let bdy = check (bind gma nm a) t (b $$ varV gma.lvl) in
    LamT (nm,Impl,bdy)

  | (HoleE , _) -> fresh_meta (gma.bds)

  | (e, expected) ->
    let (e',inferred) = insert gma (infer gma e) in
    unify (gma.lvl) expected inferred ; e'

and infer gma expr =
  (* pr "@,Inferring type of %a@," pp_expr expr ;
   * dump_ctx gma;  *)
  match expr with

  | VarE nm -> (
      try let (idx,typ) = assoc_with_idx nm gma.types in
        (* pr "Inferred variable of index %d to have type: %a@," idx pp_term (quote gma.lvl typ) ; *)
        (VarT idx, typ)
      with Lookup_error -> raise (Typing_error (str "Unknown identifier %s" nm))
    )

  | LamE (nm,ict,e) ->
    let a = eval (gma.rho) (fresh_meta gma.bds) in
    let (e', t) = insert gma (infer (bind gma nm a) e) in
    (LamT (nm,ict,e') , PiV (nm,ict,a,Closure (gma.rho,quote (gma.lvl + 1) t)))

  | AppE (u,v,ict) ->
    let (u',ut) = match ict with
      | Impl -> infer gma u
      | Expl -> insert' gma (infer gma u)
    in
    
    let (a,b) = match mforce ut with
      | PiV (_,ict',a,b) ->
        if (Poly.(<>) ict ict') then
          raise (Typing_error "Implicit mismatch")
        else (a,b)
      | _ ->
        let a = eval (gma.rho) (fresh_meta gma.bds) in
        let b = Closure (gma.rho , fresh_meta (bind gma "x" a).bds) in
        unify gma.lvl ut (PiV ("x",ict,a,b)); 
        (a,b)
    in let v' = check gma v a in 
    (AppT (u', v', ict) , b $$ eval gma.rho v')

  | PiE (nm,ict,a,b) ->
    let a' = check gma a TypV in
    let b' = check (bind gma nm (eval gma.rho a')) b TypV in
    (PiT (nm,ict,a',b') , TypV)

  | TypE -> (TypT , TypV)

  | HoleE ->
    let a = eval (gma.rho) (fresh_meta gma.bds) in
    let t = fresh_meta gma.bds in
    (t , a)

let rec with_tele gma tl m =
  match tl with
  | Emp -> m gma
  | Ext (tl',(id,ty)) ->
    with_tele gma tl' (fun gma' ->
        let ty' = check gma' ty TypV in
        m (bind gma' id (eval gma'.rho ty')))

let rec abstract_tele tl ty tm =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',(nm,ict,expr)) ->
    abstract_tele tl' (PiE (nm,ict,expr,ty)) (LamE (nm,ict,tm))
    
let rec check_defs gma defs =
  match defs with
  | [] -> gma
  | (Def (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele tl ty tm in
    let ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.rho ty_tm in
    let tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.rho tm_tm in 
    pr "Checking complete for %s@," id;
    let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val) in
    let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val) in
    pr "Type: %a@," pp_expr ty_nf;
    pr "Term: %a@," pp_expr tm_nf;
    check_defs (define gma id tm_val ty_val) ds

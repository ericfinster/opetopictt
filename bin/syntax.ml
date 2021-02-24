(*****************************************************************************)
(*                                   Syntax                                  *)
(*****************************************************************************)

open Fmt
    
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

type tele = (name * expr) suite
    
type defn =
  | Def of name * tele * expr * expr

let is_app e =
  match e with
  | AppE (_, _) -> true
  | _ -> false

let rec pp_expr ppf expr =
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,bdy) -> pf ppf "\\%s. %a" nm pp_expr bdy
  | AppE (u, v) ->
    let pp_v = if (is_app v) then
        parens pp_expr
      else pp_expr in 
    pf ppf "%a %a" pp_expr u pp_v v
  | PiE (nm,dom,cod) ->
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
  | LamT of name * term
  | AppT of term * term
  | PiT of name * term * term
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar * bd suite

(*****************************************************************************)
(*                      Pretty printing internal syntax                      *)
(*****************************************************************************)

let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | LamT (nm,t) ->
    pf ppf "\\%s.%a" nm pp_term t
  | AppT (u,AppT (v,w)) ->
    pf ppf "%a (%a)" pp_term u  pp_term (AppT (v,w))
  | AppT (u,v) ->
    pf ppf "%a %a" pp_term u pp_term v
  | PiT (nm,a,p) ->
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
  | LamV of name * closure
  | PiV of name * value * closure 
  | TypV 

and env = value suite
and spine = value suite

and closure =
  | Closure of env * term

let rec pp_value ppf v =
  match v with
  | FlexV (i,sp) -> pf ppf "?%d%a" i (pp_suite pp_value) sp
  | RigidV (l,sp) -> pf ppf "%d%a" l (pp_suite pp_value) sp
  | LamV (nm,_) -> pf ppf "\\%s.?" nm
  | PiV (nm,v,_) -> pf ppf "(%s : %a) -> ?" nm pp_value v
  | TypV -> pf ppf "U"

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
  | LamT (nm,u) -> LamV (nm, Closure (rho,u))
  | AppT (u,v) -> appV (eval rho u) (eval rho v)
  | PiT (nm,u,v) -> PiV (nm, eval rho u, Closure (rho,v))
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

and appV t u =
  match t with
  | FlexV (m,sp) -> FlexV (m,Ext(sp,u))
  | RigidV (i,sp) -> RigidV (i,Ext(sp,u))
  | LamV (_,cl) -> cl $$ u 
  | _ -> raise (Eval_error "malformed app")

and appBdsV rho v bds =
  match (rho , bds) with
  | (Emp,Emp) -> v
  | (Ext (rho',u),Ext (bds',Bound)) -> appV (appBdsV rho' v bds') u 
  | (Ext (rho',_),Ext (bds',Defined)) -> appBdsV rho' v bds'
  | _ -> raise (Eval_error "malfomed bounding mask")

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
       
(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let varV k = RigidV (k,Emp)
    
let rec quote k v =
  match v with
  | FlexV (m,sp) -> quote_sp k (MetaT m) sp
  | RigidV (l,sp) -> quote_sp k (VarT (lvl_to_idx k l)) sp
  | LamV (nm,cl) -> LamT (nm, quote (k+1) (cl $$ varV k))
  | PiV (nm,u,cl) -> PiT (nm, quote k u, quote (k+1) (cl $$ varV k))
  | TypV -> TypT

and quote_sp k t sp =
  match sp with
  | Emp -> t
  | Ext (sp',u) ->
    AppT (quote_sp k t sp',quote k u)

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
    | Ext (sp',u) ->
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
    | Ext (sp,u) -> AppT (goSp pr v sp, go pr u)

  and go pr v = match mforce v with
    | FlexV (m',sp) ->
      if (m <> m') then
        goSp pr (MetaT m') sp
      else raise (Unify_error "failed occurs check")
    | RigidV (i,sp) ->
      (match Map.find pr.ren i with
       | Some l -> goSp pr (VarT (lvl_to_idx pr.dom l)) sp 
       | None -> raise (Unify_error "escaped variable"))
    | LamV (nm,a) -> LamT (nm, go (lift pr) (a $$ varV pr.cod))
    | PiV (nm,a,b) -> PiT (nm, go pr a, go (lift pr) (b $$ varV pr.cod))
    | TypV -> TypT

  in go pren v

let lams l t =
  let rec go k t =
    if (k = l) then t else
      let nm = Printf.sprintf "x%d" (k+1) in
      LamT (nm, go (k+1) t)
  in go 0 t

let solve k m sp v =
  let pr = invert k sp in
  let v' = rename m pr v in
  let sol = eval Emp (lams pr.dom v') in
  let mctx = ! metacontext in
  metacontext := Map.update mctx m ~f:(fun _ -> Solved sol)

let rec unify l t u =
  match (mforce t , mforce u) with
  | (LamV (_,a) , LamV (_,a')) -> unify (l+1) (a $$ varV l) (a' $$ varV l)
  | (t' , LamV(_,a')) -> unify (l+1) (appV t' (varV l)) (a' $$ varV l)
  | (LamV (_,a) , t') -> unify (l+1) (a $$ varV l) (appV t' (varV l))
  | (TypV , TypV) -> ()
  | (PiV (_,a,b) , PiV (_,a',b')) ->
    unify l a a';
    unify (l+1) (b $$ varV l) (b' $$ varV l)
  | (RigidV (i,sp) , RigidV (i',sp')) ->
    if (i = i') then unifySp l sp sp' else
      raise (Unify_error (str "Rigid mismatch: %d =/= %d" i i'))
  | (FlexV (m,sp) , FlexV (m',sp')) ->
    if (m = m') then unifySp l sp sp' else
      raise (Unify_error (str "Flex mismatch: %d =/= %d" m m'))
  | (t' , FlexV (m,sp)) -> solve l m sp t'
  | (FlexV (m,sp) , t') -> solve l m sp t'
  | _ -> raise (Unify_error "could not unify")

and unifySp l sp sp' =
  match (sp,sp') with
  | (Emp,Emp) -> ()
  | (Ext (s,u),Ext(s',u')) ->
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
    
let pp_ctx =
  record [
    field "rho"   (fun g -> g.rho)   (pp_suite pp_value) ;
    field "lvl"   (fun g -> g.lvl)   (int) ;
    field "types" (fun g -> g.types) (pp_suite (pair string pp_value));
    field "bds"   (fun g -> g.bds)   (pp_suite pp_bd)
  ]

let rec quote_tele typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, typ)) ->
    let (res_typs, l) = quote_tele typs' in
    let typ_tm = quote l typ in
    (Ext (res_typs,(nm, typ_tm)),l+1)

let dump_ctx gma =
  (* let (tele,_) = quote_tele gma.types in *)
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_value)))
    gma.types

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

exception Typing_error of string

let rec check gma expr typ =
  (* let typ_tm = quote gma.lvl typ in  *)
  pr "Checking %a has type %a@," pp_expr expr pp_value typ ;
  dump_ctx gma;
  match (expr, mforce typ) with
  
  | (LamE (nm,e) , PiV (_,a,b)) ->
    let bdy = check (bind gma nm a) e (b $$ varV (gma.lvl)) in
    LamT (nm,bdy)

  | (HoleE , _) -> fresh_meta (gma.bds)

  | (e, expected) ->
    let (e',inferred) = infer gma e in
    unify (gma.lvl) expected inferred ; e'

and infer gma expr =
  pr "Inferring type of %a@," pp_expr expr ;
  dump_ctx gma; 
  match expr with

  | VarE nm ->
    let (idx,typ) = assoc_with_idx nm gma.types in
    pr "Inferred variable of index %d to have type: %a@," idx pp_value typ ;
    (VarT idx, typ)

  | LamE (nm,e) ->
    let a = eval (gma.rho) (fresh_meta gma.bds) in
    let (e', t) = infer (bind gma nm a) e in
    (LamT (nm,e') , PiV (nm,a,Closure (gma.rho,quote (gma.lvl + 1) t)))

  | AppE (u,v) ->
    let (u',ut) = infer gma u in
    let (a,b) = match mforce ut with
      | PiV (_,a,b) -> (a,b)
      | _ ->
        let a = eval (gma.rho) (fresh_meta gma.bds) in
        let b = Closure (gma.rho , fresh_meta (bind gma "x" a).bds) in
        unify gma.lvl ut (PiV ("x",a,b)); 
        (a,b)
    in let v' = check gma v a in 
    (AppT (u', v') , b $$ eval gma.rho u')

  | PiE (nm,a,b) ->
    let a' = check gma a TypV in
    let b' = check (bind gma nm (eval gma.rho a')) b TypV in
    (PiT (nm,a',b') , TypV)

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
  | Ext (tl',(nm,expr)) ->
    abstract_tele tl' (PiE (nm,expr,ty)) (LamE (nm,tm))
    
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
    check_defs (define gma id tm_val ty_val) ds

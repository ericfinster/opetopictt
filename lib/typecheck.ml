(*****************************************************************************)
(*                                                                           *)
(*                           Typechecking Routines                           *)
(*                                                                           *)
(*****************************************************************************)

open Fmt

open Base
open Suite
open Expr
open Term
open Value
open Eval
open Syntax

open Opetopes.Idt
open Opetopes.Complex

(*****************************************************************************)
(*                           Typechecking Contexts                           *)
(*****************************************************************************)

(* Elements which can be locally bound *) 
type bound_element =
  | BoundVar of value * lvl 
  | BoundName of value * value

let get_binding qnm bndgs =
  match qnm with
  | Name nm ->
    begin match assoc_with_idx_opt nm bndgs with
      | Some (i,BoundVar (ty,_)) -> Some (VarT i , ty)
      | Some (i,BoundName (ty,_)) -> Some (VarT i , ty)
      | None -> None 
    end
  | Qual _ -> None

(* The Typchecking Context *) 
type ctx = {

  (* This won't be enough: we'll also need the names *) 
  global_scope  : value entry_map ; 
  bindings      : (name * bound_element) suite ;
  level         : lvl ;
  module_params : term tele ;
  qual_prefix   : string suite ;
  
}

let empty_ctx = {
  global_scope = Emp ;
  bindings = Emp ;
  level = 0 ;
  module_params = Emp ;
  qual_prefix = Emp ;
} 
  
let bind_var gma nm ty =
  { gma with
    bindings =
      gma.bindings |@>
      (nm , BoundVar (ty, gma.level)) ; 
    level = gma.level + 1 ;
  }

let bind_let gma nm ty tm =
  { gma with
    bindings =
      gma.bindings |@>
      (nm , BoundName (ty,tm));
    level = gma.level + 1;
  }

(* let define gma def =
 *   { gma with
 *     local_scope =
 *       gma.local_scope |@> def ; 
 *   }  *)
  
let names gma =
  map_suite gma.bindings ~f:fst

let loc gma =
  fold_left gma.bindings Emp
    (fun acc (_,b) ->
       match b with
       | BoundVar (_,l) -> acc |@> varV l
       | BoundName (_,tm) -> acc |@> tm
    )

(* top level guys are evaluated with no local bindings ... *) 
let top gma qnm =
  match resolve_qname qnm gma.global_scope with
  | Some (_,tm) -> tm 
  | None -> failwith "unresolved name" 

(*****************************************************************************)
(*                               Typing Errors                               *)
(*****************************************************************************)
           
type typing_error = [
  | `NameNotInScope of qname
  | `TypeMismatch of expr * expr * expr
  | `NotImplemented of string
  | `InferrenceFailed of expr
  | `ExpectedFunction of expr
  | `ExpectedProduct of expr 
  | `InvalidShape of string 
  | `InternalError of string 
]

let pp_error ppf e =
  match e with
  | `NameNotInScope qnm ->
    
    Fmt.pf ppf "Name not in scope: %a" pp_qname qnm
      
  | `TypeMismatch (e,exp,inf) ->

    Fmt.pf ppf "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
    Fmt.pf ppf "@[<v>has type: @,@, @[%a@]@,@,@]" pp_expr inf;
    Fmt.pf ppf "@[<v>but was expected to have type: @,@, @[%a@]@,@]" pp_expr exp;

  | `NotImplemented f ->

    Fmt.pf ppf "Feature not implemented: %s" f
      
  | `InferrenceFailed e ->

    Fmt.pf ppf "Failed to infer the type of: %a" pp_expr e
      
  | `ExpectedFunction e -> 

    Fmt.pf ppf "The expression @,@, @[%a@] @,@," pp_expr e ;
    Fmt.pf ppf "was expected to be a function but isn't"

  | `ExpectedProduct e -> 

    Fmt.pf ppf "The expression @,@, @[%a@] @,@," pp_expr e ;
    Fmt.pf ppf "was expected to be a product but isn't"

  | `InvalidShape msg -> pf ppf "Shape error: %s" msg 

  | `InternalError msg -> Fmt.pf ppf "Internal Error: %s" msg 


(*****************************************************************************)
(*                            Typechecking Monad                             *)
(*****************************************************************************)

type 'a tcm = ctx -> ('a , typing_error) Result.t

module TcmBasic = 
  struct

    type 'a t = 'a tcm
        
    let return a _ = Ok a
    let bind m ~f:f gma =
      match m gma with
      | Ok x -> f x gma 
      | Error e -> Error e

    let map m ~f:f gma =
      Result.map (m gma) ~f:f

    let map = `Custom map

    let apply mf ma =
      bind mf ~f:(fun f ->
          bind ma ~f:(fun a ->
              return (f a)))
      
  end
  
module TcmMonad = Monad.Make(TcmBasic) 
module TcmApplicative = Applicative.Make(TcmBasic)
module TcmTraverse = TreeTraverse(TcmBasic) 
module TcmComplexTraverse = ComplexTraverse(TcmBasic)

let (let*) m f = TcmMonad.bind m ~f 
let tcm_ok = TcmMonad.return 
let tcm_fail e _ = Error e 

let tcm_ctx gma = Ok gma
      
let tcm_eval (t : term) : value tcm =
  let* gma = tcm_ctx in
  tcm_ok (eval (top gma) (loc gma) t)

let tcm_quote (v : value) (ufld : bool) : term tcm =
  let* gma = tcm_ctx in
  tcm_ok (quote ufld gma.level v)

let tcm_in_ctx g m _ = m g 

let tcm_with_var_binding nm ty m =
  let* gma = tcm_ctx in
  tcm_in_ctx (bind_var gma nm ty) m 

let tcm_with_let_binding nm ty tm m =
  let* gma = tcm_ctx in
  tcm_in_ctx (bind_let gma nm ty tm) m

let tcm_with_local_defn _ _ =
  failwith "definitions not done"
  (* let* gma = tcm_ctx in
   * tcm_in_ctx (define gma def) m  *)

let rec tcm_extract_pi (v: value) =
  match v with
  | PiV (_,a,b) -> tcm_ok (a, b)
  | TopV (_,_,v') -> tcm_extract_pi v'
  | _ ->
    let* gma = tcm_ctx in 
    let e = term_to_expr (names gma) (quote false gma.level v) in 
    tcm_fail (`ExpectedFunction e) 

let rec tcm_extract_sig (v: value) =
  match v with
  | SigV (_,a,b) -> tcm_ok (a, b)
  | TopV (_,_,v') -> tcm_extract_sig v'
  | _ ->
    let* gma = tcm_ctx in 
    let e = term_to_expr (names gma) (quote false gma.level v) in 
    tcm_fail (`ExpectedProduct e) 

let tcm_ensure (b : bool) (e : typing_error) : unit tcm =
  if b then tcm_ok ()
  else tcm_fail e
      
let tcm_to_cmplx c =
  let open IdtConv in 
  try let c' = to_cmplx c in
    let _ = validate_opetope c' in 
    tcm_ok c' 
  with TreeExprError msg -> tcm_fail (`InvalidShape msg)
     | ShapeError msg -> tcm_fail (`InvalidShape msg) 

(*****************************************************************************)
(*                            Typechecking Rules                             *)
(*****************************************************************************)

let rec tcm_check (e : expr) (t : value) : term tcm =

  match (e , t) with

  | (e , TopV (_,_,tv)) -> tcm_check e tv

  | (LetE (nm,ty,tm,bdy), _) ->
    let* ty' = tcm_check ty TypV in
    let* tyv = tcm_eval ty' in
    let* tm' = tcm_check tm tyv in
    let* tmv = tcm_eval tm' in 
    let* bdy' = tcm_with_let_binding nm tyv tmv 
        (tcm_check bdy t) in 
    tcm_ok (LetT (nm,ty',tm',bdy'))

  | (LamE (nm,e) , PiV (_,a,b)) ->
    let* gma = tcm_ctx in
    tcm_in_ctx (bind_var gma nm a)
      begin
        let* bdy = tcm_check e (b (varV gma.level)) in
        tcm_ok (LamT (nm,bdy))
      end

  | (PairE (u,v) , SigV (_,a,b)) ->
    let* u' = tcm_check u a in
    let* uv = tcm_eval u' in
    let* v' = tcm_check v (b uv) in
    tcm_ok (PairT (u',v')) 

  | (e, expected) ->

    let* gma = tcm_ctx in 
    let* (e',inferred) = tcm_infer e in

    let inferred_nf = quote true gma.level inferred in
    let expected_nf = quote true gma.level expected in

    if (not (term_eq expected_nf inferred_nf)) 
    then
      let exp_e = term_to_expr (names gma) expected_nf in
      let inf_e = term_to_expr (names gma) inferred_nf in
      tcm_fail (`TypeMismatch (e,exp_e,inf_e))
    else tcm_ok e'

and tcm_infer (e : expr) : (term * value) tcm =

  match e with

  | VarE qnm ->
    let* gma = tcm_ctx in
    begin match get_binding qnm gma.bindings with
      | Some (tm,ty) -> tcm_ok (tm, ty)
      | None ->
        log_val "qnm" qnm pp_qname;
        log_val "names" (all_qnames Emp gma.global_scope) (pp_suite pp_qname) ; 
        begin match resolve_qname qnm gma.global_scope with
          | Some (ty,_) -> tcm_ok (TopT qnm , ty) 
          | _ -> tcm_fail (`NameNotInScope (qnm))
        end
    end

  | LetE (nm,ty,tm,bdy) ->
    let* ty' = tcm_check ty TypV in
    let* tyv = tcm_eval ty' in
    let* tm' = tcm_check tm tyv in
    let* tmv = tcm_eval tm' in 
    let* (bdy',bdyty) = tcm_with_let_binding nm tyv tmv 
        (tcm_infer bdy) in 
    tcm_ok (LetT (nm,ty',tm',bdy'),bdyty)

  | AppE (u,v) ->

    let* (u',ut) = tcm_infer u in
    let* (a , b) = tcm_extract_pi ut in
    let* v' = tcm_check v a in
    let* vv = tcm_eval v' in 
    tcm_ok (AppT (u',v') , b vv)

  | PiE (nm,a,b) ->
    let* a' = tcm_check a TypV in
    let* av = tcm_eval a' in
    let* b' = tcm_with_var_binding nm av
        (tcm_check b TypV) in 

    tcm_ok (PiT (nm,a',b') , TypV)

  | FstE u ->
    let* (u',ut) = tcm_infer u in
    let* (a, _) = tcm_extract_sig ut in
    tcm_ok (FstT u', a)

  | SndE u ->
    let* (u',ut) = tcm_infer u in
    let* (_, b) = tcm_extract_sig ut in
    let* uv = tcm_eval u' in
    tcm_ok (SndT u', b (fst_val uv))

  | SigE (nm,a,b) ->
    let* a' = tcm_check a TypV in
    let* av = tcm_eval a' in
    let* b' = tcm_with_var_binding nm av
        (tcm_check b TypV) in 

    tcm_ok (SigT (nm,a',b') , TypV)

  | TypE -> tcm_ok (TypT , TypV)

  | ReflE (u,pi) ->
    let* (u',ut) = tcm_infer u in
    let* pi' = tcm_to_cmplx pi in

    if (is_obj pi') then tcm_ok (ReflT (u',pi') , ut) else
      
      let rt = fst_val (refl_val Emp 0 ut pi') in
      
      let* uv = tcm_eval u' in
      let uc = map_cmplx (face_cmplx (tail_of pi'))
          ~f:(fun f -> refl_val Emp 0 uv f) in 

      tcm_ok (ReflT (u',pi') , app_args rt (labels uc))

  | _ -> tcm_fail (`InferrenceFailed e) 

let rec tcm_in_tele : 'a. expr tele
  -> (term tele -> value tele -> 'a tcm)
  -> 'a tcm = 
  fun tl k -> 
  match tl with
  | Emp -> k Emp Emp
  | Ext (tl',(id,ty)) ->
    tcm_in_tele tl' (fun tt vt -> 
        let* ty_tm = tcm_check ty TypV in
        let* ty_val = tcm_eval ty_tm in
        let* gma = tcm_ctx in
        tcm_in_ctx (bind_var gma id ty_val)
          (k (tt |@> (id,ty_tm)) (vt |@> (id,ty_val))))

let rec tcm_check_defns defs =
  match defs with
  | [] -> tcm_ok Emp
  | (nm , ModuleEntry md)::ds ->

    Fmt.pr "----------------@,";
    Fmt.pr "Entering module: %s@," nm;
    
    let* vm = tcm_check_module_contents
        nm (to_list md.params) md.entries in

    Fmt.pr "----------------@,";
    Fmt.pr "Module %s complete.@," nm; 

    let* gma = tcm_ctx in
    let* rs = tcm_in_ctx
        ({ gma with global_scope =
                      insert_entry (to_list gma.qual_prefix)
                        nm vm gma.global_scope })
        (tcm_check_defns ds) in 
    
    tcm_ok (rs |@> (nm,vm))
      
  | (nm, TermEntry (ty,tm))::ds ->
    
    Fmt.pr "----------------@,";
    Fmt.pr "Checking definition: %s@," nm;
    
    let* ty' = tcm_check ty TypV in
    let* tyv = tcm_eval ty' in 
    let* tm' = tcm_check tm tyv in 
    let* tmv = tcm_eval tm' in

    Fmt.pr "Checking complete for %s@," nm;
    let* gma = tcm_ctx in 
    let exp = term_to_expr (names gma) tm' in 
    Fmt.pr "Result: @[%a@]@," pp_expr exp ; 


    let (fty,ftm) = TermUtil.abstract_tele_with_type
                      gma.module_params ty' tm' in 

    (* Hmmm.  But there should be a version which just works on values, no? *)
    (* Hmmm. Actually, I'm not sure how to do this correctly ... *) 
    let* ftyv = tcm_eval fty in
    let* ftmv = tcm_eval ftm in 
    
    let gma' = { gma with
                 bindings = gma.bindings |@> (nm, BoundName (tyv,tmv)) } in 

    let* rs = tcm_in_ctx gma'
        (tcm_check_defns ds) in 

    
    tcm_ok (rs |@> (nm, TermEntry (ftyv,ftmv))) 
      
and tcm_check_module_contents nm params defns =
  match params with
  | [] ->
    let* gma = tcm_ctx in
    let* defns = tcm_in_ctx ({ gma with qual_prefix = gma.qual_prefix |@> nm })
        (tcm_check_defns (to_list defns)) in
    tcm_ok (ModuleEntry { params = Emp ; entries = defns })
  | (id,ty)::ps ->
    let* ty_tm = tcm_check ty TypV in
    let* ty_val = tcm_eval ty_tm in
    let* gma = tcm_ctx in
    let gma' = { gma with
                 bindings = gma.bindings |@> (id, BoundVar (ty_val,gma.level)) ; 
                 module_params = gma.module_params |@> (id,ty_tm)
               } in
    tcm_in_ctx gma' (tcm_check_module_contents nm ps defns)
        

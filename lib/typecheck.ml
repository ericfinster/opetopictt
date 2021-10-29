
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

let bind_name gma nm ty tm =
  { gma with
    bindings =
      gma.bindings |@>
      (nm , BoundName (ty, tm));
    level = gma.level + 1;
  }

let names gma =
  map_suite gma.bindings ~f:fst

let loc gma =
  fold_left gma.bindings Emp
    (fun acc (_,b) ->
       match b with
       | BoundVar (_,l) -> acc |@> varV l
       | BoundName (_,tm) -> acc |@> tm
    )

let bvars gma = 
  fold_left gma.bindings Emp
    (fun acc (_,b) ->
       match b with
       | BoundVar (_,l) -> acc |@> varV l
       | BoundName _ -> acc 
    )

let top gma qnm =
  (* log_val "qnm" qnm pp_qname;
   * log_val "names" (all_qnames Emp gma.global_scope) (pp_suite pp_qname) ;  *)
  match resolve_qname qnm gma.global_scope with
  | Some (_,tm) -> tm 
  | None -> failwith (Fmt.str "Unresolved name: %a" pp_qname qnm)

let log_bindings gma =
  log_val "bindings" (map_suite gma.bindings ~f:fst)
    (pp_suite Fmt.string) ;
  log_val "level" gma.level Fmt.int 

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
  tcm_in_ctx (bind_name gma nm ty tm) m

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
          | Some (ty,_) ->

            let* ty_tm = tcm_quote ty false in
            let ty_ex = term_to_expr (names gma) ty_tm in
            log_msg "read a global" ;
            log_val "ty_ex" ty_ex pp_expr ; 
            
            tcm_ok (TopT qnm , ty) 
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
    
    let* md' = tcm_check_module_contents
        nm (to_list md.params) md.entries in

    Fmt.pr "----------------@,";
    Fmt.pr "Module %s complete.@," nm; 

    let* gma = tcm_ctx in
    let* rs = tcm_in_ctx
        ({ gma with global_scope =
                      insert_entry (to_list gma.qual_prefix)
                        nm (ModuleEntry md') gma.global_scope })
        (tcm_check_defns ds) in 
    
    tcm_ok (rs |@> (nm,ModuleEntry md'))
      
  | (nm, TermEntry (ty,tm))::ds ->
    
    Fmt.pr "----------------@,";
    Fmt.pr "Checking definition: %s@," nm;

    let* gma = tcm_ctx in
    log_bindings gma;

    log_val "ty" ty pp_expr;
    let* ty' = tcm_check ty TypV in
    log_msg "type check";
    let* tyv = tcm_eval ty' in
    log_msg "type eval";
    let* tm' = tcm_check tm tyv in
    log_msg "term check";
    let* tmv = tcm_eval tm' in
    log_msg "term eval";

    Fmt.pr "Checking complete for %s@," nm;

    (* let exp_ty = term_to_expr (names gma) ty' in 
     * let exp_tm = term_to_expr (names gma) tm' in
     * Fmt.pr "Type: @[%a@]@," pp_expr exp_ty ; 
     * Fmt.pr "Result: @[%a@]@," pp_expr exp_tm ; *)

    let* glbl_ty = tcm_quote tyv false in
    let* glbl_tm = tcm_quote tmv false in 

    log_val "glbl_ty" glbl_ty pp_term;
    log_val "glbl_tm" glbl_tm pp_term;
    
    let (fty,ftm) = TermUtil.abstract_tele_with_type
        gma.module_params glbl_ty glbl_tm in

    (* Can we apply the arguments and bind here ? *)

    log_val "fty" fty pp_term;
    log_val "ftm" ftm pp_term;
    
    let fty_exp = term_to_expr Emp fty in
    let ftm_exp = term_to_expr Emp ftm in
    
    log_val "fty_exp" fty_exp pp_expr ;
    log_val "ftm_exp" ftm_exp pp_expr ;
    
    (* Evaluate the globalized terms *) 
    let ftyv = eval (top gma) Emp fty in
    let ftmv = eval (top gma) Emp ftm in 

    (* Synthesizing the global reference ... *) 
    let term_qname = with_prefix gma.qual_prefix (Name nm) in
    let term_val = TopV (term_qname,EmpSp,ftmv) in

    (* BUG: the indices here are wrong. they should refer to 
       the global, not local variables *) 
    let global_term = app_args term_val (to_list (bvars gma)) in 
        (* (List.map (List.range 0 (length (bvars gma)))
         * ~f:(fun l -> varV l)) in  *)

    (* Now bind everything *) 
    let gma' = { gma with
                 bindings = gma.bindings |@>
                            (nm, BoundName (tyv,global_term)) ; 
                 global_scope = insert_entry (to_list gma.qual_prefix)
                     nm (TermEntry (ftyv,ftmv)) gma.global_scope ; 
                 level = gma.level + 1 
               } in 

    
    let* rs = tcm_in_ctx gma'
        (tcm_check_defns ds) in 

    tcm_ok (rs |@> (nm, TermEntry (ftyv,ftmv))) 
      
and tcm_check_module_contents nm params defns =
  match params with
  | [] ->
    let* gma = tcm_ctx in
    let* defns = tcm_in_ctx
        ({ gma with
           qual_prefix = gma.qual_prefix |@> nm ;
           global_scope = insert_entry (to_list gma.qual_prefix)
                        nm (ModuleEntry empty_module) gma.global_scope 
         })
        (tcm_check_defns (to_list defns)) in
    tcm_ok ({ params = Emp ; entries = defns })
  | (id,ty)::ps ->
    let* ty_tm = tcm_check ty TypV in
    (* BUG: the module parameters could also use global defintiions.
       Doesn't this mean we need to take special action here? *) 
    let* ty_val = tcm_eval ty_tm in
    let* glbl_ty_tm = tcm_quote ty_val false in 
    let* gma = tcm_ctx in
    let gma' = { gma with
                 bindings = gma.bindings |@> (id, BoundVar (ty_val,gma.level)) ;
                 level = gma.level + 1 ;
                 module_params = gma.module_params |@> (id,glbl_ty_tm)
               } in
    tcm_in_ctx gma' (tcm_check_module_contents nm ps defns)

let open_module prefix md gma =
  let new_bindings =
    fold_left md.entries Emp
      (fun acc en ->
         match en with
         | (nm, TermEntry (ty,tm)) ->
           let top_tm = TopV (with_prefix prefix (Name nm), EmpSp, tm) in 
           acc |@> (nm, BoundName (ty, top_tm)) 
         | _ -> acc) in

  { gma with
    bindings = append gma.bindings new_bindings ; 
    level = gma.level + length new_bindings ; 
  } 

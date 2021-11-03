
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
open Reflexivity

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


type section_desc = {
    params : term tele ;
    names : name suite ; 
}

let empty_section = {
  params = Emp ;
  names = Emp ;
}
    
let params_level secs =
  fold_left secs 0
    (fun acc s -> acc + length s.params)

let rec section_level secs nm =
  match secs with
  | Emp -> 0
  | Ext (secs',s) ->
    if List.exists (to_list s.names)
        ~f:(fun nm' -> String.equal nm nm') then
      params_level secs
    else section_level secs' nm 

let section_params secs =
  fold_left secs Emp
    (fun acc sec -> append acc sec.params)
    
(* The Typchecking Context *) 
type ctx = {

  global_scope  : (name * (term * term)) suite ; 
  bindings      : (name * bound_element) suite ;
  sections      : section_desc suite ; 
  level         : lvl ;
  shapes        : (name * name cmplx) suite ;
  
}

let empty_ctx = {
  global_scope = Emp ;
  bindings = Emp ;
  level = 0 ;
  sections = Emp;
  shapes = Emp; 
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

let rec top gma qnm =
  (* log_val "qnm" qnm pp_qname;
   * log_val "names" (all_qnames Emp gma.global_scope) (pp_suite pp_qname) ;  *)
  match assoc_opt (short_name qnm) gma.global_scope with
  | Some (_,tm) -> eval (top gma) Emp tm 
  | None -> raise (Internal_error (Fmt.str "Unresolved name: %a" pp_qname qnm))

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
  try tcm_ok (quote ufld gma.level v) with
  | Internal_error msg ->
    tcm_fail (`InternalError
                (Fmt.str "@[<v>Failed to quote: %a@,Message: %s@,@]"
                   pp_value v msg))

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
    let* t = tcm_quote v false in 
    let e = term_to_expr (names gma) t in 
    tcm_fail (`ExpectedFunction e) 

let rec tcm_extract_sig (v: value) =
  match v with
  | SigV (_,a,b) -> tcm_ok (a, b)
  | TopV (_,_,v') -> tcm_extract_sig v'
  | _ ->
    let* gma = tcm_ctx in
    let* t = tcm_quote v false in 
    let e = term_to_expr (names gma) t in 
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

  (* TODO: this means that if you are checking with a defined type, 
     then the error will always be unfolded.  That's a bit annoying .. *) 
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
      
      let inf_folded = quote false gma.level inferred in
      let exp_folded = quote false gma.level expected in 
      let exp_e = term_to_expr (names gma) exp_folded in
      let inf_e = term_to_expr (names gma) inf_folded in
      tcm_fail (`TypeMismatch (e,exp_e,inf_e))
        
    else tcm_ok e'

and tcm_infer (e : expr) : (term * value) tcm =

  match e with

  | VarE qnm ->
    let* gma = tcm_ctx in
    begin match get_binding qnm gma.bindings with
      | Some (tm,ty) -> tcm_ok (tm, ty)
      | None ->
        (* log_msg "infering top-level"; 
         * log_val "qnm" qnm pp_qname; *)
        begin match assoc_opt (short_name qnm) gma.global_scope with
          | Some (ty,_) ->

            (* log_val "gty" ty pp_term;
             * log_val "gtm" tm pp_term ; *)
            
            let tyv = eval (top gma) Emp ty in
            let sec_lvl = section_level gma.sections (short_name qnm) in

            (* log_val "sec_lvl" sec_lvl Fmt.int; *)
            
            let lvls = List.range 0 sec_lvl in 
            (* log_val "lvls" lvls (Fmt.list Fmt.int) ; *)
            
            let v_vars = List.map lvls ~f:varV in
            let t_vars = List.map lvls ~f:(fun l -> VarT (lvl_to_idx gma.level l)) in
            
            let top_tm = TermUtil.app_args (TopT qnm) (from_list t_vars) in

            (* log_val "top_tm" top_tm pp_term ; *)

            tcm_ok (top_tm , app_pi_args tyv v_vars)
              
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

  (* TODO: this is ugly, these next two should be combined ... *) 
  | ReflE (u, First nm) ->
    let* gma = tcm_ctx in
    begin match assoc_opt nm gma.shapes with
      | None -> tcm_fail (`NameNotInScope (Name nm))
      | Some pi' ->
        
        let* (u',ut) = tcm_infer u in

        if (is_obj pi') then tcm_ok (ReflT (u',nm,pi') , ut) else

          let rt = fst_val (refl_val Emp 0 ut nm pi') in

          let* uv = tcm_eval u' in
          let uc = map_cmplx (face_cmplx (tail_of pi'))
              ~f:(fun f -> refl_val Emp 0 uv "" f) in 

          tcm_ok (ReflT (u',nm,pi') , app_args rt (labels uc))
    end
      
  | ReflE (u, Second pi) ->
    let* (u',ut) = tcm_infer u in
    let* pi' = tcm_to_cmplx pi in

    if (is_obj pi') then tcm_ok (ReflT (u',"",pi') , ut) else
      
      let rt = fst_val (refl_val Emp 0 ut "" pi') in
      
      let* uv = tcm_eval u' in
      let uc = map_cmplx (face_cmplx (tail_of pi'))
          ~f:(fun f -> refl_val Emp 0 uv "" f) in 

      tcm_ok (ReflT (u',"",pi') , app_args rt (labels uc))

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
  | [] -> tcm_ctx 
  | (nm , ModuleEntry md)::ds ->

    Fmt.pr "----------------@,";
    Fmt.pr "Entering module: %s@," nm;

    let* gma = tcm_ctx in
    let gma' = { gma with
                 sections = gma.sections |@>
                            empty_section 
               } in
    
    let* gma'' = tcm_in_ctx gma'
        (tcm_check_module_contents
           nm (to_list md.params) md.entries) in

    let gma''' = match gma''.sections with
      | Emp -> gma''
      | Ext (Emp,s) ->
        let l = length s.params in 
        { gma'' with
          level = gma''.level - l ; 
          bindings = fst (grab l gma''.bindings) ;
          sections = Emp ; 
        }
      | Ext (Ext (secs',s),t) ->
        let l = length t.params in
        { gma'' with
          level = gma''.level - l ; 
          bindings = fst (grab l gma''.bindings) ; 
          sections = secs' |@> { s with names = append s.names t.names }
        } in 
    
    Fmt.pr "----------------@,";
    Fmt.pr "Module %s complete.@," nm; 

    tcm_in_ctx gma''' 
      (tcm_check_defns ds)
      
  | (nm, TermEntry (ty,tm))::ds ->
    
    Fmt.pr "----------------@,";
    Fmt.pr "Checking definition: %s@," nm;

    let* gma = tcm_ctx in
    (* log_bindings gma; *)

    (* log_val "ty" ty pp_expr; *)
    let* ty' = tcm_check ty TypV in
    (* log_msg "type check"; *)
    let* tyv = tcm_eval ty' in
    (* log_msg "type eval"; *)
    let* tm' = tcm_check tm tyv in
    (* log_msg "term check"; *)
    let* tmv = tcm_eval tm' in
    (* log_msg "term eval"; *)

    Fmt.pr "Checking complete for %s@," nm;

    (* let exp_ty = term_to_expr (names gma) ty' in 
     * let exp_tm = term_to_expr (names gma) tm' in
     * Fmt.pr "Type: @[%a@]@," pp_expr exp_ty ; 
     * Fmt.pr "Result: @[%a@]@," pp_expr exp_tm ; *)

    let* glbl_ty = tcm_quote tyv true in
    let* glbl_tm = tcm_quote tmv true in 

    (* log_val "glbl_ty" glbl_ty pp_term;
     * log_val "glbl_tm" glbl_tm pp_term; *)
    
    let (fty,ftm) = TermUtil.abstract_tele_with_type
        (section_params gma.sections) glbl_ty glbl_tm in

    (* Can we apply the arguments and bind here ? *)

    (* log_val "fty" fty pp_term;
     * log_val "ftm" ftm pp_term; *)
    
    (* let fty_exp = term_to_expr Emp fty in
     * let ftm_exp = term_to_expr Emp ftm in
     * 
     * log_val "fty_exp" fty_exp pp_expr ;
     * log_val "ftm_exp" ftm_exp pp_expr ; *)

    let secs = match gma.sections with
      | Emp -> Emp
      | Ext (secs',s) -> secs' |@>
                         { s with names = s.names |@> nm } in 
                                   
    let gma' = { gma with
                 global_scope = gma.global_scope |@>
                                (nm,(fty,ftm)) ;
                 sections = secs ; 
               } in 

    
    tcm_in_ctx gma' (tcm_check_defns ds) 

    (* tcm_ok (rs |@> (nm, TermEntry (ftyv,ftmv)))  *)

  | (nm, ShapeEntry (First pi))::ds ->
    let* pi' = tcm_to_cmplx pi in
    log_msg (Fmt.str "Defined shape: %s" nm) ; 
    let* gma = tcm_ctx in
    tcm_in_ctx { gma with shapes = gma.shapes |@> (nm, pi') }
      (tcm_check_defns ds)
      
  | (nm, ShapeEntry (Second _))::ds ->
    log_msg (Fmt.str "Skipping already checked shape %s" nm) ;
    tcm_check_defns ds 


and tcm_check_module_contents nm params defns =
  match params with
  | [] ->
    let* gma = tcm_ctx in
    let* gma' = tcm_in_ctx gma
        (tcm_check_defns (to_list defns)) in
    tcm_ok gma'
  | (id,ty)::ps ->
    let* ty_tm = tcm_check ty TypV in
    let* ty_val = tcm_eval ty_tm in
    let* glbl_ty_tm = tcm_quote ty_val false in 
    let* gma = tcm_ctx in
    begin match gma.sections with
      | Emp -> raise (Internal_error "No active section")
      | Ext (secs,s) ->
        let gma' = { gma with
                     
                     bindings = gma.bindings |@>
                                (id, BoundVar (ty_val,gma.level)) ;
                     
                     level = gma.level + 1 ;
                     
                     sections = secs |@>
                                { s with params = s.params |@>
                                                  (id,glbl_ty_tm)
                                } ; 
                   } in
        tcm_in_ctx gma' (tcm_check_module_contents nm ps defns)

    end
    


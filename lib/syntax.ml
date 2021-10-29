(*****************************************************************************)
(*                                                                           *)
(*                        Generic Syntax Constructions                       *)
(*                                                                           *)
(*****************************************************************************)

open Suite
open Base

open Opetopes.Idt
open Opetopes.Complex

(*****************************************************************************)
(*                             Basic Syntax Types                            *)
(*****************************************************************************)

type lvl = int
type idx = int
type mvar = int
type name = string

let lvl_to_idx k l = k - l - 1
let idx_to_lvl k i = k - i - 1

type 'a decl = (name * 'a)
type 'a tele = ('a decl) suite

let tele_sem_eq (eq : 'a -> 'a -> bool) :
  'a tele -> 'a tele -> bool =
  fun tla tlb ->
  suite_eq (fun (_,a) (_,b) -> eq a b) tla tlb

(*****************************************************************************)
(*                             Logging functions                             *)
(*****************************************************************************)

let log_msg ?idt:(i=0) (s : string) =
  let indt = String.make i ' ' in 
  Fmt.pr "@[<v>%s@,@]" (indt ^ s)
    
let log_val ?idt:(i=0) (s : string) (a : 'a) (pp : 'a Fmt.t) =
  let indt = String.make i ' ' in 
  Fmt.pr "@[<v>%s: @[%a@]@,@]" (indt ^ s) pp a

(*****************************************************************************)
(*                             Logging functions                             *)
(*****************************************************************************)

exception Internal_error of string 

(*****************************************************************************)
(*                             Qualified Names                               *) 
(*****************************************************************************)

type qname =
  | Name of string
  | Qual of string * qname

let rec short_name qnm =
  match qnm with
  | Name nm -> nm
  | Qual (_,qn) -> short_name qn
    
let rec qname_eq qnm qnm' =
  match (qnm , qnm') with
  | (Name nm , Name nm') ->
    String.equal nm nm'
  | (Qual (m,qn) , Qual (m',qn')) ->
    if (String.equal m m') then
      qname_eq qn qn'
    else false
  | _ -> false

(*****************************************************************************)
(*                                 Modules                                   *)
(*****************************************************************************)

type 'a module_desc = {
  params : 'a tele ; 
  entries : 'a entry_map ; 
}
  
and 'a module_entry =
  | ModuleEntry of 'a module_desc
  | TermEntry of 'a * 'a

and 'a entry_map =
  (name * 'a module_entry) suite

let empty_module = {
  params = Emp ;
  entries = Emp ; 
}

let rec resolve_qname qnm ents =
  match qnm with
  | Name nm ->
    begin match assoc_opt nm ents with
      | Some (TermEntry (ty,tm)) -> Some (ty,tm)
      | _ -> None
    end
  | Qual (mn,qn) -> 
    begin match assoc_opt mn ents with
      | Some (ModuleEntry md') ->
        resolve_qname qn md'.entries 
      | _ -> None
    end

let rec insert_entry prefix name entry emap =
  (* log_msg "Inserting ..." ; 
   * log_val "prefix" prefix (Fmt.list ~sep:(Fmt.any ".") Fmt.string) ; 
   * log_val "name" name Fmt.string ; *)
  match prefix with
  | [] -> emap |@> (name,entry)
  | nm::ps ->
    begin
      match Suite.open_where (fun (nm',_) -> String.equal nm nm') emap with
      | Some (l,(_,ModuleEntry md),r) ->
        let md' = { md with entries = insert_entry ps name entry md.entries } in
        append_list (Ext (l,(nm,ModuleEntry md'))) r 
      | _ -> failwith (Fmt.str "Invalid prefix: %s" nm)
    end


let rec with_prefix prefix qnm =
  match prefix with
  | Emp -> qnm
  | Ext (ps,p) -> with_prefix ps (Qual (p,qnm))
    
let rec all_qnames prefix emap =
  match emap with
  | Emp -> Emp
  | Ext (em',(nm,TermEntry _)) ->
    let nms = all_qnames prefix em' in
    Ext (nms, with_prefix prefix (Name nm))
  | Ext (em',(nm,ModuleEntry md)) ->
    let nms = all_qnames prefix em' in
    let mnms = all_qnames (prefix |@> nm) md.entries in
    append (nms |@> with_prefix prefix (Name nm)) mnms 

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let tele_fold_with_idx g l f =
  fold_accum_cont g l
    (fun (nm,ict,tm) l' ->
       ((nm,ict,f tm l') , l'+1))

let pp_tele pp_el ppf tl =
  let pp_pair ppf (nm,t) =
    Fmt.pf ppf "(%s : %a)" nm pp_el t 
  in pp_suite pp_pair ppf tl


(*****************************************************************************)
(*                             Splitting                                     *)
(*****************************************************************************)
      
let rec split_nst
    (n : 'a suite nst) (g : 'b suite)
    (f : 'a -> 'b -> 'c)
  : 'c nst suite = 
  match n with
    | Lf s -> map_simul s g (fun a b -> Lf (f a b)) 
    | Nd (s,sh) ->
      let sh' = map_tr sh ~f:(fun v -> split_nst v g f) in
      let sh'' = split_tr sh' g (fun v _ -> v) in
      map_simul (map_simul s g (fun a b -> (a,b))) sh''
          (fun (a,b) v -> Nd (f a b,v)) 

and split_tr : 'a 'b 'c . 'a suite tr
  -> 'b suite -> ('a -> 'b -> 'c) 
  -> 'c tr suite = 
  fun t g f -> 
  match t with
  | Lf _ -> map_suite g ~f:(fun _ -> Lf ()) 
  | Nd (s,sh) ->
    let sh' = map_tr sh ~f:(fun v -> split_tr v g f) in
    let sh'' = split_tr sh' g (fun v _ -> v) in 
    map_simul (map_simul s g (fun a b -> (a,b)))
        sh'' (fun (a,b) v ->  Nd (f a b , v)) 
    
let rec split_cmplx (c : 'a suite cmplx) (g : 'b suite)
    (f : 'a -> 'b -> 'c)
  : 'c cmplx suite =
  match c with
  | Base n -> map_suite (split_nst n g f)
                ~f:(fun ns -> Base ns)
  | Adjoin (t,n) ->
    let ts = split_cmplx t g f in
    let ns = split_nst n g f in
    map_simul ts ns (fun t' n' -> Adjoin (t',n'))

let arr_cmplx src tgt arr =
  (~> (Nd (tgt, Nd (Lf src, Lf ())))
   |> Lf arr) 

(*****************************************************************************)
(*                               Generic Syntax                              *)
(*****************************************************************************)
    
module type Syntax = sig
  type s
  val var : lvl -> lvl -> name -> s 
  val lam : name -> s -> s
  val app : s -> s -> s 
  val pi : name -> s -> s -> s
  val pp_s : s Fmt.t
end

module SyntaxUtil(Syn : Syntax) = struct
  include Syn

  (* Utility Routines *)
  let app_args t args =
    fold_left args t
      (fun t' arg -> app t' arg) 

  let id_sub t =
    let k = length t in
    map_with_lvl t ~f:(fun l (nm,ict,_) ->
        (ict, var k l nm))
          
  let abstract_tele tele tm =
    fold_right tele tm (fun (nm,_) tm'  ->
        lam nm tm')

  let abstract_tele_with_type tl ty tm =
    fold_right tl (ty,tm)
      (fun (nm,ty) (ty',tm') ->
        (pi nm ty ty', lam nm tm'))

  let rec level_of tl nm =
    match tl with
    | Emp -> raise Lookup_error
    | Ext (tl',(nm',_,_)) ->
      if (String.(=) nm nm') then
        Suite.length tl'
      else level_of tl' nm 
  
end


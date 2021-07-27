(*****************************************************************************)
(*                                                                           *)
(*                        Generic Syntax Constructions                       *)
(*                                                                           *)
(*****************************************************************************)

open Suite
open Base

(*****************************************************************************)
(*                             Basic Syntax Types                            *)
(*****************************************************************************)

type lvl = int
type idx = int
type mvar = int
type name = string

let lvl_to_idx k l = k - l - 1
let idx_to_lvl k i = k - i - 1

type icit =
  | Impl
  | Expl

type occ =
  | Full
  | NonFull

type nm_ict = (name * icit)
type 'a decl = (name * icit * 'a)
type 'a tele = ('a decl) suite
type 'a judgmt = 'a tele * 'a * 'a 

let pp_ict ppf ict =
  match ict with
  | Impl -> Fmt.pf ppf "Impl"
  | Expl -> Fmt.pf ppf "Expl"

let pp_nm_ict ppf ni =
  let open Fmt in
  pf ppf "%a" (parens (pair ~sep:(any ",") string pp_ict)) ni
    
(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let tele_fold_with_idx g l f =
  fold_accum_cont g l
    (fun (nm,ict,tm) l' ->
       ((nm,ict,f tm l') , l'+1))

let pp_tele pp_el ppf tl =
  let pp_trpl ppf (nm,ict,t) =
    match ict with
    | Expl -> Fmt.pf ppf "(%s : %a)" nm pp_el t
    | Impl -> Fmt.pf ppf "{%s : %a}" nm pp_el t
  in pp_suite pp_trpl ppf tl

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
(*                               Generic Syntax                              *)
(*****************************************************************************)
    
module type Syntax = sig
  type s
  val var : lvl -> lvl -> name -> s 
  val lam : name -> icit -> s -> s
  val app : s -> s -> icit -> s 
  val pi : name -> icit -> s -> s -> s
  val pp_s : s Fmt.t
end

module SyntaxUtil(Syn : Syntax) = struct
  include Syn

  (* Utility Routines *)
  let app_args t args =
    fold_left args t
      (fun t' (ict,arg) -> app t' arg ict) 

  let id_sub t =
    let k = length t in
    map_with_lvl t ~f:(fun l (nm,ict,_) ->
        (ict, var k l nm))
          
  let abstract_tele tele tm =
    fold_right tele tm (fun (nm,ict,_) tm'  ->
        lam nm ict tm')

  let abstract_tele_with_type tl ty tm =
    fold_right tl (ty,tm)
      (fun (nm,ict,ty) (ty',tm') ->
        (pi nm ict ty ty', lam nm ict tm'))

  let rec level_of tl nm =
    match tl with
    | Emp -> raise Lookup_error
    | Ext (tl',(nm',_,_)) ->
      if (String.(=) nm nm') then
        Suite.length tl'
      else level_of tl' nm 
  
end


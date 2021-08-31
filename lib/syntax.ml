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

type 'a decl = (name * 'a)
type 'a tele = ('a decl) suite

type 'a dep_term = 'a suite * 'a option

module DepTermBasic =
struct

  type 'a t = 'a dep_term

  module SA = SuiteApplicative
  module SM = SuiteMonad
  module O = Option
      
  let return a =
    (SA.return a, O.return a)

  let bind (ma,mb) ~f =
    (SM.bind ma ~f:(fun a -> fst (f a)) ,
     O.bind mb ~f:(fun a -> snd (f a)))

  let map (ta : 'a dep_term) ~f:(f: 'a -> 'b) : 'b dep_term =
    (SA.map (fst ta) ~f:f, O.map (snd ta) ~f:f)
      
  let map = `Custom map
  
  let apply mf mx =
    bind mf ~f:(fun f ->
        bind mx ~f:(fun x ->
            return (f x)))
      
end

module DepTermApplicative = Applicative.Make(DepTermBasic)

let rec sub_terms ((s,a_opt) : 'a dep_term) : 'a dep_term suite =
  match s with
  | Emp -> singleton (Emp,a_opt)
  | Ext (s',a) ->
    let r = sub_terms (s',Some a) in
    Ext (r,(s,a_opt))

let rec sub_teles (tl : 'a tele) (ty : 'a) : ('a tele * 'a) suite =
  match tl with
  | Emp -> singleton (Emp,ty)
  | Ext (tl',(_,ty')) ->
    let rtl = sub_teles tl' ty' in
    Ext (rtl,(tl,ty))

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


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
    
(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let tele_fold_with_idx g l f =
  fold_accum_cont g l
    (fun (nm,ict,tm) l' ->
       ((nm,ict,f tm l') , l'+1))

let pp_tele pp_el ppf tl =
  pp_suite (Fmt.pair Fmt.string pp_el) ppf tl 

(*****************************************************************************)
(*                             Logging functions                             *)
(*****************************************************************************)

let log_msg ?idt:(i=0) (s : string) =
  let indt = String.make i ' ' in 
  Fmt.pr "@[<v>%s@,@]" (indt ^ s)
    
let log_val ?idt:(i=0) (s : string) (a : 'a) (pp : 'a Fmt.t) =
  let indt = String.make i ' ' in 
  Fmt.pr "@[<v>%s: @[%a@]@,@]" (indt ^ s) pp a

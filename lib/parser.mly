%{

    open Expr
    open Suite
    open Cmd
       
%} 

%token DEF NORMALIZE EXPAND IMPORT
%token LET COLON EQUAL IN
%token LAMBDA DOT VBAR VDASH
%token LPAR RPAR LBR RBR
%token ARROW 
%token TIMES COMMA FST SND
%token LBRKT RBRKT AT 
%token TYPE
%token LF ND UNIT
%token <string> IDENT
%token EOF

%start prog
%type <string list * Cmd.cmd list> prog

%%

suite(X):
  | { Emp }
  | s = suite(X) x = X
    { Ext (s,x) }

non_empty_suite(X,S):
  | x = X
    { Ext (Emp,x) }
  | s = non_empty_suite(X,S) S x = X
    { Ext (s,x) }

sep_suite(X,S):
  | { Emp }
  | x = X
    { Ext (Emp,x) }
  | s = sep_suite(X,S) S x = X
    { Ext (s,x) } 

tr_expr(V):
  | UNIT
    { UnitE }
  | LBR v = V RBR
    { ValueE v }
  | LF t = tr_expr(V)
    { LeafE t }
  | ND s = tr_expr(V) t = tr_expr(V)
    { NodeE (s,t) }
  | LPAR t = tr_expr(V) RPAR
    { t } 

cmplx(X):
  | c = non_empty_suite(tr_expr(X),VBAR) 
    { c } 

prog:
  | EOF
    { ([],[]) }
  | imprts = list(import) defs = nonempty_list(cmd) EOF
    { (imprts, defs) }

import:
  | IMPORT nm = IDENT
    { nm } 

cmd:
  | DEF id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { Define (id,tl,ty,tm) }
  | NORMALIZE tl = tele COLON ty = expr VDASH tm = expr
    { Normalize (tl,ty,tm) } 
  | EXPAND tl = tele COLON ty = expr VBAR tm = expr VBAR c = cmplx(IDENT)
    { Expand (tl,ty,tm,c) } 

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,ty) }

tele:
  | tl = suite(var_decl)
    { tl } 

pi_head:
  | v = var_decl
    { v }
  | e = expr2
    { ("",e) }

expr: 
  | e = expr1
    { e }
  | u = expr1 COMMA v = expr
    { PairE (u,v) } 
  | LET id = IDENT COLON ty = expr EQUAL tm = expr IN bdy = expr
    { LetE (id,ty,tm,bdy) }

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,e) }
  | hd = pi_head ARROW cod = expr1
    { let (nm,dom) = hd in PiE (nm,dom,cod) }
  | hd = pi_head TIMES cod = expr1
    { let (nm,dom) = hd in SigE (nm,dom,cod) } 


expr2:
  | e = expr3
    { e }
  | u = expr2 v = expr3
    { AppE (u,v) }

expr3:
  | TYPE
    { TypE }
  | id = IDENT
    { VarE id }

  | FST e = expr3
    { FstE e }
  | SND e = expr3
    { SndE e }

  | LBRKT e = expr AT pi = cmplx(IDENT) RBRKT
    { ReflE (e,pi) } 

  | LPAR t = expr RPAR
    { t }



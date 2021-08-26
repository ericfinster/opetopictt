%{

    open Expr
    open Suite
    open Syntax
    open Cmd
       
%} 

%token LET LAMBDA COLON EQUAL DOT
%token LPAR RPAR LBR RBR 
%token ARROW HOLE 
%token TYPE
%token LF ND UNIT
%token LBRKT RBRKT VBAR
%token FRM 
%token <string> IDENT
%token EOF

%start prog
%type <Cmd.cmd list> prog

%%

suite(X):
  | { Emp }
  | s = suite(X) x = X
    { Ext (s,x) }

sep_suite(X,S):
  | { Emp }
  | s = sep_suite(X,S) S x = X
    { Ext (s,x) }

non_empty_suite(X,S):
  | x = X
    { Ext (Emp,x) }
  | s = non_empty_suite(X,S) S x = X
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

prog:
  | EOF
    { [] }
  | defs = nonempty_list(cmd) EOF
    { defs }

cmd:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { Let (id,tl,ty,tm) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,Expl,ty) }
  | LBR id = IDENT COLON ty = expr RBR
    { (id,Impl,ty) }

tele:
  | tl = suite(var_decl)
    { tl } 

pi_head:
  | v = var_decl
    { v }
  | e = expr2
    { ("",Expl,e) }

cmplx:
  | LBRKT c = non_empty_suite(tr_expr(UNIT),VBAR) RBRKT
    { c } 

expr: 
  | e = expr1
    { e }

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,Expl,e) }
  | LAMBDA LBR id = IDENT RBR DOT e = expr1
    { LamE (id,Impl,e) }
  | hd = pi_head ARROW cod = expr1
    { let (nm,ict,dom) = hd in PiE (nm,ict,dom,cod) }

expr2:
  | e = expr3
    { e }
  | u = expr2 LBR v = expr2 RBR
    { AppE (u,v,Impl) }
  | u = expr2 v = expr3
    { AppE (u,v,Expl) }

expr3:
  | TYPE
    { TypE }
  | HOLE
    { HoleE } 
  | id = IDENT
    { VarE id }
  | FRM c = cmplx
    { FrmE c } 
  | LPAR t = expr RPAR
    { t }


%{

    open Expr
    open Suite
    open Cmd
       
%} 

%token LET LAMBDA COLON EQUAL DOT VBAR
%token LPAR RPAR LBR RBR LBRKT RBRKT
%token ARROW VDASH EMPTY SEMI
%token COMP FILL KANELIM 
%token TYPE
%token LF ND UNIT
%token <string> IDENT
%token EOF

%start prog
%type <Cmd.cmd list> prog

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
    { [] }
  | defs = nonempty_list(cmd) EOF
    { defs }

cmd:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { Let (id,tl,ty,tm) }

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

/* dir: */
/*   | a = addr */
/*     { Dir a } */

/* addr: */
/*   | LBRKT ds = separated_list(COMMA,dir) RBRKT */
/*     { ds }  */

dep_term:
  | s = sep_suite(expr,SEMI) VDASH e = expr
    { (s,Some e) }
  | s = sep_suite(expr,SEMI) VDASH EMPTY
    { (s,None) }

expr: 
  | e = expr1
    { e }

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,e) }
  | hd = pi_head ARROW cod = expr1
    { let (nm,dom) = hd in PiE (nm,dom,cod) }

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
  | LBRKT t = tele VDASH e = expr VBAR c = cmplx(dep_term) RBRKT
    { CellE (t,e,c) }
  | COMP LBRKT t = tele VDASH e = expr VBAR c = cmplx(dep_term) RBRKT
    { CompE (t,e,c) } 
  | FILL LBRKT t = tele VDASH e = expr VBAR c = cmplx(dep_term) RBRKT
    { FillE (t,e,c) }
  | KANELIM LBRKT tl = tele VDASH ty = expr VBAR c = cmplx(dep_term) RBRKT
      p = expr3 d = expr3 comp = expr3 fill = expr3
    { KanElimE (tl,ty,c,p,d,comp,fill) } 
  | LPAR t = expr RPAR
    { t }


%{

    open Expr
    open Cmd 
    open Suite
       
%} 

%token LET LAMBDA COLON EQUAL DOT
%token LPAR RPAR 
%token TYPE ARROW 
%token POS EL ARROWPOS TIMESPOS
%token COMMA SUM UNITPOS EMPTYPOS
%token TTPOS INLPOS INRPOS LAMBDAPOS
%token APPPOS TOPELIM BOTELIM
%token SUMELIM SIGELIM
%token NORMALIZE INFER VBAR
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

prog:
  | EOF
    { [] }
  | defs = nonempty_list(cmd) EOF
    { defs }

cmd:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { Let (id,tl,ty,tm) }
  | NORMALIZE tl = tele COLON ty = expr VBAR tm = expr
    { Normalize (tl,ty,tm) }
  | INFER tl = tele VBAR tm = expr
    { Infer (tl,tm) } 

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
  | e = expr1 COMMA f = expr
    { PosPairE (e,f) }
  | e = expr2 SUM f = expr
    { PosSumE (e,f) } 

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id,e) }
  | LAMBDAPOS id = IDENT DOT e = expr1
    { PosLamE (id,e) } 
  | hd = pi_head ARROW cod = expr1
    { let (nm,dom) = hd in PiE (nm,dom,cod) }
  | hd = pi_head ARROWPOS cod = expr1
    { let (nm,dom) = hd in PosPiE (nm,dom,cod) }
  | hd = pi_head TIMESPOS cod = expr1
    { let (nm,dom) = hd in PosSigE (nm,dom,cod) }

expr2:
  | e = expr3
    { e }
  | u = expr2 v = expr3
    { AppE (u,v) }
  | u = expr2 APPPOS v = expr3
    { PosAppE (u,v) } 

expr3:
  | TYPE
    { TypE }
  | POS
    { PosE }
  | UNITPOS
    { PosUnitE }
  | EMPTYPOS
    { PosEmptyE }
  | TTPOS
    { PosTtE } 
  | EL e = expr3
    { ElE e }
  | INLPOS e = expr3
    { PosInlE e }
  | INRPOS e = expr3
    { PosInrE e }
  | BOTELIM
    { PosBotElimE }
  | TOPELIM e = expr3
    { PosTopElimE e } 
  | SUMELIM e = expr3 f = expr3
    { PosSumElimE (e, f) }
  | SIGELIM e = expr3
    { PosSigElimE e }

  | id = IDENT
    { VarE id }
  | LPAR t = expr RPAR
    { t }


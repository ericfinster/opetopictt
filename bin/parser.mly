%{

    open Syntax
    open Suite
       
%} 

%token LET
%token TYPE 
%token LAMBDA COLON EQUAL DOT
%token LPAR RPAR
%token ARROW HOLE
%token <string> IDENT 
%token EOF

%start prog
%type <Syntax.defn list> prog

%%

prog:
  | EOF
    { [] }
  | defs = nonempty_list(defn) EOF
    { defs }

defn:
  | LET id = IDENT tl = tele COLON ty = expr EQUAL tm = expr
    { Def (id,tl,ty,tm) }

tele:
  |
    { Emp }
  | t = tele v = var_decl
    { Ext (t, v) }

var_decl:
  | LPAR id = IDENT COLON ty = expr RPAR
    { (id,ty) }

expr: 
  | e = expr1
    { e }

expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { LamE (id, e) }
  | LPAR id = IDENT COLON ty = expr1 RPAR ARROW tm = expr1
    { PiE (id,ty,tm) } 

expr2:
  | t = expr3
    { t }
  | u = expr2 v = expr3
    { AppE (u,v) }

expr3:
  | TYPE
    { TypE }
  | HOLE
    { HoleE } 
  | id = IDENT
    { VarE id }
  | LPAR t = expr RPAR
    { t }


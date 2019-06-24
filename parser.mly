%{

    open Syntax

%} 

%token TYPE FST SND
%token <string> IDENT 
%token LET DEF EQUAL
%token LPAR RPAR
%token COLON ARROW STAR
%token LAMBDA DOT COMMA
%token EOF

%start prog
%type < Syntax.cmd list > prog

%%

prog:
  | EOF
    { [] }
  | cmds = nonempty_list(cmd) EOF
    { cmds }

cmd:
  | DEF id = IDENT COLON ty = expr EQUAL tm = expr
    { Def (id , ty , tm) }

expr:
  | e = expr1
    { e }
  | e1 = expr1 COMMA e2 = expr
    { EPair (e1, e2) }
  
expr1:
  | e = expr2
    { e }
  | LAMBDA id = IDENT DOT e = expr1
    { ELam (id , e) }
  | LPAR id = IDENT COLON ty = expr1 RPAR ARROW tm = expr1
    { EPi (id , ty , tm) }
  | LPAR id = IDENT COLON ty = expr1 RPAR STAR tm = expr1
    { ESig (id , ty , tm) }

expr2:
  | e = expr3
    { e }
  | e1 = expr2 e2 = expr3
    { EApp (e1 , e2) }

expr3:
  | TYPE
    { EType }
  | id = IDENT
    { EVar id }
  | FST e = expr3
    { EFst e }
  | SND e = expr3
    { ESnd e }
  | LPAR e = expr RPAR
    { e }
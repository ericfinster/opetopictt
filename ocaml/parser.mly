%{

    open Syntax

%} 

%token TYPE OTYPE
%token FRAME CELL TREE
%token POS TYP INH
%token MU ETA GAMMA ND LF OB 
%token FRMEMPTY FRMEXT FRMHD
%token OBPOSELIM LFPOSELIM NDPOSELIM
%token ETAPOSELIM MUPOSFST MUPOSSND
%token GAMMAPOSELIM
%token OBPOS NDPOSHERE NDPOSTHERE
%token MUPOS ETAPOS
%token GAMMAPOSINL GAMMAPOSINR
%token FST SND
%token LET DEF EQUAL
%token LPAR RPAR
%token COLON ARROW STAR
%token LAMBDA DOT COMMA
%token <string> IDENT 
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
  | f = frm
    { f }
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
  | OTYPE
    { EOType }
    
  | FRAME x = expr3
    { EFrm x }
  | CELL x = expr3 f = expr3
    { ECell (x, f) }
  | TREE x = expr3 f = expr3
    { ETree (x , f) }
  | POS x = expr3 f = expr3 s = expr3
    { EPos (x, f, s) }
  | TYP x = expr3 f = expr3 s = expr3 p = expr3
    { ETyp (x, f, s, p) }
  | INH x = expr3 f = expr3 s = expr3 p = expr3
    { EInh (x, f, s, p) }

  | MU x = expr3 f = expr3 s = expr3 k = expr3
    { EMu (x, f, s, k) }
  | ETA x = expr3 f = expr3 a = expr3
    { EEta (x, f, a) }
  | GAMMA x = expr3 f = expr3 s = expr3 t = expr3 r = expr3 phi = expr3 psi = expr3
    { EGamma (x, f, s, t, r, phi, psi) }
  | ND x = expr3 f = expr3 s = expr3 t = expr3 a = expr3 d = expr3 e = expr3
    { ENd (x, f, s, t, a, d, e) }
  | LF x = expr3 f = expr3 a = expr3
    { ELf (x, f, a) }
  | OB x = expr3 a = expr3
    { EOb (x, a) }

  | OBPOS x = expr3 a = expr3
    { EObPos (x, a) }
  | NDPOSHERE x = expr3 f = expr3 s = expr3 t = expr3 a = expr3 d = expr3 e = expr3
    { ENdHere (x, f, s, t, a, d, e) }
  | NDPOSTHERE x = expr3 f = expr3 s = expr3 t = expr3 a = expr3 d = expr3 e = expr3 p = expr3 q = expr3
    { ENdThere (x, f, s, t, a, d, e, p, q) }
  | MUPOS x = expr3 f = expr3 s = expr3 k = expr3 p = expr3 q = expr3
    { EMuPos (x, f, s, k, p, q) }
  | ETAPOS x = expr3 f = expr3 a = expr3
    { EEtaPos (x, f, a) }
  | GAMMAPOSINL x = expr3 f = expr3 s = expr3 t = expr3 r = expr3 phi = expr3 psi = expr3 p = expr3
    { EGammaInl (x, f, s, t, r, phi, psi, p) }
  | GAMMAPOSINR x = expr3 f = expr3 s = expr3 t = expr3 r = expr3 phi = expr3 psi = expr3 p = expr3 q = expr3
    { EGammaInr (x, f, s, t, r, phi, psi, p, q) }
    
  | OBPOSELIM x = expr3 a = expr3 w = expr3 c = expr3 p = expr3
    { EObPosElim (x, a, w, c, p) }
  | LFPOSELIM x = expr3 f = expr3 a = expr3 w = expr3 p = expr3
    { ELfPosElim (x, f, a, w, p) }
  | NDPOSELIM x = expr3 f = expr3 s = expr3 t = expr3 a = expr3 d = expr3 e = expr3 w = expr3 h = expr3 th = expr3 p = expr3
    { ENdPosElim (x, f, s, t, a, d, e, w, h, th, p) }
  | ETAPOSELIM x = expr3 f = expr3 a = expr3 w = expr3 n = expr3 p = expr3
    { EEtaPosElim (x, f, a, w, n, p) }
  | MUPOSFST x = expr3 f = expr3 s = expr3 k = expr3 p = expr3
    { EMuPosFst (x, f, s, k, p) }
  | MUPOSSND x = expr3 f = expr3 s = expr3 k = expr3 p = expr3
    { EMuPosSnd (x, f, s, k, p) }
  | GAMMAPOSELIM x = expr3 f = expr3 s = expr3 t = expr3 r = expr3 phi = expr3 psi = expr3 w = expr3 il = expr3 ir = expr3 p = expr3
    { EGammaPosElim (x, f, s, t, r, phi, psi, w, il, ir, p) }

  | id = IDENT
    { EVar id }
  | FST e = expr3
    { EFst e }
  | SND e = expr3
    { ESnd e }
  | LPAR e = expr RPAR
    { e }

frm:
  | FRMEMPTY
    { EFrmEmpty }
  | f = frm FRMEXT s = expr3 FRMHD t = expr3
    { EFrmExt (f, s, t) } 


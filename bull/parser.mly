%{open Utils

  let foo x f = let (l,t) = x in f l t
  let foo2 x y f = foo y (foo x f)
  let foo3 x y z f = foo z (foo2 x y f)

  let fun0 f = (Locnode(Parsing.symbol_start_pos(), Parsing.symbol_end_pos (), []), f)
  let fun1 f x = foo x (fun l1 t1 -> (Locnode(Parsing.symbol_start_pos(), Parsing.symbol_end_pos (), [l1]), f t1))
  let fun2 f x y = foo2 x y (fun l1 t1 l2 t2 -> (Locnode(Parsing.symbol_start_pos(), Parsing.symbol_end_pos (), [l1; l2]), f t1 t2))
  let fun3 f x y z = foo3 x y z (fun l1 t1 l2 t2 l3 t3 -> (Locnode(Parsing.symbol_start_pos(), Parsing.symbol_end_pos (), [l1; l2; l3]), f t1 t2 t3))
%}

%token OPENP
%token CLOSP
%token LT
%token GT
%token LAMBDA
%token ENDLAMBDA
%token DOT
%token COMMA
%token COLON
%token ASSIGN
%token SEMICOLON
%token ARROW
%token SAND
%token SOR
%token OMEGA
%token SMATCH
%token RETURN
%token WITH
%token PI
%token SUBSET
%token LAMBDAR
%token INJLEFT
%token INJRIGHT
%token PROJLEFT
%token PROJRIGHT
%token QUIT
%token LOAD
%token LEMMA
%token TYPE
%token AXIOM
%token DEFINITION
%token COMPUTE
%token PRINT
%token SIG
%token HELP
%token <string> ID
%token EOF

%start s
%type <Utils.sentence> s

%%

s:
    | QUIT DOT { Quit }
    | LOAD ID DOT { Load $2 }
    | LEMMA ID COLON term DOT { foo $4 (fun l t -> Proof ($2, l, t)) }
    | AXIOM ID COLON term DOT { foo $4 (fun l t -> Axiom ($2, l, t)) }
    | DEFINITION ID COLON term ASSIGN term
		 DOT { foo2 $4 $6 (fun l1 t1 l2 t2 -> Definition ($2, l1, t1, Some(l2,t2))) }
    | DEFINITION ID ASSIGN term DOT { foo $4 (fun l t -> Definition ($2, l, t, None)) }
    | PRINT ID DOT { Print $2 }
    | SIG DOT { Print_all }
    | COMPUTE ID DOT { Compute $2 }
    | HELP DOT { Help }
    | error DOT { Error }
    | EOF { Quit }
    ;

      /* I had to manage the precedence of operators the hard way, because I couldn't manage the precedence of the "application operator" (which does not exist, haha) automatically */

term:
    | PI ID COLON term COMMA
	     term
	     { fun2 (fun t1 t2 -> Prod ($2, t1, t2)) $4 $6 }
    | SUBSET ID COLON term COMMA
	     term
	     { fun2 (fun t1 t2 -> Subset ($2, t1, t2)) $4 $6 }
    | LAMBDA ID COLON term ENDLAMBDA
	     term
	     { fun2 (fun t1 t2 -> Abs ($2, t1, t2)) $4 $6 }
    | LAMBDAR ID COLON term ENDLAMBDA
	     term
	     { fun2 (fun t1 t2 -> Subabs ($2, t1, t2)) $4 $6 }
    | term2 { $1 }
    ;

term2:
    | term3 ARROW term2 { fun2 (fun t1 t2 -> Prod("", t1, t2)) $1 $3 } /* arrow is right-to-left */
    | term3 { $1 }
    ;

term3:
    | term4 SOR term3 { fun2 (fun t1 t2 -> Union(t1, t2)) $1 $3 } /* union is right-to-left */
    | term4 { $1 }
    ;

term4:
    | term5 SAND term4 { fun2 (fun t1 t2 -> Inter(t1, t2)) $1 $3 } /* inter is right-to-left */
    | term5 { $1 }
    ;

term5:
    | term5 term6 { fun2 (fun t1 t2 -> App (t1, t2)) $1 $2 } /* applications are left-
      to-right */
    | term6 { $1 }
    ;

term6:
    | PROJLEFT term6 { fun1 (fun t1 -> SPrLeft (t1)) $2 }
    | PROJRIGHT term6 { fun1 (fun t1 -> SPrRight (t1)) $2 }
    | INJLEFT term6 term6 { fun2 (fun t1 t2 -> SInLeft (t1, t2)) $2 $3 }
    | INJRIGHT term6 term6 { fun2 (fun t1 t2 -> SInRight (t1, t2)) $2 $3 }
    | term7 { $1 }
    ;

term7:
    | OPENP term CLOSP { $2 } /* highest precedence */
    | ID { fun0 (Const $1) }
    | OMEGA { fun0 Omega }
    | TYPE { fun0 (Sort Type) }
    | LT term COMMA term GT { fun2 (fun t1 t2 -> SPair (t1, t2)) $2 $4 }
    | RETURN term WITH LT term COMMA term
	     GT { fun3 (fun t1 t2 t3 -> SMatch (t1, t2, t3)) $2 $5 $7 }
    ;

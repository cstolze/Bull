%{open Utils%}

%token OPENP
%token CLOSP
%token LAMBDA
%token DOT
%token COMMA
%token COLON
%token EQUAL
%token SEMICOLON
%token ARROW
%token SOR
%token SAND
%token VAR
%token INTRO
%token ELIM
%token SCONJ
%token PROJLEFT
%token PROJRIGHT
%token INJLEFT
%token INJRIGHT
%token SDISJ
%token BACKTRACK
%token CHANGERULE
%token ABORT
%token QUIT
%token LOAD
%token PROOF
%token TYPE
%token CONSTANT
%token LT
%token GT
%token SHARP
%token DELTATERM
%token PRINT
%token SIG
%token HELP
%token <string> ID
		%token EOF

		%right ARROW
		%right SOR
		%right SAND

		%start proof
		%type <Utils.proofrule> proof

%start s
%type <Utils.sentence> s

			     %%

			       s:
    | QUIT SEMICOLON { Quit }
    | LOAD ID SEMICOLON { Load $2 }
    | PROOF ID COLON family SEMICOLON { Proof ($2, $4) }
    | TYPE ID COLON kind SEMICOLON { Typecst ($2, $4) }
    | CONSTANT ID COLON family SEMICOLON { Cst ($2, $4) }
    | DELTATERM ID EQUAL deltaterm COLON family SEMICOLON { Typecheck ($2, $4, $6) }
    | DELTATERM ID EQUAL deltaterm SEMICOLON { Typeinfer ($2, $4) }
    | PRINT ID SEMICOLON { Print $2 }
    | SIG SEMICOLON { Print_all }
    | HELP SEMICOLON { Help }
    | error SEMICOLON { Error }
    | EOF { Quit }
    ;

      kind:
    | OPENP kind CLOSP { $2 }
    | TYPE { Type }
    ;

      family:
    | ID { SAtom $1 }
    | OPENP family CLOSP { $2 }
    | family ARROW family { SFc ($1, $3) }
    | family SAND family { SAnd ($1, $3) }
    | family SOR family { SOr ($1, $3) }
    ;

      /* I had to manage the precedence of operators the hard way, because I couldn't manage the precedence of the "application operator" (which does not exist, haha) automatically */
      deltaterm:
    | LAMBDA ID COLON family DOT deltaterm { DLambda ($2, $4, $6) } /* lowest precedence */
    | deltaterm2 { $1 }

	deltaterm2:
    | deltaterm2 deltaterm3 { DApp ($1, $2) } /* applications are left-to-right */
    | deltaterm3 { $1 }

		 deltaterm3:
    | PROJLEFT deltaterm3 { DProjL $2 }
    | PROJRIGHT deltaterm3 { DProjR $2 }
    | INJLEFT deltaterm3 { DInjL $2 }
    | INJRIGHT deltaterm3 { DInjR $2 }
    | deltaterm4 { $1 }

	deltaterm4:
    | OPENP deltaterm CLOSP { $2 } /* highest precedence */
    | ID { DVar $1 }
    | LT deltaterm SAND deltaterm GT { DAnd ($2, $4) }
    | LT LAMBDA ID COLON family DOT deltaterm SOR LAMBDA ID COLON family DOT deltaterm SHARP deltaterm GT { DOr ($3, $5, $7, $10, $12, $14, $16) }
    ;

      proof:
    | VAR SEMICOLON { PVar }
    | ABORT SEMICOLON { PAbort }
    | INTRO SEMICOLON { PIntro }
    | ELIM family SEMICOLON { PElim $2 }
    | SCONJ SEMICOLON { PSconj }
    | PROJLEFT family SEMICOLON { PProjL $2 }
    | PROJRIGHT family SEMICOLON { PProjR $2 }
    | INJLEFT SEMICOLON { PInjL }
    | INJRIGHT SEMICOLON { PInjR }
    | SDISJ family COMMA family SEMICOLON { PSdisj ($2, $4) }
    | BACKTRACK SEMICOLON { PBacktrack }
    | CHANGERULE SEMICOLON { PChangerule }
    | error SEMICOLON { PError }
    ;

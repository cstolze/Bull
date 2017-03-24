%{open Utils%}

%token OPENP
%token CLOSP
%token LAMBDA
%token DOT
%token COMMA
%token COLON
%token STAR
%token OMEGA
%token PI
%token EQUAL
%token SEMICOLON
%token ARROW
%token SOR
%token SAND
%token SCONJ
%token INTRO
%token EXACT
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
%token COMPUTE
%token LT
%token GT
%token SHARP
%token DELTATERM
%token PRINT
%token SIG
%token HELP
%token <string> ID
		%token EOF

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
    | COMPUTE ID SEMICOLON { Compute $2 }
    | HELP SEMICOLON { Help }
    | error SEMICOLON { Error }
    | EOF { Quit }
    ;

      kind:
    | OPENP kind CLOSP { $2 }
    | TYPE { Type }
    | PI ID COLON family DOT kind { KProd ($2, $4, $6) }
    ;

      family:
    | PI ID COLON family DOT family { SProd ($2, $4, $6) } /* lowest precedence */
    | LAMBDA ID COLON family DOT family { SLambda ($2, $4, $6) }
    | family2 { $1 }

	family2:
    | family3 ARROW family2 { SFc ($1, $3) } /* arrow is right-to-left */
    | family3 { $1 }

	family3:
    | family4 SOR family3 { SOr ($1, $3) } /* sor is right-to-left */
    | family4 { $1 }

	family4:
    | family5 SAND family4 { SAnd ($1, $3) } /* sand is right-to-left */
    | family5 { $1 }

	family5:
    | family5 deltaterm3 { SApp ($1, $2) } /* highest precedence */ /* we choose deltaterm3 because it is like a deltaterm application, ie the deltaterm2 rule */
    | ID { SAtom $1 }
    | OMEGA { SOmega }
    | OPENP family CLOSP { $2 }
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
    | STAR { DStar }
    | LT deltaterm SAND deltaterm GT { DAnd ($2, $4) }
    | LT LAMBDA ID COLON family DOT deltaterm SOR LAMBDA ID COLON family DOT deltaterm SHARP deltaterm GT { DOr ($3, $5, $7, $10, $12, $14, $16) }
    ;

      proof:
    | ABORT SEMICOLON { PAbort }
    | BACKTRACK SEMICOLON { PBacktrack }
    | INTRO SEMICOLON { PAbst1 }
    | EXACT deltaterm SEMICOLON { PExact $2 }
    | INTRO ID SEMICOLON { PAbst2 $2 }
    | SCONJ SEMICOLON { PSConj }
    | SDISJ ID COMMA family COMMA family SEMICOLON { PSDisj ($2, family_to_bruijn ($4), family_to_bruijn ($6)) }
    | PROJLEFT family SEMICOLON { PProjL (family_to_bruijn $2) }
    | PROJRIGHT family SEMICOLON { PProjR (family_to_bruijn $2) }
    | INJLEFT SEMICOLON { PInjL }
    | INJRIGHT SEMICOLON { PInjR }
    | error SEMICOLON { PError }
    | EOF { PQuit }
    ;


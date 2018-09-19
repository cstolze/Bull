%{open Utils
  let get_loc () = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
  let unquote s = String.trim (String.map (fun c -> if c = '"' then ' '
						    else c) s)
  let to_spine t1 t2 =
    match t1 with
    | App (_, t, l) -> App (get_loc (), t, t2 :: l) (* args are from
  last to first *)
    | _ -> App(get_loc (), t1, [t2])

%}

%token OPENP
%token CLOSP
%token LT
%token GT
%token LAMBDA
%token ENDLAMBDA
%token LET
%token IN
%token DOT
%token COMMA
%token COLON
%token ASSIGN
%token SEMICOLON
%token ARROW
%token SAND
%token SOR
%token UNDERSCORE
%token SMATCH
%token RETURN
%token WITH
%token END
%token PI
%token SUBSET
%token COERCION
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
%token <string> QUOTE
%token <string> ID
%token EOF

%start s
%type <Utils.sentence list> s

%%

s:
    | QUIT DOT { [Quit] }
    | LOAD QUOTE DOT { [Load (unquote $2)] }
    | LEMMA ID COLON term DOT { [Proof ($2,$4)] }
    | AXIOM ID COLON term DOT { [Axiom ($2, $4)] }
    | DEFINITION ID COLON term ASSIGN term
		 DOT { [Definition ($2, $6, Some($4))] }
    | DEFINITION ID ASSIGN term DOT { [Definition ($2, $4, None)] }
    | PRINT ID DOT { [Print $2] }
    | SIG DOT { [Print_all] }
    | COMPUTE ID DOT { [Compute $2] }
    | HELP DOT { [Help] }
    | error { [Error] }
    | EOF { [Quit] }
    ;

      /* I had to manage the precedence of operators the hard way, because I couldn't manage the precedence of the "application operator" (which does not exist, haha) automatically */

term:
    | PI ID COLON term COMMA term
	     { Prod (get_loc (), $2, $4, $6) }
    | LAMBDA ID COLON term ENDLAMBDA
	     term
	     { Abs (get_loc (), $2, $4, $6) }
    | LET ID COLON term ASSIGN term IN term { Let (get_loc (), $2, $4, $6, $8) }
    | term2 { $1 }
    ;

term2:
    | term3 ARROW term2 { Prod (get_loc (), "_", $1, $3) } /* arrow is right-to-left */
    | term3 { $1 }
    ;

term3:
    | term4 SOR term3 { Union (get_loc (), $1, $3) } /* union is right-to-left */
    | term4 { $1 }
    ;

term4:
    | term5 SAND term4 { Inter (get_loc (), $1, $3) } /* inter is right-to-left */
    | term5 { $1 }
    ;

term5:
    | term5 term6 { to_spine $1 $2 } /* applications are left-
      to-right */
    | term6 { $1 }
    ;

term6:
    | COERCION term6 term6 { Coercion (get_loc (),$2, $3) }
    | PROJLEFT term6 { SPrLeft (get_loc (), $2) }
    | PROJRIGHT term6 { SPrRight (get_loc (), $2) }
    | INJLEFT term6 term6 { SInLeft (get_loc (), $2, $3) }
    | INJRIGHT term6 term6 { SInRight (get_loc (), $2, $3) }

    | OPENP term CLOSP { $2 } /* highest precedence */
    | ID { Const (get_loc (), $1) }
    | TYPE { Sort (get_loc (), Type) }
    | LT term COMMA term GT { SPair (get_loc (), $2, $4) }
    | SMATCH term RETURN term WITH ID COLON term ENDLAMBDA term COMMA ID COLON term ENDLAMBDA term END { SMatch (get_loc (), $2, $4, $6, $8, $10, $12, $14, $16) }
    ;

%{open Utils
  let get_loc () = (Parsing.symbol_start_pos (), Parsing.symbol_end_pos ())
  let unquote s = String.trim (String.map (fun c -> if c = '"' then ' '
						    else c) s)
  let to_spine t1 t2 =
    match t1 with
    | App (_, t, l) -> App (get_loc (), t, t2 :: l) (* args are from
  last to first *)
    | _ -> App(get_loc (), t1, [t2])

  let rec add_args l t =
    match l with
    | [] -> t
    | (id,t1) :: l -> Abs(dummy_loc, id, t1, add_args l t)

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
%token SHOW
%token <string> QUOTE
%token <string> ID
%token EOF

%token QUESTION
%token OPENB
%token CLOSB
%token META
%token ENDMETA
%token ADD
%token UNIFY
%token UNTYPED
%token TURNSTILE

%start s
%type <Utils.sentence list> s

%%

s:
    | QUIT DOT { [Quit] }
    | LOAD QUOTE DOT { [Load (unquote $2)] }
    | LEMMA ID COLON term DOT { [Proof($2,$4)] }
    | AXIOM decl_list DOT { List.map (fun (x,y) -> Axiom (x,y)) $2 }
    | DEFINITION ID pdl_opt COLON term ASSIGN term
		 DOT { [Definition ($2, add_args $3 $7, $5)] }
    | DEFINITION ID pdl_opt ASSIGN term DOT { [Definition ($2, add_args $3 $5, Underscore dummy_loc)] }
    | PRINT id_list DOT { List.map (fun x -> Print x) $2 }
    | SIG DOT { [Print_all] }
    | SHOW DOT { [Show] }
    | COMPUTE term DOT { [Compute $2] }
    | HELP DOT { [Help] }
    | error { [Error] }
    | EOF { [Quit] }

    /* For debugging purpose */
    | META DOT { [Beginmeta] }
    | ENDMETA DOT { [Endmeta] }
    | UNIFY term WITH term DOT { [Unify($2,$4)] }
    | ADD pdl_opt TURNSTILE term DOT { [Add ($2,$4)] }
    | AXIOM UNTYPED decl_list DOT { List.map (fun (x,y) -> UAxiom (x,y)) $3 }
    | DEFINITION UNTYPED ID pdl_opt COLON term ASSIGN term
		 DOT { [UDefinition ($3, add_args $4 $8, $6)] }
    ;

id_list :
  | ID {[$1]}
  | ID id_list {$1 :: $2}
  ;

decl :
  | id_list COLON term { List.map (fun x -> (x, $3)) $1 }
  ;

paren_decl_list:
  | OPENP decl CLOSP {$2}
  | OPENP decl CLOSP paren_decl_list {List.append $2 $4}
  ;

decl_list :
  | decl {$1}
  | paren_decl_list {$1}
  ;

paren_decl_list2:
  | OPENP decl CLOSP paren_decl_list2 {List.append $2 $4}
  ;

pdl_opt :
  | { [] }
  | ID pdl_opt {($1, Underscore (get_loc ())) :: $2}
  | OPENP decl CLOSP pdl_opt { List.append $2 $4 }
  ;

      /* I had to manage the precedence of operators the hard way, because I couldn't manage the precedence of the "application operator" (which does not exist, haha) automatically */

term:
    | PI ID COLON term COMMA term
	     { Prod (get_loc (), $2, $4, $6) }
    | PI ID COMMA term
             { Prod (get_loc (), $2, Underscore (get_loc ()), $4) }
    | LAMBDA ID COLON term ENDLAMBDA
	     term
	     { Abs (get_loc (), $2, $4, $6) }
    | LAMBDA ID ENDLAMBDA
             term
	     { Abs (get_loc (), $2, Underscore (get_loc ()), $4) }
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
    | term5 term6 { to_spine $1 $2 } /* applications are left-to-right */
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
    | UNDERSCORE { Underscore (get_loc ()) }
    | TYPE { Sort (get_loc (), Type) }
    | LT term COMMA term GT { SPair (get_loc (), $2, $4) }
    | SMATCH term RETURN term WITH ID COLON term ENDLAMBDA term COMMA ID COLON term ENDLAMBDA term END { SMatch (get_loc (), $2, $4, $6, $8, $10, $12, $14, $16) }
    | QUESTION ID OPENB tlist CLOSB { Meta(get_loc (), int_of_string $2, $4) }
    ;

tlist:
    | { [] }
    | term { [$1] }
    | term COMMA tlist { $1 :: $3 }

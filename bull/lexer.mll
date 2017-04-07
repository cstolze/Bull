{open Parser}

rule read = parse
        | [' ' '\t'] {read lexbuf}
        | [ '\n' ] { begin Lexing.new_line lexbuf; read lexbuf end }
	| '(' {OPENP}
	| ')' {CLOSP}
	| '<' {LT}
	| '>' {GT}
	| "let" {LET}
	| "in" {IN}
	| "fun" {LAMBDA}
	| "=>" {ENDLAMBDA}
	| '.' {DOT}
	| ',' {COMMA}
	| ":=" {ASSIGN}
	| ':' {COLON}
	| ';' {SEMICOLON}
	| "->" {ARROW}
	| '&' {SAND}
	| '|' {SOR}
	| '$' {OMEGA}
	| "smatch" {SMATCH}
	| "return" {RETURN}
	| "with" {WITH}
	| "forall" {PI}
	| "sforall" {SUBSET}
	| "sfun" {LAMBDAR}
	| "coe" {COERCION}
	| "inj_l" {INJLEFT}
	| "inj_r" {INJRIGHT}
	| "proj_l" {PROJLEFT}
	| "proj_r" {PROJRIGHT}
	| "Quit" {QUIT}
	| "Load" {LOAD}
	| "Lemma" {LEMMA}
	| "Type" {TYPE}
	| "Axiom" {AXIOM}
	| "Definition" {DEFINITION}
	| "Compute" {COMPUTE}
	| "Printall" {SIG}
	| "Print" {PRINT}
	| "Help" {HELP}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {ID x}
	| eof {EOF}

{open Parser}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| '<' {LT}
	| '>' {GT}
	| "fun" {LAMBDA}
	| "=>" {ENDLAMBDA}
	| '.' {DOT}
	| ',' {COMMA}
	| ":=" {ASSIGN}
	| ':' {COLON}
	| '=' {EQUAL}
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

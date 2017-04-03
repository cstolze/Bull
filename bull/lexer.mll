{open Parser}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| '<' {LT}
	| '>' {GT}
	| 'fun' {LAMBDA}
	| '.' {DOT}
	| ',' {COMMA}
	| ':' {COLON}
	| '=' {EQUAL}
	| ';' {SEMICOLON}
	| '#' {SHARP}
	| "->" {ARROW}
	| '&' {SAND}
	| '|' {SOR}
	| '*' {STAR}
	| '$' {OMEGA}
	| "forall" {PI}
	| "abort" {ABORT}
	| "backtrack" {BACKTRACK}
	| "intro" {INTRO}
	| "exact" {EXACT}
	| "inter" {SCONJ}
	| "inj_l" {INJLEFT}
	| "inj_r" {INJRIGHT}
	| "union" {SDISJ}
	| "proj_l" {PROJLEFT}
	| "proj_r" {PROJRIGHT}
	| "changerule" {CHANGERULE}
	| "Quit" {QUIT}
	| "Load" {LOAD}
	| "Proof" {PROOF}
	| "Type" {TYPE}
	| "Axiom" {AXIOM}
	| "Definition" {DELTATERM}
	| "Compute" {COMPUTE}
	| "Print" {PRINT}
	| "Print_all" {SIG}
	| "Help" {HELP}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {ID x}
	| eof {EOF}

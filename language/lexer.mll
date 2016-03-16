{open Parser}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| '\\' {LAMBDA}
	| '.' {DOT}
	| ',' {COMMA}
	| ':' {COLON}
	| '=' {EQUAL}
	| ';' {SEMICOLON}
	| "->" {ARROW}
	| "&" {SAND}
	| "|" {SOR}
	| "var" {VAR}
	| "intro" {INTRO}
	| "elim" {ELIM}
	| "sconj" {SCONJ}
	| "proj_l" {PROJLEFT}
	| "proj_r" {PROJRIGHT}
	| "inj_l" {INJLEFT}
	| "inj_r" {INJRIGHT}
	| "sdisj" {SDISJ}
	| "backtrack" {BACKTRACK}
	| "changerule" {CHANGERULE}
	| "abort" {ABORT}
	| "Quit" {QUIT}
	| "Load" {LOAD}
	| "Proof" {PROOF}
	| "Type" {TYPE}
	| "Constant" {CONSTANT}
	| "Definition" {DELTATERM}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {ID x}
	| eof {EOF}

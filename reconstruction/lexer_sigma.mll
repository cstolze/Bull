{open Parser_sigma}

rule read = parse
	| [' ' '\t' '\n'] {read lexbuf}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {VAR x}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "->" {FC}
	| '&' {AND}
	| "int" {INT}
	| eof {EOF}

{open Parser_sigma}

rule read = parse
	| [' ' '\t' '\n'] {read lexbuf}
	| "a" {A}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "->" {FC}
	| '&' {AND}
	| "int" {INT}
	| eof {EOF}

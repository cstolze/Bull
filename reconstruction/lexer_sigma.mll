{open Parser_sigma}

rule lecture = parse
	| [' ' '\t' '\n'] {lecture lexbuf}
	| "a" {A}
	| '(' {POUVR}
	| ')' {PFERM}
	| "->" {FC}
	| '&' {ET}
	| "int" {INT}
	| eof {EOF}

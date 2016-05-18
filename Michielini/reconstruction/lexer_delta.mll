{open Parser_delta}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "\\" {LAMBDA}
	| "." {AS}
	| ':' {COLON}
	| "=>" {AR}
	| "<=" {AL}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {VAR x}
	| "->" {FC}
	| "&" {AND}
	| eof {EOF}

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
	| ['a' - 'z']+ as x {VAR x}
	| "->" {FC}
	| "&" {AND}
	| eof {EOF}

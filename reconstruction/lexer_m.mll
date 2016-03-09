{open Parser_m}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "\\" {LAMBDA}
	| "." {AS}
	| ':' {COLON}
	| ['A' - 'Z' 'a' - 'z' '0' - '9' '_' '\'']+ as x {VAR x}
	| eof {EOF}

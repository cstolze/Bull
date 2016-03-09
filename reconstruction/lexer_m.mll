{open Parser_m}

rule read = parse
	| ['\n' ' ' '\t'] {read lexbuf}
	| '(' {OPENP}
	| ')' {CLOSP}
	| "\\" {LAMBDA}
	| "." {AS}
	| ':' {COLON}
	| ['a' - 'z']+ as x {VAR x}
	| eof {EOF}

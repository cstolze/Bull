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
	| ['0' - '9']+ as s {let i = int_of_string s in INT i}
	| "a" {A}
	| " -> " {FC}
	| " & " {AND}
	| eof {EOF}

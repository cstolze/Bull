{open Parser_delta}

rule lecture = parse
	| ['\n' '\t'] {lecture lexbuf}
	| '(' {POUVR}
	| ')' {PFERM}
	| "\\" {LAMBDA}
	| ". " {AS}
	| ' ' {AP}
	| ':' {PRES} 
	| "=>" {ED}
	| "<=" {EG}
	| ['0' - '9']+ as s {let i = int_of_string s in INT i}
	| "a" {A}
	| " -> " {FC}
	| " & " {ET}
	| eof {EOF}


rule get = parse
   | [' ' '\t' '\n'] { get lexbuf }
   | [^'.']* '.' { Lexing.lexeme lexbuf }
   | eof { "" }

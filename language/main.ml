(*
    <one line to give the program's name and a brief idea of what it does.> :-D
    Copyright (C) 2016 Claude Stolze

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *)

open Utils

let usage = "Usage: ./main.native [-v] [FILE]\n"

let version _ = print_string "<program>  Copyright (C) 2016  Claude Stolze\nLicense GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.\nThis is free software: you are free to change and redistribute it.\nThere is NO WARRANTY, to the extent permitted by law.\n"

let versiondoc = "output version information and exit\n"

let arg_file arg = print_string ("loading " ^ arg ^ " not implemented yet\n")

let options = ("-v", Arg.Unit (version), versiondoc) :: []

let main =
  let lx = Lexing.from_channel stdin in
  let ps = Parser.s Lexer.read lx in
  begin
    Arg.parse options arg_file usage;
    match ps with
    | Quit -> print_string "Quit.\n"
    | Load id -> print_string ("Load " ^ id ^ ".\n")
    | Proof (id, f) -> print_string "Proof.\n"
    | Typecst (id, k) -> print_string "Type.\n"
    | Cst (id, f) -> print_string "Constant.\n"
    | Typecheck (id, d, f) -> print_string "Typecheck.\n"
    | Typeinfer (id, d) -> print_string "Typeinfer.\n"
    | Error -> print_string "Error.\n"
  end
;;

main

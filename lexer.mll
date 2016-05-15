{
open Parser
open Syntax
exception Eof
}
rule token = parse
       [' ']			 { token lexbuf }
     | '\n'			 { EOL }
     | "=>" | "->"	     	 { IMPL }
     | "\\/"		     	 { OR }
     | "/\\"			 { AND }
     | '('			 { LPAREN }
     | ')'			 { RPAREN }
     | ','			 { COMMA }
     | ';'			 { SEMICOLON }
     | "_|_"                     { BOTTOM }
     | "not" | '!' | '~'         { NOT }
     | "forall"                  { FORALL }
     | "exists"                  { EXISTS }
     | "|-"                      { THESIS }
     | "axiom"                   { AXIOM }
     | "impl_i"                  { IMPLI }
     | "impl_e"                  { IMPLE }
     | "and_i"                   { ANDI }
     | "and_e_l"                 { ANDEL }
     | "and_e_r"                 { ANDER }
     | "or_i_l"                  { ORIL }
     | "or_i_r"                  { ORIR }
     | "or_e"                    { ORE }
     | "not_i"                   { NOTI }
     | "not_e"                   { NOTE }
     | "absurd"                  { ABSURD }
     | "forall_i"                { FORALLI }
     | "forall_e"                { FORALLE }
     | "exists_i"                { EXISTSI }
     | "exists_e"                { EXISTSE }
     | "prove"                   { PROVE }
     | "export"                  { EXPORT }
     | "list"                    { LISTENV }
     | ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9']* as lxm { MINNAME lxm }
     | ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9']* as lxm { MAJNAME lxm }
     | eof			 { raise Eof }

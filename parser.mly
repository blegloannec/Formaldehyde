%{
open Syntax
%}
%token <string> MINNAME
%token <string> MAJNAME
%token NOT OR AND IMPL
%token FORALL EXISTS BOTTOM
%token LPAREN RPAREN COMMA SEMICOLON THESIS
%token AXIOM IMPLI IMPLE ANDI ANDEL ANDER
%token ORIL ORIR ORE NOTI NOTE ABSURD
%token FORALLI FORALLE EXISTSI EXISTSE
%token PROVE
%token EOL
%right IMPL
%right OR
%right AND
%nonassoc NOT
%start main
%type <Syntax.command> main
%type <Syntax.term> term
%type <Syntax.term list> term_list
%type <Syntax.formula> form
%type <Syntax.formula list> form_list
%type <Syntax.sequent> sequent
%type <Syntax.command> command
%%
main:
    command EOL	      { $1 }
;
term:
     MINNAME				{ Var $1 }
   | MAJNAME LPAREN term_list RPAREN	{ Func ($1,$3) }
   | MAJNAME                    	{ Func ($1,[]) }
;
term_list:
                                { [] }
  | term    			{ [$1] }
  | term COMMA term_list	{ $1::$3 }
;
form:
    MAJNAME LPAREN term_list RPAREN	{ Pred ($1,$3) }
  | MAJNAME                     	{ Pred ($1,[]) }
  | BOTTOM                              { Bot }
  | form OR form                        { Or ($1,$3) }
  | form AND form                       { And ($1,$3) }
  | form IMPL form                      { Impl ($1,$3) }
  | NOT form                            { Not $2 }
  | FORALL MINNAME COMMA form           { Forall ($2,$4) }
  | EXISTS MINNAME COMMA form           { Exists ($2,$4) }
  | LPAREN form RPAREN                  { $2 }
;
form_list:
                              { [] }
  | form                      { [$1] }
  | form SEMICOLON form_list  { $1::$3 }
;
sequent:
    form_list THESIS form        { ($1,$3) }
;
command:
    AXIOM             { Axiom }
  | IMPLI             { Impl_i }
  | IMPLE form        { Impl_e $2 }
  | ANDI              { And_i }
  | ANDEL form        { And_e_l $2 }
  | ANDER form        { And_e_r $2 }
  | ORIL              { Or_i_l }
  | ORIR              { Or_i_r }
  | ORE form form     { Or_e ($2,$3) }
  | NOTI              { Not_i }
  | NOTE form         { Not_e $2 }
  | ABSURD            { Absurd }
  | FORALLI           { Forall_i }
  | FORALLE term      { Forall_e $2 }
  | EXISTSI term      { Exists_i $2 }
  | EXISTSE form      { Exists_e $2 }
  | PROVE sequent     { Prove $2 }
;

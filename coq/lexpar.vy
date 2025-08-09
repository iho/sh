%{
Require Import FullAst.
Require Import String.
Require Import List.
Import ListNotations.
%}

%token <string> WORD ASSIGNMENT_WORD NAME  
%token <nat> IO_NUMBER
%token AND_IF OR_IF DSEMI DLESS DGREAT LESSAND GREATAND LESSGREAT DLESSDASH CLOBBER
%token LESS GREAT PIPE AMP SEMI NEWLINE EOF_TOK BANG LPAREN RPAREN LBRACE RBRACE
%token IF_TOK THEN_TOK ELSE_TOK ELIF_TOK FI_TOK DO_TOK DONE_TOK CASE_TOK ESAC_TOK WHILE_TOK UNTIL_TOK FOR_TOK IN_TOK

%start <FullAst.exp> program
%type <FullAst.exp> list
%type <FullAst.exp> and_or
%type <FullAst.exp> command
%type <FullAst.exp> compound
%type <FullAst.exp> subshell
%type <FullAst.exp> for_clause
%type <FullAst.exp> case_clause
%type <FullAst.exp> if_clause
%type <FullAst.exp> while_clause
%type <FullAst.exp> until_clause
%type <FullAst.exp> function_def
%type <FullAst.exp> function_body
%type <FullAst.exp> brace_group
%type <list FullAst.exp> clist
%type <list FullAst.exp> term
%type <list FullAst.exp> do_group
%type <list FullAst.exp> pipe_sequence
%type <list string> wlist
%type <list string> pattern
%type <option (string * list string)> scmd
%type <list FullAst.exp> rlist
%type <FullAst.exp> io_redirect
%type <FullAst.sep> separator
%type <list FullAst.exp> prefix
%type <list FullAst.exp> suffix
%type <list (list string * list FullAst.exp)> case_list
%type <list string * list FullAst.exp> case_item
%type <list (list FullAst.exp * list FullAst.exp)> else_part

%%

program:       | list                              { $1 }

list:          | list separator and_or             { List $1 $2 $3 }
               | and_or                            { $1 }

and_or:        | pipe_sequence                     { Pipeline false $1 }
               | BANG pipe_sequence                { Pipeline true $2 }
               | and_or AND_IF and_or              { AndIf $1 $3 }
               | and_or OR_IF and_or               { OrIf $1 $3 }

pipe_sequence: | command                           { [$1] }
               | pipe_sequence PIPE command        { $3 :: $1 }

command:       | scmd                              { Simple $1 [] }
               | compound                          { Compound $1 [] }
               | compound rlist                    { Compound $1 $2 }
               | function_def                      { $1 }

compound:      | brace_group                       { $1 }
               | subshell                          { $1 }
               | for_clause                        { $1 }
               | case_clause                       { $1 }
               | if_clause                         { $1 }
               | while_clause                      { $1 }
               | until_clause                      { $1 }

subshell:      | LPAREN clist RPAREN               { Subshell $2 }

clist:         | term                              { $1 }
               | term SEMI                         { $1 }
               | term SEMI clist                   { $1 }

term:          | command                           { [$1] }
               | command SEMI                      { [$1] }

for_clause:    | FOR_TOK NAME IN_TOK wlist SEMI do_group   { ForClause $2 (Some $4) $6 }
               | FOR_TOK NAME do_group                 { ForClause $2 None $3 }

wlist:         | WORD                              { [$1] }
               | wlist WORD                        { $2 :: $1 }

case_clause:   | CASE_TOK WORD IN_TOK case_list ESAC_TOK       { CaseClause $2 $4 }
               | CASE_TOK WORD IN_TOK ESAC_TOK                 { CaseClause $2 [] }

case_list:     | case_item case_list               { $1 :: $2 }
               | case_item                         { [$1] }

case_item:     | pattern RPAREN clist DSEMI        { ($1, $3) }
               | LPAREN pattern RPAREN clist DSEMI { ($2, []) }

pattern:       | WORD                              { [$1] }
               | WORD pattern                      { $1 :: $2 }

if_clause:     | IF_TOK clist THEN_TOK clist FI_TOK            { IfClause $2 $4 [] None }
               | IF_TOK clist THEN_TOK clist else_part FI_TOK  { IfClause $2 $4 $5 None }

else_part:     | ELSE_TOK clist                        { [] }
               | ELIF_TOK clist THEN_TOK clist             { [($2, $4)] }
               | ELIF_TOK clist THEN_TOK clist else_part   { ($2, $4) :: $5 }

while_clause:  | WHILE_TOK clist DO_TOK do_group           { WhileClause $2 $4 }

until_clause:  | UNTIL_TOK clist DO_TOK do_group           { UntilClause $2 $4 }

function_def:  | NAME LPAREN RPAREN function_body  { FunctionDef $1 $4 }

function_body: | compound                          { Compound $1 [] }
               | compound rlist                    { Compound $1 $2 }

brace_group:   | LBRACE clist RBRACE               { BraceGroup $2 }

do_group:      | DO_TOK clist DONE_TOK                     { $2 }

scmd:          | prefix WORD suffix                { Some ($2, []) }
               | prefix WORD                       { Some ($2, []) }
               | prefix                            { None }
               | WORD suffix                       { Some ($1, []) }
               | WORD                              { Some ($1, []) }

rlist:         | io_redirect                       { [$1] }
               | rlist io_redirect                 { $2 :: $1 }

io_redirect:   | LESS WORD                         { IoFile None Less $2 }
               | GREAT WORD                        { IoFile None Great $2 }
               | DGREAT WORD                       { IoFile None DGreat $2 }
               | LESSAND WORD                      { IoFile None LessAnd $2 }
               | GREATAND WORD                     { IoFile None GreatAnd $2 }
               | LESSGREAT WORD                    { IoFile None LessGreat $2 }
               | CLOBBER WORD                      { IoFile None Clobber $2 }
               | DLESS WORD                        { IoHere None DLess $2 }
               | DLESSDASH WORD                    { IoHere None DLessDash $2 }
               | IO_NUMBER LESS WORD               { IoFile (Some $1) Less $3 }
               | IO_NUMBER GREAT WORD              { IoFile (Some $1) Great $3 }
               | IO_NUMBER DGREAT WORD             { IoFile (Some $1) DGreat $3 }
               | IO_NUMBER LESSAND WORD            { IoFile (Some $1) LessAnd $3 }
               | IO_NUMBER GREATAND WORD           { IoFile (Some $1) GreatAnd $3 }
               | IO_NUMBER LESSGREAT WORD          { IoFile (Some $1) LessGreat $3 }
               | IO_NUMBER CLOBBER WORD            { IoFile (Some $1) Clobber $3 }
               | IO_NUMBER DLESS WORD              { IoHere (Some $1) DLess $3 }
               | IO_NUMBER DLESSDASH WORD          { IoHere (Some $1) DLessDash $3 }

separator:     | AMP                               { Amp }
               | SEMI                              { Semi }

prefix:        | io_redirect                       { [$1] }
               | prefix io_redirect                { $2 :: $1 }
               | ASSIGNMENT_WORD                   { [Assignment $1] }
               | prefix ASSIGNMENT_WORD            { Assignment $2 :: $1 }

suffix:        | io_redirect                       { [] }
               | suffix io_redirect                { $1 }
               | WORD                              { [Word $1] }
               | suffix WORD                       { Word $2 :: $1 }
               | SEMI                              { [] }
               | suffix SEMI                       { $1 }

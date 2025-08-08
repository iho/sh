%{
open Ast
let fst4 (a, _, _, _) = a
let snd4 (_, b, _, _) = b
let trd4 (_, _, c, _) = c
let fth4 (_, _, _, d) = d
let fst3 (a, _, _) = a
let snd3 (_, b, _) = b
let trd3 (_, _, c) = c
let fst (a, _) = a
let snd (_, b) = b
let extract_words = List.map (function Word w -> w | _ -> raise (Failure "Expected Word"))
%}

%token <string> WORD ASSIGNMENT_WORD NAME
%token <int> IO_NUMBER
%token AND_IF OR_IF DSEMI DLESS DGREAT LESSAND GREATAND LESSGREAT DLESSDASH CLOBBER
%token LESS GREAT PIPE AMP SEMI NEWLINE EOF BANG LPAREN RPAREN LBRACE RBRACE
%token IF THEN ELSE ELIF FI DO DONE CASE ESAC WHILE UNTIL FOR IN
%start <Ast.exp> program

%%

(* https://pubs.opengroup.org/onlinepubs/9695969399/toc.pdf *)

program:       | list separator                    { ListItem ($1, Some $2) }
               | list                              { ListItem ($1, None) }
               | list NEWLINE                      { ListItem ($1, None) }
list:          | list separator and_or             { List ($1, $2, $3) }
               | and_or                            { $1 }
and_or:        | pipeline                          { Pipeline (fst $1, snd $1) }
               | and_or AND_IF pipeline            { AndIf ($1, Pipeline (fst $3, snd $3)) }
               | and_or OR_IF pipeline             { OrIf ($1, Pipeline (fst $3, snd $3)) }
pipeline:      | pipe_sequence                     { (false, $1) }
               | BANG pipe_sequence                { (true, $2) }
pipe_sequence: | command                           { [$1] }
               | pipe_sequence PIPE command        { $1 @ [$3] }
command:       | scmd                              { Simple ($1, []) }
               | compound                          { Compound ($1, []) }
               | compound rlist                    { Compound ($1, $2) }
               | function_def                      { $1 }
compound:      | brace_group                       { BraceGroup $1 }
               | subshell                          { Subshell $1 }
               | for_clause                        { ForClause (fst3 $1, Option.map extract_words (snd3 $1), trd3 $1) }
               | case_clause                       { CaseClause (fst $1, snd $1) }
               | if_clause                         { IfClause (fst4 $1, snd4 $1, trd4 $1, fth4 $1) }
               | while_clause                      { WhileClause (fst $1, snd $1) }
               | until_clause                      { UntilClause (fst $1, snd $1) }
subshell:      | LPAREN clist RPAREN               { $2 }
clist:         | term                              { $1 }
               | term SEMI                         { $1 }  (* Ignore trailing SEMI *)
               | term SEMI clist                   { $1 @ $3 }  (* Multiple terms *)
term:          | command                           { [$1] }
               | command SEMI                      { [$1] }  (* Allow SEMI after command *)
for_clause:    | FOR NAME IN wlist SEMI do_group   { ($2, Some $4, $6) }
               | FOR NAME do_group                 { ($2, None, $3) }
wlist:         | WORD                              { [Word $1] }
               | wlist WORD                        { $1 @ [Word $2] }
case_clause:   | CASE WORD IN case_list ESAC       { ($2, $4) }
               | CASE WORD IN ESAC                 { ($2, []) }
case_list:     | case_list case_item               { $1 @ [$2] }
               | case_item                         { [$1] }
case_item:     | pattern RPAREN clist DSEMI        { (extract_words $1, $3) }
               | LPAREN pattern RPAREN clist DSEMI { (extract_words $2, []) }
pattern:       | WORD                              { [Word $1] }
               | pattern PIPE WORD                 { $1 @ [Word $3] }
if_clause:     | IF clist THEN clist FI            { ($2, $4, [], None) }
               | IF clist THEN clist else_part FI  { ($2, $4, fst $5, snd $5) }
else_part:     | ELSE clist                        { ([], Some $2) }
               | ELIF clist THEN clist             { ([($2, $4)], None) }
               | ELIF clist THEN clist else_part   { (($2, $4) :: fst $5, snd $5) }
while_clause:  | WHILE clist DO do_group           { ($2, $4) }
until_clause:  | UNTIL clist DO do_group           { ($2, $4) }
function_def:  | NAME LPAREN RPAREN function_body  { FunctionDef ($1, $4) }
function_body: | compound                          { Compound ($1, []) }
               | compound rlist                    { Compound ($1, $2) }
brace_group:   | LBRACE clist RBRACE               { $2 }
do_group:      | DO clist DONE                     { $2 }
scmd:          | prefix WORD suffix                { Some ($2, extract_words $3) }
               | prefix WORD                       { Some ($2, []) }
               | prefix                            { None }
               | WORD suffix                       { Some ($1, extract_words $2) }
               | WORD                              { Some ($1, []) }
rlist:         | io_redirect                       { [$1] }
               | rlist io_redirect                 { $1 @ [$2] }
io_redirect:   | io_file                           { IoFile (None, fst $1, snd $1) }
               | IO_NUMBER io_file                 { IoFile (Some $1, fst $2, snd $2) }
               | io_here                           { IoHere (None, fst $1, snd $1) }
               | IO_NUMBER io_here                 { IoHere (Some $1, fst $2, snd $2) }
io_file:       | LESS WORD                         { (Less, $2) }
               | GREAT WORD                        { (Great, $2) }
               | DGREAT WORD                       { (DGreat, $2) }
               | LESSAND WORD                      { (LessAnd, $2) }
               | GREATAND WORD                     { (GreatAnd, $2) }
               | LESSGREAT WORD                    { (LessGreat, $2) }
               | CLOBBER WORD                      { (Clobber, $2) }
io_here:       | DLESS WORD                        { (DLess, $2) }
               | DLESSDASH WORD                    { (DLessDash, $2) }
separator:     | AMP                               { Amp }
               | SEMI                              { Semi }
prefix:        | io_redirect                       { [$1] }
               | prefix io_redirect                { $1 @ [$2] }
               | ASSIGNMENT_WORD                   { [Assignment $1] }
               | prefix ASSIGNMENT_WORD            { $1 @ [Assignment $2] }
suffix:        | io_redirect                       { [] }
               | suffix io_redirect                { $1 }
               | WORD                              { [Word $1] }
               | suffix WORD                       { $1 @ [Word $2] }
               | SEMI                              { [] }
               | suffix SEMI                       { $1 }

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
%}

%token <string> WORD ASSIGNMENT_WORD NAME
%token <int> IO_NUMBER
%token AND_IF OR_IF DSEMI DLESS DGREAT LESSAND GREATAND LESSGREAT DLESSDASH CLOBBER
%token LESS GREAT PIPE AMP SEMI NEWLINE EOF BANG LPAREN RPAREN LBRACE RBRACE
%token IF THEN ELSE ELIF FI DO DONE CASE ESAC WHILE UNTIL FOR IN
%start <Ast.program> program

%%

program:
  | complete_commands EOF { $1 }
  | EOF { [] }

complete_commands:
  | complete_commands NEWLINE complete_command { $1 @ [$3] }
  | complete_command { [$1] }

complete_command:
  | list separator_op { ($1, Some $2) }
  | list { ($1, None) }

list:
  | list separator_op and_or { List ($1, $2, $3) }
  | and_or { $1 }

and_or:
  | pipeline { AndOr $1 }
  | and_or AND_IF pipeline { AndIf ($1, $3) }
  | and_or OR_IF pipeline { OrIf ($1, $3) }

pipeline:
  | pipe_sequence { (false, $1) }
  | BANG pipe_sequence { (true, $2) }

pipe_sequence:
  | command { [$1] }
  | pipe_sequence PIPE command { $1 @ [$3] }

command:
  | simple_command { Simple ($1, []) }
  | compound_command { Compound ($1, []) }
  | compound_command redirect_list { Compound ($1, $2) }
  | function_definition { $1 }

simple_command:
  | cmd_prefix cmd_word cmd_suffix { Some ($2, $3) }
  | cmd_prefix cmd_word { Some ($2, []) }
  | cmd_prefix { None }
  | cmd_name cmd_suffix { Some ($1, $2) }
  | cmd_name { Some ($1, []) }

cmd_name:
  | WORD { $1 }

cmd_word:
  | WORD { $1 }

cmd_prefix:
  | io_redirect { [$1] }
  | cmd_prefix io_redirect { $1 @ [$2] }
  | ASSIGNMENT_WORD { [Assignment $1] }
  | cmd_prefix ASSIGNMENT_WORD { $1 @ [Assignment $2] }

cmd_suffix:
  | io_redirect { [] }
  | cmd_suffix io_redirect { $1 }
  | WORD { [$1] }
  | cmd_suffix WORD { $1 @ [$2] }

compound_command:
  | brace_group { BraceGroup $1 }
  | subshell { Subshell $1 }
  | for_clause { ForClause (fst3 $1, snd3 $1, trd3 $1) }
  | case_clause { CaseClause (fst $1, snd $1) }
  | if_clause { IfClause (fst4 $1, snd4 $1, trd4 $1, fth4 $1) }
  | while_clause { WhileClause (fst $1, snd $1) }
  | until_clause { UntilClause (fst $1, snd $1) }

brace_group:
  | LBRACE compound_list RBRACE { $2 }

subshell:
  | LPAREN compound_list RPAREN { $2 }

compound_list:
  | term { $1 }

term:
  | command { [$1] }
  | term separator command { $1 @ [$3] }

for_clause:
  | FOR NAME IN wordlist SEMI do_group { ($2, Some $4, $6) }
  | FOR NAME SEMI do_group { ($2, None, $4) }

wordlist:
  | WORD { [$1] }
  | wordlist WORD { $1 @ [$2] }

case_clause:
  | CASE WORD IN case_list ESAC { ($2, $4) }
  | CASE WORD IN ESAC { ($2, []) }

case_list:
  | case_list case_item { $1 @ [$2] }
  | case_item { [$1] }

case_item:
  | pattern RPAREN compound_list DSEMI { ($1, $3) }
  | pattern RPAREN { ($1, []) }

pattern:
  | WORD { [$1] }
  | pattern PIPE WORD { $1 @ [$3] }

if_clause:
  | IF compound_list THEN compound_list FI { ($2, $4, [], None) }
  | IF compound_list THEN compound_list else_part FI { ($2, $4, fst $5, snd $5) }

else_part:
  | ELSE compound_list { ([], Some $2) }
  | ELIF compound_list THEN compound_list { ([($2, $4)], None) }
  | ELIF compound_list THEN compound_list else_part { (($2, $4) :: fst $5, snd $5) }

while_clause:
  | WHILE compound_list DO compound_list DONE { ($2, $4) }

until_clause:
  | UNTIL compound_list DO compound_list DONE { ($2, $4) }

function_definition:
  | NAME LPAREN RPAREN function_body { FunctionDef ($1, $4) }

function_body:
  | compound_command { Compound ($1, []) }
  | compound_command redirect_list { Compound ($1, $2) }

do_group:
  | DO compound_list DONE { $2 }

redirect_list:
  | io_redirect { [$1] }
  | redirect_list io_redirect { $1 @ [$2] }

io_redirect:
  | io_file { IoFile (None, fst $1, snd $1) }
  | IO_NUMBER io_file { IoFile (Some $1, fst $2, snd $2) }
  | io_here { IoHere (None, fst $1, snd $1) }
  | IO_NUMBER io_here { IoHere (Some $1, fst $2, snd $2) }

io_file:
  | LESS WORD { (Less, $2) }
  | GREAT WORD { (Great, $2) }
  | DGREAT WORD { (DGreat, $2) }
  | LESSAND WORD { (LessAnd, $2) }
  | GREATAND WORD { (GreatAnd, $2) }
  | LESSGREAT WORD { (LessGreat, $2) }
  | CLOBBER WORD { (Clobber, $2) }

io_here:
  | DLESS WORD { (DLess, $2) }
  | DLESSDASH WORD { (DLessDash, $2) }

separator_op:
  | AMP { `Amp }
  | SEMI { `Semi }

separator:
  | separator_op { () }
  | NEWLINE { () }

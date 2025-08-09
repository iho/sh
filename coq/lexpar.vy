%{
(* Empty header for Coq generation *)
%}

%token WORD ASSIGNMENT_WORD NAME
%token IO_NUMBER
%token AND_IF OR_IF DSEMI DLESS DGREAT LESSAND GREATAND LESSGREAT DLESSDASH CLOBBER
%token LESS GREAT PIPE AMP SEMI NEWLINE EOF_TOK BANG LPAREN RPAREN LBRACE RBRACE
%token IF_TOK THEN_TOK ELSE_TOK ELIF_TOK FI_TOK DO_TOK DONE_TOK CASE_TOK ESAC_TOK WHILE_TOK UNTIL_TOK FOR_TOK IN_TOK

%start <unit> program

%%

(* ======== PARSER RULES ======== *)

program:       | list separator                    { () }
               | list                              { () }
               | list NEWLINE                      { () }
list:          | list separator and_or             { () }
               | and_or                            { () }
and_or:        | pipeline                          { () }
               | and_or AND_IF pipeline            { () }
               | and_or OR_IF pipeline             { () }
pipeline:      | pipe_sequence                     { () }
               | BANG pipe_sequence                { () }
pipe_sequence: | command                           { () }
               | pipe_sequence PIPE command        { () }
command:       | scmd                              { () }
               | compound                          { () }
               | compound rlist                    { () }
               | function_def                      { () }
compound:      | brace_group                       { () }
               | subshell                          { () }
               | for_clause                        { () }
               | case_clause                       { () }
               | if_clause                         { () }
               | while_clause                      { () }
               | until_clause                      { () }
subshell:      | LPAREN clist RPAREN               { () }
clist:         | term                              { () }
               | term SEMI                         { () }
               | term SEMI clist                   { () }
term:          | command                           { () }
               | command SEMI                      { () }
for_clause:    | FOR_TOK NAME IN_TOK wlist SEMI do_group   { () }
               | FOR_TOK NAME do_group                 { () }
wlist:         | WORD                              { () }
               | wlist WORD                        { () }
case_clause:   | CASE_TOK WORD IN_TOK case_list ESAC_TOK       { () }
               | CASE_TOK WORD IN_TOK ESAC_TOK                 { () }
case_list:     | case_list case_item               { () }
               | case_item                         { () }
case_item:     | pattern RPAREN clist DSEMI        { () }
               | LPAREN pattern RPAREN clist DSEMI { () }
pattern:       | WORD                              { () }
               | pattern PIPE WORD                 { () }
if_clause:     | IF_TOK clist THEN_TOK clist FI_TOK            { () }
               | IF_TOK clist THEN_TOK clist else_part FI_TOK  { () }
else_part:     | ELSE_TOK clist                        { () }
               | ELIF_TOK clist THEN_TOK clist             { () }
               | ELIF_TOK clist THEN_TOK clist else_part   { () }
while_clause:  | WHILE_TOK clist DO_TOK do_group           { () }
until_clause:  | UNTIL_TOK clist DO_TOK do_group           { () }
function_def:  | NAME LPAREN RPAREN function_body  { () }
function_body: | compound                          { () }
               | compound rlist                    { () }
brace_group:   | LBRACE clist RBRACE               { () }
do_group:      | DO_TOK clist DONE_TOK                     { () }
scmd:          | prefix WORD suffix                { () }
               | prefix WORD                       { () }
               | prefix                            { () }
               | WORD suffix                       { () }
               | WORD                              { () }
rlist:         | io_redirect                       { () }
               | rlist io_redirect                 { () }
io_redirect:   | io_file                           { () }
               | IO_NUMBER io_file                 { () }
               | io_here                           { () }
               | IO_NUMBER io_here                 { () }
io_file:       | LESS WORD                         { () }
               | GREAT WORD                        { () }
               | DGREAT WORD                       { () }
               | LESSAND WORD                      { () }
               | GREATAND WORD                     { () }
               | LESSGREAT WORD                    { () }
               | CLOBBER WORD                      { () }
io_here:       | DLESS WORD                        { () }
               | DLESSDASH WORD                    { () }
separator:     | AMP                               { () }
               | SEMI                              { () }
prefix:        | io_redirect                       { () }
               | prefix io_redirect                { () }
               | ASSIGNMENT_WORD                   { () }
               | prefix ASSIGNMENT_WORD            { () }
suffix:        | io_redirect                       { () }
               | suffix io_redirect                { () }
               | WORD                              { () }
               | suffix WORD                       { () }
               | SEMI                              { () }
               | suffix SEMI                       { () }

%%

(* ======== LEXER ======== *)

let lat1   = [^ '\t' ' ' '\r' '\n' '(' ')' '[' ']' ':' '.' ',' '<' '>']
let beg    = lat1 # '-'
let nl            = "\r\n"|"\r"|"\n"
let inlineComment = "#" [^ '\n' '\r']* (nl|eof)

let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']
let utf8    = lat1|bytes2|bytes3|bytes4
let ident   = beg utf8*
let ws      = ['\t' ' ']

let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let name = letter (letter | digit | '_')*
let word = [^ ' ' '\t' '\n' ';' '&' '|' '<' '>' '(' ')' '{' '}']+ | '"' [^ '"']* '"'

rule token = parse
  | '\n' { NEWLINE }
  | [' ' '\t' '\n'] { token lexbuf }
  | "&&" { AND_IF }
  | "||" { OR_IF }
  | "<<" { DLESS }
  | ">>" { DGREAT }
  | "<&" { LESSAND }
  | ">&" { GREATAND }
  | "<>" { LESSGREAT }
  | "<<-" { DLESSDASH }
  | ">|" { CLOBBER }
  | "<" { LESS }
  | ">" { GREAT }
  | "|" { PIPE }
  | "&" { AMP }
  | ";" { SEMI }
  | "!" { BANG }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "if" { IF_TOK }
  | "then" { THEN_TOK }
  | "else" { ELSE_TOK }
  | "elif" { ELIF_TOK }
  | "fi" { FI_TOK }
  | "do" { DO_TOK }
  | "done" { DONE_TOK }
  | "case" { CASE_TOK }
  | "esac" { ESAC_TOK }
  | "while" { WHILE_TOK }
  | "until" { UNTIL_TOK }
  | "for" { FOR_TOK }
  | "in" { IN_TOK }
  | ['0'-'9']+ as n { IO_NUMBER (int_of_string n) }
  | [^ ' ' '\t' '\n' ';' '&' '|' '<' '>' '(' ')' '{' '}']+ as w { WORD w }
  | eof { EOF_TOK }
  | _ { raise (Error (Lexing.lexeme lexbuf)) }

{
open Parser
exception SyntaxError of string
}

let whitespace = [' ' '\t']+
let newline = '\n'
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let name = letter (letter | digit | '_')*
let word = [^ ' ' '\t' '\n' ';' '&' '|' '<' '>' '(' ')' '{' '}']+ | '"' [^ '"']* '"'

rule token = parse
  | whitespace { token lexbuf }
  | newline    { NEWLINE }
  | "&&"       { AND_IF }
  | "||"       { OR_IF }
  | ";;"       { DSEMI }
  | "<<"       { DLESS }
  | ">>"       { DGREAT }
  | "<&"       { LESSAND }
  | ">&"       { GREATAND }
  | "<>"       { LESSGREAT }
  | "<<-"      { DLESSDASH }
  | ">|"       { CLOBBER }
  | "<"        { LESS }
  | ">"        { GREAT }
  | "|"        { PIPE }
  | "&"        { AMP }
  | ";"        { SEMI }
  | "if"       { IF }
  | "then"     { THEN }
  | "else"     { ELSE }
  | "elif"     { ELIF }
  | "fi"       { FI }
  | "do"       { DO }
  | "done"     { DONE }
  | "case"     { CASE }
  | "esac"     { ESAC }
  | "while"    { WHILE }
  | "until"    { UNTIL }
  | "for"      { FOR }
  | "in"       { IN }
  | "{"        { LBRACE }
  | "}"        { RBRACE }
  | "!"        { BANG }
  | "("        { LPAREN }
  | ")"        { RPAREN }
  | digit+     { IO_NUMBER (int_of_string (Lexing.lexeme lexbuf)) }
  | name '=' [^ ' ' '\t' '\n' ';' '&' '|' '<' '>' '(' ')' '{' '}']+ { ASSIGNMENT_WORD (Lexing.lexeme lexbuf) }
  | name       { NAME (Lexing.lexeme lexbuf) }
  | word       { WORD (Lexing.lexeme lexbuf) }
  | eof        { EOF }
  | _          { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }

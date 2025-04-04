{
  open Parser
  open Lexing

  let nextLine lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }

  exception Error of string
}

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
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "elif" { ELIF }
  | "fi" { FI }
  | "do" { DO }
  | "done" { DONE }
  | "case" { CASE }
  | "esac" { ESAC }
  | "while" { WHILE }
  | "until" { UNTIL }
  | "for" { FOR }
  | "in" { IN }
  | ['0'-'9']+ as n { IO_NUMBER (int_of_string n) }
  | ['a'-'z' 'A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* as w { WORD w }
  | eof { EOF }
  | _ { raise (Error (Lexing.lexeme lexbuf)) }


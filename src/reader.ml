open Parser
open Lexing
open Ast

type content = exp list
type file = string * content

let parseErr f lexbuf filename =
  try 
    Error.Ok (f Lexer.token lexbuf)
  with exn ->
    match exn with
    | Parser.Error ->
        Error.Error (Printf.sprintf "Parse error in %s at line %d, token '%s'" 
                     filename lexbuf.lex_curr_p.pos_lnum (lexeme lexbuf))
    | _ ->
        Error.Error (Printf.sprintf "Unexpected error in %s: %s" filename (Printexc.to_string exn))

let lex filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  Printf.printf "Lexing \"%s\".\n" filename;
  let rec lex_loop () =
    let tok = Lexer.token lexbuf in
    if tok = Parser.EOF then (
      close_in chan;
      print_newline ()
    ) else (
      print_string (Token.tokenToString tok ^ " ");
      lex_loop ()
    )
  in
  lex_loop ()

let parseWithResult filename chan =
  let lexbuf = Lexing.from_channel chan in
  match parseErr Parser.program lexbuf filename with
  | Error.Ok file -> 
      print_endline (string_of_exp file);
      Error.Ok file
  | Error.Error msg -> 
      Error.Error msg

let parse filename =
  let chan = open_in filename in
  Printf.printf "Parsing \"%s\".\n" filename;
  let result = Error.handleErrors
    (parseWithResult filename)
    chan (Program []) in
  close_in chan;
  result

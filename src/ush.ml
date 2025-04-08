open Ast
open Unix
open Token
open Stdlib
open Parser

let rec execute_program = function
  | Program items -> List.iter execute_list_item items
  | _ -> failwith "Expected Program"

and execute_list_item = function
  | ListItem (and_or, sep) ->
      let status = execute_exp and_or in
      (match sep with
       | Some `Amp ->
           if fork () = 0 then begin
             ignore (execute_exp and_or);
             exit 0
           end
       | _ -> ())
  | _ -> failwith "Expected ListItem"

and execute_exp = function
  | Pipeline (bang, cmds) -> execute_pipeline (bang, cmds)
  | AndIf (a, p) -> if execute_exp a = 0 then execute_exp p else 1
  | OrIf (a, p) -> if execute_exp a <> 0 then execute_exp p else 0
  | List (a, op, b) ->
      let status = execute_exp a in
      (match op with
       | `Amp ->
           if fork () = 0 then begin
             ignore (execute_exp b);
             exit 0
           end;
           status
       | `Semi -> if status = 0 then execute_exp b else status)
  | exp -> execute_command exp

and execute_pipeline (bang, cmds) =
  let rec pipe cmds =
    match cmds with
    | [cmd] -> execute_command cmd
    | cmd :: rest ->
        let (r, w) = Unix.pipe () in
        let pid = fork () in
        if pid = 0 then begin
          dup2 w Unix.stdout; close r; close w;
          ignore (execute_command cmd);
          exit 0
        end else begin
          dup2 r Unix.stdin; close r; close w;
          let rest_status = pipe rest in
          let (_, cmd_wstatus) = waitpid [] pid in
          let cmd_status = match cmd_wstatus with WEXITED n -> n | _ -> 1 in
          if cmd_status <> 0 then cmd_status else rest_status
        end
    | [] -> 0
  in
  let status = pipe cmds in
  if bang then if status = 0 then 1 else 0 else status

and execute_command = function
  | Simple (Some (cmd, args), redirects) ->
      let pid = fork () in
      if pid = 0 then begin
        List.iter apply_redirect redirects;
        (try execvp cmd (Array.of_list (cmd :: args))
         with Unix_error (ENOENT, _, _) -> 
           Printf.eprintf "ush: command not found: %s\n" cmd; exit 127)
      end else begin
        let (_, status) = waitpid [] pid in
        match status with WEXITED n -> n | _ -> 1
      end
  | Simple (None, redirects) ->
      List.iter apply_redirect redirects; 0
  | Compound (comp, redirects) ->
      let pid = fork () in
      if pid = 0 then begin
        List.iter apply_redirect redirects;
        ignore (execute_exp comp); exit 0
      end else begin
        let (_, status) = waitpid [] pid in
        match status with WEXITED n -> n | _ -> 1
      end
  | FunctionDef (name, body) -> 0
  | _ -> failwith "Expected command"

and apply_redirect = function
  | IoFile (n, op, file) ->
      let fd = openfile file [O_WRONLY; O_CREAT] 0o666 in
      (match op with
       | Great -> dup2 fd Unix.stdout
       | DGreat -> dup2 fd Unix.stdout
       | Less -> dup2 fd Unix.stdin
       | _ -> ());
      close fd
  | IoHere _ -> ()
  | Assignment s ->
      let parts = String.split_on_char '=' s in
      Unix.putenv (List.hd parts) (List.nth parts 1)
  | _ -> ()

and execute_compound = function
  | BraceGroup cmds -> List.iter (fun cmd -> ignore (execute_command cmd)) cmds
  | Subshell cmds -> List.iter (fun cmd -> ignore (execute_command cmd)) cmds
  | ForClause (var, words, body) ->
      let words = match words with Some ws -> ws | None -> [] in
      List.iter (fun w -> Unix.putenv var w; List.iter (fun cmd -> ignore (execute_command cmd)) body) words
  | CaseClause (word, cases) ->
      List.iter (fun (pats, cmds) ->
        if List.mem word pats then List.iter (fun cmd -> ignore (execute_command cmd)) cmds) cases
  | IfClause (cond, then_part, elifs, else_part) ->
      if execute_condition cond then List.iter (fun cmd -> ignore (execute_command cmd)) then_part
      else begin
        let rec check_elifs = function
          | [] -> (match else_part with Some e -> List.iter (fun cmd -> ignore (execute_command cmd)) e | None -> ())
          | (c, t) :: rest ->
              if execute_condition c then List.iter (fun cmd -> ignore (execute_command cmd)) t
              else check_elifs rest
        in check_elifs elifs
      end
  | WhileClause (cond, body) ->
      while execute_condition cond do List.iter (fun cmd -> ignore (execute_command cmd)) body done
  | UntilClause (cond, body) ->
      while not (execute_condition cond) do List.iter (fun cmd -> ignore (execute_command cmd)) body done
  | _ -> failwith "Expected compound command"

and execute_condition cmds =
  let status = List.fold_left (fun acc cmd ->
    let s = execute_command cmd in
    if acc = 0 then s else acc) 0 cmds
  in status = 0

let parse_string2 input =
  try
    let lexbuf = Lexing.from_string (input ^ "\n") in
    let rec print_tokens () =
      let tok = Lexer.token lexbuf in
      if tok = EOF then () else (Printf.printf "Token: %s\n" (tokenToString tok); print_tokens ())
    in
    let _ = print_tokens () in
    let lexbuf = Lexing.from_string (input ^ "\n") in
    Printf.printf "Starting parse...\n"; flush stdout;
    let ast = Parser.program Lexer.token lexbuf in
    let _ = Printf.printf "Debug 2: %s\n" (string_of_exp ast) in
    flush stdout;
    Some ast
  with
  | Lexer.Error msg -> Printf.printf "Lexer error: %s\n" msg; flush stdout; None
  | Parser.Error -> Printf.printf "Parse error at position %d\n" (Lexing.lexeme_start (Lexing.from_string input)); flush stdout; None
  | Error.Parser (line, tok, _) -> Printf.printf "Custom parse error at line %d, token '%s'\n" line tok; flush stdout; None
  | ex -> Printf.printf "Unexpected error: %s\n" (Printexc.to_string ex); flush stdout; None

let parse_string input =
  try
    let lexbuf = Lexing.from_string (input ^ "\n") in
    let rec print_tokens () =
      let tok = Lexer.token lexbuf in
      if tok = EOF then () else (Printf.printf "Token: %s\n" (tokenToString tok); print_tokens ())
    in
    let _ = print_tokens () in
    let lexbuf = Lexing.from_string (input ^ "\n") in
    Printf.printf "Starting parse...\n"; flush stdout;
    let ast = Parser.program Lexer.token lexbuf in
    let _ = Printf.printf "Debug 2: %s\n" (string_of_exp ast) in
    flush stdout;
    Some ast
  with
  | Lexer.Error msg -> Printf.eprintf "Lexer error: %s\n" msg; flush stdout; None
  | Parser.Error -> Printf.printf "Parse error at position %d\n" (Lexing.lexeme_start (Lexing.from_string input)); flush stdout; None
  | ex -> Printf.eprintf "Unexpected error: %s\n" (Printexc.to_string ex); flush stdout; None

let repl () =
  print_endline ("Synrc POSIX Shell (c) 2025\n");
  try while true do
    print_string "$ ";
    let line = read_line () in
    match parse_string line with
    | Some ast -> Printf.printf ": Parsed (%s)\n" (string_of_exp ast)
    | None -> Printf.printf ": None\n"
  done with End_of_file -> print_newline ()

let () = repl ()

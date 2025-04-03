open Ast
open Unix
open Stdlib

let rec execute_program prog =
  List.iter execute_list_item prog

and execute_list_item (and_or, sep) =
  let status = execute_and_or and_or in
  match sep with
  | Some `Amp ->
      if fork () = 0 then begin
        ignore (execute_and_or and_or);
        exit 0
      end
  | _ -> ()

and execute_and_or = function
  | AndOr p -> execute_pipeline p
  | AndIf (a, p) -> if execute_and_or a = 0 then execute_pipeline p else 1
  | OrIf (a, p) -> if execute_and_or a <> 0 then execute_pipeline p else 0
  | List (a, op, b) ->
      let status = execute_and_or a in
      (match op with
       | `Amp ->
           if fork () = 0 then begin
             ignore (execute_and_or b);
             exit 0
           end;
           status
       | `Semi -> if status = 0 then execute_and_or b else status)

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
        execvp cmd (Array.of_list (cmd :: args))
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
        execute_compound comp; exit 0
      end else begin
        let (_, status) = waitpid [] pid in
        match status with WEXITED n -> n | _ -> 1
      end
  | FunctionDef (name, body) ->
      0

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

and execute_compound = function
  | BraceGroup cmds -> List.iter (fun cmd -> ignore (execute_command cmd)) cmds; ()
  | Subshell cmds -> List.iter (fun cmd -> ignore (execute_command cmd)) cmds; ()
  | ForClause (var, words, body) ->
      let words = match words with Some ws -> ws | None -> [] in
      List.iter (fun w -> Unix.putenv var w; List.iter (fun cmd -> ignore (execute_command cmd)) body) words; ()
  | CaseClause (word, cases) ->
      List.iter (fun (pats, cmds) ->
        if List.mem word pats then List.iter (fun cmd -> ignore (execute_command cmd)) cmds) cases; ()
  | IfClause (cond, then_part, elifs, else_part) ->
      if execute_condition cond then List.iter (fun cmd -> ignore (execute_command cmd)) then_part
      else begin
        let rec check_elifs = function
          | [] -> (match else_part with Some e -> List.iter (fun cmd -> ignore (execute_command cmd)) e | None -> ())
          | (c, t) :: rest ->
              if execute_condition c then List.iter (fun cmd -> ignore (execute_command cmd)) t
              else check_elifs rest
        in check_elifs elifs
      end; ()
  | WhileClause (cond, body) ->
      while execute_condition cond do List.iter (fun cmd -> ignore (execute_command cmd)) body done; ()
  | UntilClause (cond, body) ->
      while not (execute_condition cond) do List.iter (fun cmd -> ignore (execute_command cmd)) body done; ()

and execute_condition cmds =
  let status = List.fold_left (fun acc cmd ->
    let s = execute_command cmd in
    if acc = 0 then s else acc) 0 cmds
  in status = 0

let () =
  let prompt = "sh> " in
  Printf.printf "%s" prompt;
  flush stdout;
  let lexbuf = Lexing.from_channel stdin in
  let rec loop () =
    try
      let ast = Parser.program Lexer.token lexbuf in
      execute_program ast;
      Printf.printf "%s" prompt; flush stdout;
      loop ()
    with
    | Lexer.SyntaxError msg ->
        Printf.eprintf "Lexing error: %s\n" msg;
        Lexing.flush_input lexbuf;
        Printf.printf "%s" prompt; flush stdout;
        loop ()
    | Parser.Error ->
        Printf.eprintf "Parsing error\n";
        Lexing.flush_input lexbuf;
        Printf.printf "%s" prompt; flush stdout;
        loop ()
    | End_of_file ->
        Printf.printf "Goodbye\n"; exit 0
  in
  loop ()

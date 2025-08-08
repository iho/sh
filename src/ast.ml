type word = string
type io_number = int

type redirect_op =
  | Less | Great | DGreat | LessAnd | GreatAnd | LessGreat
  | DLess | DLessDash | Clobber



type sep = Amp | Semi

type exp =
  | Word of word
  | IoFile of io_number option * redirect_op * word
  | IoHere of io_number option * redirect_op * word
  | Assignment of string
  | Simple of (word * word list) option * exp list (* redirects *)
  | Compound of exp * exp list                     (* compound_command, redirects *)
  | FunctionDef of string * exp                    (* name, body *)
  | BraceGroup of exp list                         (* commands *)
  | Subshell of exp list                           (* commands *)
  | ForClause of string * word list option * exp list  (* var, words, body *)
  | CaseClause of word * (word list * exp list) list   (* word, cases *)
  | IfClause of exp list * exp list * (exp list * exp list) list * exp list option  (* cond, then, elifs, else *)
  | WhileClause of exp list * exp list             (* cond, body *)
  | UntilClause of exp list * exp list             (* cond, body *)
  | Pipeline of bool * exp list                    (* bang, commands *)
  | AndOr of exp                                   (* pipeline *)
  | AndIf of exp * exp                             (* left, right *)
  | OrIf of exp * exp                              (* left, right *)
  | List of exp * sep * exp             (* left, sep, right *)
  | ListItem of exp * sep option        (* and_or, separator *)
  | Program of exp list                            (* list_items *)


let rec string_of_exp = function
  | Word w -> w
  | IoFile (Some n, op, w) -> string_of_int n ^ print_op op ^ w
  | IoFile (None, op, w) -> print_op op ^ w
  | IoHere (Some n, op, w) -> string_of_int n ^ print_op op ^ w
  | IoHere (None, op, w) -> print_op op ^ w
  | Assignment s -> s
  | Simple (Some (cmd, args), redirects) -> cmd ^ " " ^ print_word_list args ^ print_redirects redirects
  | Simple (None, redirects) -> print_redirects redirects
  | Compound (cc, redirects) -> string_of_exp cc ^ print_redirects redirects
  | FunctionDef (name, body) -> name ^ "() {" ^ string_of_exp body ^ "}"
  | BraceGroup cmds -> "{" ^ print_exp_list cmds ^ "}"
  | Subshell cmds -> "(" ^ print_exp_list cmds ^ ")"
  | ForClause (var, Some wl, body) -> "for " ^ var ^ " in " ^ print_word_list wl ^ " do " ^ print_exp_list body ^ " done"
  | ForClause (var, None, body) -> "for " ^ var ^ " do " ^ print_exp_list body ^ " done"
  | CaseClause (w, cases) -> "case " ^ w ^ " in " ^ print_case_list cases ^ " esac"
  | IfClause (cond, then_part, elifs, else_part) -> "if " ^ print_exp_list cond ^ " then " ^ print_exp_list then_part ^ print_elif_list elifs ^ print_else_part else_part ^ " fi"
  | WhileClause (cond, body) -> "while " ^ print_exp_list cond ^ " do " ^ print_exp_list body ^ " done"
  | UntilClause (cond, body) -> "until " ^ print_exp_list cond ^ " do " ^ print_exp_list body ^ " done"
  | Pipeline (bang, cmds) -> (if bang then "! " else "") ^ String.concat " | " (List.map string_of_exp cmds)
  | AndIf (left, right) -> string_of_exp left ^ " && " ^ string_of_exp right
  | OrIf (left, right) -> string_of_exp left ^ " || " ^ string_of_exp right
  | List (left, sep, right) -> string_of_exp left ^ (match sep with Amp -> " &" | Semi -> " ;") ^ string_of_exp right
  | ListItem (ao, sep) -> string_of_exp ao ^ (match sep with Some Amp -> " &" | Some Semi -> " ;" | None -> "")
  | Program prog -> String.concat " " (List.map string_of_exp prog)
  | AndOr e -> string_of_exp e

and print_op = function
  | Less -> "<" | Great -> ">" | DGreat -> ">>" | LessAnd -> "<&" | GreatAnd -> ">&"
  | LessGreat -> "<>" | DLess -> "<<" | DLessDash -> "<<-" | Clobber -> ">|"

and print_word_list = function | [] -> "[]" | [w] -> w | w :: ws -> w ^ " " ^ print_word_list ws
and print_redirects redirects = String.concat "" (List.map (fun r -> " " ^ string_of_exp r) redirects)
and print_exp_list cmds = String.concat " " (List.map string_of_exp cmds)
and print_case_list cases = String.concat " " (List.map (fun (p, c) -> print_word_list p ^ ") " ^ print_exp_list c ^ " ;;") cases)
and print_elif_list elifs = String.concat " " (List.map (fun (cond, body) -> "elif " ^ print_exp_list cond ^ " then " ^ print_exp_list body) elifs)

and print_else_part = function
  | Some cmds -> " else " ^ print_exp_list cmds
  | None -> ""

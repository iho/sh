type word = string
type io_number = int

type redirect_op =
  | Less | Great | DGreat | LessAnd | GreatAnd | LessGreat
  | DLess | DLessDash | Clobber

type redirect =
  | IoFile of io_number option * redirect_op * word
  | IoHere of io_number option * redirect_op * word
  | Assignment of string

type command =
  | Simple of (word * word list) option * redirect list
  | Compound of compound_command * redirect list
  | FunctionDef of string * command

and compound_command =
  | BraceGroup of command list
  | Subshell of command list
  | ForClause of string * word list option * command list
  | CaseClause of word * (word list * command list) list
  | IfClause of command list * command list * (command list * command list) list * command list option
  | WhileClause of command list * command list
  | UntilClause of command list * command list

type pipeline = bool * command list
type and_or =
  | AndOr of pipeline
  | AndIf of and_or * pipeline
  | OrIf of and_or * pipeline
  | List of and_or * [`Amp | `Semi] * and_or

type list_item = and_or * [`Amp | `Semi] option
type program = list_item list

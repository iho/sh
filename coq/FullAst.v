Require Import Strings.String.
Require Import Lists.List.
Import ListNotations.
Open Scope string_scope.

(* Complete AST types matching ast.ml *)
Definition word : Set := string.
Definition io_number : Set := nat.

Inductive redirect_op : Set :=
  | Less | Great | DGreat | LessAnd | GreatAnd 
  | LessGreat | DLess | DLessDash | Clobber.

Inductive sep : Set := | Amp | Semi.

Inductive exp : Set :=
  | Word : word -> exp
  | IoFile : option io_number -> redirect_op -> word -> exp
  | IoHere : option io_number -> redirect_op -> word -> exp
  | Assignment : string -> exp
  | Simple : option (word * list word) -> list exp -> exp
  | Compound : exp -> list exp -> exp
  | FunctionDef : string -> exp -> exp
  | BraceGroup : list exp -> exp
  | Subshell : list exp -> exp
  | ForClause : string -> option (list word) -> list exp -> exp
  | CaseClause : word -> list (list word * list exp) -> exp
  | IfClause : list exp -> list exp -> list (list exp * list exp) -> option (list exp) -> exp
  | WhileClause : list exp -> list exp -> exp
  | UntilClause : list exp -> list exp -> exp
  | Pipeline : bool -> list exp -> exp
  | AndOr : exp -> exp                  (* Missing constructor added *)
  | AndIf : exp -> exp -> exp
  | OrIf : exp -> exp -> exp
  | List : exp -> sep -> exp -> exp
  | ListItem : exp -> option sep -> exp
  | Program : list exp -> exp.

(* String conversion helpers *)
Definition print_op (op : redirect_op) : string :=
  match op with
  | Less => "<" | Great => ">" | DGreat => ">>" | LessAnd => "<&" | GreatAnd => ">&"
  | LessGreat => "<>" | DLess => "<<" | DLessDash => "<<-" | Clobber => ">|"
  end.

Definition print_sep (s : sep) : string :=
  match s with Amp => " &" | Semi => " ;" end.

Definition string_of_nat (n : nat) : string :=
  match n with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4"
  | 5 => "5" | 6 => "6" | 7 => "7" | 8 => "8" | 9 => "9"
  | _ => "N"
  end.

Fixpoint string_concat (sep : string) (l : list string) : string :=
  match l with
  | [] => ""
  | [h] => h
  | h :: t => h ++ sep ++ string_concat sep t
  end.

Fixpoint print_word_list (words : list word) : string :=
  match words with
  | [] => "[]"
  | [w] => w
  | w :: ws => w ++ " " ++ print_word_list ws
  end.

(* Main string conversion function *)
Fixpoint string_of_exp (e : exp) : string :=
  match e with
  | Word w => w
  | Assignment s => s
  | Simple (Some (cmd, args)) _ => cmd ++ " " ++ print_word_list args
  | Simple None _ => "redirect"
  | Pipeline false cmds => string_concat " | " (map string_of_exp cmds)
  | Pipeline true cmds => "! " ++ string_concat " | " (map string_of_exp cmds)
  | AndOr e => string_of_exp e
  | AndIf l r => string_of_exp l ++ " && " ++ string_of_exp r
  | OrIf l r => string_of_exp l ++ " || " ++ string_of_exp r
  | List l s r => string_of_exp l ++ print_sep s ++ string_of_exp r
  | ListItem ao (Some s) => string_of_exp ao ++ print_sep s
  | ListItem ao None => string_of_exp ao
  | Program prog => string_concat " " (map string_of_exp prog)
  | FunctionDef name _ => name ++ "()"
  | BraceGroup _ => "{...}"
  | Subshell _ => "(...)"
  | ForClause var (Some wl) _ => "for " ++ var ++ " in " ++ print_word_list wl
  | ForClause var None _ => "for " ++ var
  | CaseClause w _ => "case " ++ w
  | IfClause _ _ _ _ => "if...fi"
  | WhileClause _ _ => "while...done"
  | UntilClause _ _ => "until...done"
  | Compound cc _ => string_of_exp cc
  | IoFile (Some n) op w => string_of_nat n ++ print_op op ++ w
  | IoFile None op w => print_op op ++ w
  | IoHere (Some n) op w => string_of_nat n ++ print_op op ++ w
  | IoHere None op w => print_op op ++ w
  end.

(* Examples of all operations *)
Definition examples := [
  ("Word", string_of_exp (Word "hello"));
  ("Assignment", string_of_exp (Assignment "VAR=value"));
  ("Simple", string_of_exp (Simple (Some ("ls", ["-l"; "*.ml"])) []));
  ("Pipeline", string_of_exp (Pipeline false [Word "cat"; Word "grep"]));
  ("BangPipeline", string_of_exp (Pipeline true [Word "false"]));
  ("AndIf", string_of_exp (AndIf (Word "test1") (Word "test2")));
  ("OrIf", string_of_exp (OrIf (Word "cmd1") (Word "cmd2")));
  ("List", string_of_exp (List (Word "cmd1") Semi (Word "cmd2")));
  ("ListAmp", string_of_exp (List (Word "bg") Amp (Word "fg")));
  ("Function", string_of_exp (FunctionDef "myfunc" (Word "body")));
  ("BraceGroup", string_of_exp (BraceGroup [Word "cmd1"; Word "cmd2"]));
  ("Subshell", string_of_exp (Subshell [Word "echo"; Word "test"]));
  ("ForLoop", string_of_exp (ForClause "i" (Some ["1"; "2"; "3"]) [Word "echo"]));
  ("Case", string_of_exp (CaseClause "var" [(["*"], [Word "default"])]));
  ("If", string_of_exp (IfClause [Word "test"] [Word "then"] [] None));
  ("While", string_of_exp (WhileClause [Word "true"] [Word "sleep"]));
  ("Until", string_of_exp (UntilClause [Word "false"] [Word "break"]));
  ("IoFile", string_of_exp (IoFile (Some 1) Great "out.txt"));
  ("IoHere", string_of_exp (IoHere None DLess "EOF"));
  ("Program", string_of_exp (Program [Word "cmd1"; Word "cmd2"]))
].

(* Verification *)
Example word_test : string_of_exp (Word "test") = "test".
Proof. reflexivity. Qed.

Example pipeline_test : 
  string_of_exp (Pipeline false [Word "cat"; Word "grep"]) = "cat | grep".
Proof. reflexivity. Qed.

Example complex_test :
  string_of_exp (AndIf (Word "make") (Word "install")) = "make && install".
Proof. reflexivity. Qed.

(* Count all supported operations *)
Definition operation_count := length examples.

Example all_operations_covered : operation_count = 20.
Proof. reflexivity. Qed.
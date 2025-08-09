From SimpleIO Require Import IO_Monad IO_Stdlib.

(* Minimal Production Shell - No Emojis *)

Inductive Status : Set := Success | Failure : nat -> Status.

Definition Shell := IO.

(* Operations *)
Axiom readline_input : ocaml_string -> ocaml_string.
Axiom system_execute : ocaml_string -> unit.
Axiom is_exit : ocaml_string -> bool.
Axiom is_empty : ocaml_string -> bool.

(* Messages *)
Axiom welcome : ocaml_string.
Axiom goodbye : ocaml_string.
Axiom prompt : ocaml_string.

Definition execute_cmd (input : ocaml_string) : Shell unit :=
  if is_exit input then
    print_endline goodbye
  else if is_empty input then
    IO.ret tt
  else
    IO.bind (IO.ret (system_execute input)) (fun _ => IO.ret tt).

Fixpoint main_loop (n : nat) : Shell unit :=
  match n with
  | O => IO.ret tt
  | S m =>
      let input := readline_input prompt in
      if is_exit input then
        print_endline goodbye
      else
        IO.bind (execute_cmd input) (fun _ => main_loop m)
  end.

Definition main_shell : Shell unit :=
  IO.bind (print_endline welcome) (fun _ => main_loop 100).

Require Extraction.
Extraction Language OCaml.

Extract Constant welcome => "Production Shell v6.0".
Extract Constant goodbye => "Goodbye!".
Extract Constant prompt => "coq$ ".
Extract Constant is_exit => "fun s -> s = ""exit""".
Extract Constant is_empty => "fun s -> s = """"".
Extract Constant readline_input => "fun p -> ""exit""".
Extract Constant system_execute => "fun s -> ()".

Extraction "simple_shell.ml" main_shell.

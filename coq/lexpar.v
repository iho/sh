  
Require Import FullAst.
Require Import String.
Require Import List.
Import ListNotations.


From Coq.extraction Require Extraction.
From Coq.Lists Require List.
From Coq.PArith Require Import BinPos.
From Coq.NArith Require Import BinNat.
From MenhirLib Require Main.
Import List.ListNotations.

Unset Elimination Schemes.

Inductive token : Type :=
| WORD :        (string)%type -> token
| WHILE_TOK : unit%type -> token
| UNTIL_TOK : unit%type -> token
| THEN_TOK : unit%type -> token
| SEMI : unit%type -> token
| RPAREN : unit%type -> token
| RBRACE : unit%type -> token
| PIPE : unit%type -> token
| OR_IF : unit%type -> token
| NEWLINE : unit%type -> token
| NAME :        (string)%type -> token
| LPAREN : unit%type -> token
| LESSGREAT : unit%type -> token
| LESSAND : unit%type -> token
| LESS : unit%type -> token
| LBRACE : unit%type -> token
| IO_NUMBER :        (nat)%type -> token
| IN_TOK : unit%type -> token
| IF_TOK : unit%type -> token
| GREATAND : unit%type -> token
| GREAT : unit%type -> token
| FOR_TOK : unit%type -> token
| FI_TOK : unit%type -> token
| ESAC_TOK : unit%type -> token
| EOF_TOK : unit%type -> token
| ELSE_TOK : unit%type -> token
| ELIF_TOK : unit%type -> token
| DSEMI : unit%type -> token
| DO_TOK : unit%type -> token
| DONE_TOK : unit%type -> token
| DLESSDASH : unit%type -> token
| DLESS : unit%type -> token
| DGREAT : unit%type -> token
| CLOBBER : unit%type -> token
| CASE_TOK : unit%type -> token
| BANG : unit%type -> token
| ASSIGNMENT_WORD :        (string)%type -> token
| AND_IF : unit%type -> token
| AMP : unit%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
| AMP't
| AND_IF't
| ASSIGNMENT_WORD't
| BANG't
| CASE_TOK't
| CLOBBER't
| DGREAT't
| DLESS't
| DLESSDASH't
| DONE_TOK't
| DO_TOK't
| DSEMI't
| ELIF_TOK't
| ELSE_TOK't
| EOF_TOK't
| ESAC_TOK't
| FI_TOK't
| FOR_TOK't
| GREAT't
| GREATAND't
| IF_TOK't
| IN_TOK't
| IO_NUMBER't
| LBRACE't
| LESS't
| LESSAND't
| LESSGREAT't
| LPAREN't
| NAME't
| NEWLINE't
| OR_IF't
| PIPE't
| RBRACE't
| RPAREN't
| SEMI't
| THEN_TOK't
| UNTIL_TOK't
| WHILE_TOK't
| WORD't.
Definition terminal := terminal'.

Global Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | AMP't => 1%positive
    | AND_IF't => 2%positive
    | ASSIGNMENT_WORD't => 3%positive
    | BANG't => 4%positive
    | CASE_TOK't => 5%positive
    | CLOBBER't => 6%positive
    | DGREAT't => 7%positive
    | DLESS't => 8%positive
    | DLESSDASH't => 9%positive
    | DONE_TOK't => 10%positive
    | DO_TOK't => 11%positive
    | DSEMI't => 12%positive
    | ELIF_TOK't => 13%positive
    | ELSE_TOK't => 14%positive
    | EOF_TOK't => 15%positive
    | ESAC_TOK't => 16%positive
    | FI_TOK't => 17%positive
    | FOR_TOK't => 18%positive
    | GREAT't => 19%positive
    | GREATAND't => 20%positive
    | IF_TOK't => 21%positive
    | IN_TOK't => 22%positive
    | IO_NUMBER't => 23%positive
    | LBRACE't => 24%positive
    | LESS't => 25%positive
    | LESSAND't => 26%positive
    | LESSGREAT't => 27%positive
    | LPAREN't => 28%positive
    | NAME't => 29%positive
    | NEWLINE't => 30%positive
    | OR_IF't => 31%positive
    | PIPE't => 32%positive
    | RBRACE't => 33%positive
    | RPAREN't => 34%positive
    | SEMI't => 35%positive
    | THEN_TOK't => 36%positive
    | UNTIL_TOK't => 37%positive
    | WHILE_TOK't => 38%positive
    | WORD't => 39%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => AMP't
    | 2%positive => AND_IF't
    | 3%positive => ASSIGNMENT_WORD't
    | 4%positive => BANG't
    | 5%positive => CASE_TOK't
    | 6%positive => CLOBBER't
    | 7%positive => DGREAT't
    | 8%positive => DLESS't
    | 9%positive => DLESSDASH't
    | 10%positive => DONE_TOK't
    | 11%positive => DO_TOK't
    | 12%positive => DSEMI't
    | 13%positive => ELIF_TOK't
    | 14%positive => ELSE_TOK't
    | 15%positive => EOF_TOK't
    | 16%positive => ESAC_TOK't
    | 17%positive => FI_TOK't
    | 18%positive => FOR_TOK't
    | 19%positive => GREAT't
    | 20%positive => GREATAND't
    | 21%positive => IF_TOK't
    | 22%positive => IN_TOK't
    | 23%positive => IO_NUMBER't
    | 24%positive => LBRACE't
    | 25%positive => LESS't
    | 26%positive => LESSAND't
    | 27%positive => LESSGREAT't
    | 28%positive => LPAREN't
    | 29%positive => NAME't
    | 30%positive => NEWLINE't
    | 31%positive => OR_IF't
    | 32%positive => PIPE't
    | 33%positive => RBRACE't
    | 34%positive => RPAREN't
    | 35%positive => SEMI't
    | 36%positive => THEN_TOK't
    | 37%positive => UNTIL_TOK't
    | 38%positive => WHILE_TOK't
    | 39%positive => WORD't
    | _ => AMP't
    end)%Z;
    inj_bound := 39%positive }.
Global Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| and_or'nt
| brace_group'nt
| case_clause'nt
| case_item'nt
| case_list'nt
| clist'nt
| command'nt
| compound'nt
| do_group'nt
| else_part'nt
| for_clause'nt
| function_body'nt
| function_def'nt
| if_clause'nt
| io_redirect'nt
| list'nt
| pattern'nt
| pipe_sequence'nt
| prefix'nt
| program'nt
| rlist'nt
| scmd'nt
| separator'nt
| subshell'nt
| suffix'nt
| term'nt
| until_clause'nt
| while_clause'nt
| wlist'nt.
Definition nonterminal := nonterminal'.

Global Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | and_or'nt => 1%positive
    | brace_group'nt => 2%positive
    | case_clause'nt => 3%positive
    | case_item'nt => 4%positive
    | case_list'nt => 5%positive
    | clist'nt => 6%positive
    | command'nt => 7%positive
    | compound'nt => 8%positive
    | do_group'nt => 9%positive
    | else_part'nt => 10%positive
    | for_clause'nt => 11%positive
    | function_body'nt => 12%positive
    | function_def'nt => 13%positive
    | if_clause'nt => 14%positive
    | io_redirect'nt => 15%positive
    | list'nt => 16%positive
    | pattern'nt => 17%positive
    | pipe_sequence'nt => 18%positive
    | prefix'nt => 19%positive
    | program'nt => 20%positive
    | rlist'nt => 21%positive
    | scmd'nt => 22%positive
    | separator'nt => 23%positive
    | subshell'nt => 24%positive
    | suffix'nt => 25%positive
    | term'nt => 26%positive
    | until_clause'nt => 27%positive
    | while_clause'nt => 28%positive
    | wlist'nt => 29%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => and_or'nt
    | 2%positive => brace_group'nt
    | 3%positive => case_clause'nt
    | 4%positive => case_item'nt
    | 5%positive => case_list'nt
    | 6%positive => clist'nt
    | 7%positive => command'nt
    | 8%positive => compound'nt
    | 9%positive => do_group'nt
    | 10%positive => else_part'nt
    | 11%positive => for_clause'nt
    | 12%positive => function_body'nt
    | 13%positive => function_def'nt
    | 14%positive => if_clause'nt
    | 15%positive => io_redirect'nt
    | 16%positive => list'nt
    | 17%positive => pattern'nt
    | 18%positive => pipe_sequence'nt
    | 19%positive => prefix'nt
    | 20%positive => program'nt
    | 21%positive => rlist'nt
    | 22%positive => scmd'nt
    | 23%positive => separator'nt
    | 24%positive => subshell'nt
    | 25%positive => suffix'nt
    | 26%positive => term'nt
    | 27%positive => until_clause'nt
    | 28%positive => while_clause'nt
    | 29%positive => wlist'nt
    | _ => and_or'nt
    end)%Z;
    inj_bound := 29%positive }.
Global Instance NonTerminalAlph : MenhirLib.Alphabet.Alphabet nonterminal := _.

Include MenhirLib.Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | WORD't =>        (string)%type
  | WHILE_TOK't => unit%type
  | UNTIL_TOK't => unit%type
  | THEN_TOK't => unit%type
  | SEMI't => unit%type
  | RPAREN't => unit%type
  | RBRACE't => unit%type
  | PIPE't => unit%type
  | OR_IF't => unit%type
  | NEWLINE't => unit%type
  | NAME't =>        (string)%type
  | LPAREN't => unit%type
  | LESSGREAT't => unit%type
  | LESSAND't => unit%type
  | LESS't => unit%type
  | LBRACE't => unit%type
  | IO_NUMBER't =>        (nat)%type
  | IN_TOK't => unit%type
  | IF_TOK't => unit%type
  | GREATAND't => unit%type
  | GREAT't => unit%type
  | FOR_TOK't => unit%type
  | FI_TOK't => unit%type
  | ESAC_TOK't => unit%type
  | EOF_TOK't => unit%type
  | ELSE_TOK't => unit%type
  | ELIF_TOK't => unit%type
  | DSEMI't => unit%type
  | DO_TOK't => unit%type
  | DONE_TOK't => unit%type
  | DLESSDASH't => unit%type
  | DLESS't => unit%type
  | DGREAT't => unit%type
  | CLOBBER't => unit%type
  | CASE_TOK't => unit%type
  | BANG't => unit%type
  | ASSIGNMENT_WORD't =>        (string)%type
  | AND_IF't => unit%type
  | AMP't => unit%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | wlist'nt =>       (list string)%type
  | while_clause'nt =>       (FullAst.exp)%type
  | until_clause'nt =>       (FullAst.exp)%type
  | term'nt =>       (list FullAst.exp)%type
  | suffix'nt =>       (list FullAst.exp)%type
  | subshell'nt =>       (FullAst.exp)%type
  | separator'nt =>       (FullAst.sep)%type
  | scmd'nt =>       (option (string * list string))%type
  | rlist'nt =>       (list FullAst.exp)%type
  | program'nt =>        (FullAst.exp)%type
  | prefix'nt =>       (list FullAst.exp)%type
  | pipe_sequence'nt =>       (list FullAst.exp)%type
  | pattern'nt =>       (list string)%type
  | list'nt =>       (FullAst.exp)%type
  | io_redirect'nt =>       (FullAst.exp)%type
  | if_clause'nt =>       (FullAst.exp)%type
  | function_def'nt =>       (FullAst.exp)%type
  | function_body'nt =>       (FullAst.exp)%type
  | for_clause'nt =>       (FullAst.exp)%type
  | else_part'nt =>       (list (list FullAst.exp * list FullAst.exp))%type
  | do_group'nt =>       (list FullAst.exp)%type
  | compound'nt =>       (FullAst.exp)%type
  | command'nt =>       (FullAst.exp)%type
  | clist'nt =>       (list FullAst.exp)%type
  | case_list'nt =>       (list (list string * list FullAst.exp))%type
  | case_item'nt =>       (list string * list FullAst.exp)%type
  | case_clause'nt =>       (FullAst.exp)%type
  | brace_group'nt =>       (FullAst.exp)%type
  | and_or'nt =>       (FullAst.exp)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Definition token := token.

Definition token_term (tok : token) : terminal :=
  match tok with
  | WORD _ => WORD't
  | WHILE_TOK _ => WHILE_TOK't
  | UNTIL_TOK _ => UNTIL_TOK't
  | THEN_TOK _ => THEN_TOK't
  | SEMI _ => SEMI't
  | RPAREN _ => RPAREN't
  | RBRACE _ => RBRACE't
  | PIPE _ => PIPE't
  | OR_IF _ => OR_IF't
  | NEWLINE _ => NEWLINE't
  | NAME _ => NAME't
  | LPAREN _ => LPAREN't
  | LESSGREAT _ => LESSGREAT't
  | LESSAND _ => LESSAND't
  | LESS _ => LESS't
  | LBRACE _ => LBRACE't
  | IO_NUMBER _ => IO_NUMBER't
  | IN_TOK _ => IN_TOK't
  | IF_TOK _ => IF_TOK't
  | GREATAND _ => GREATAND't
  | GREAT _ => GREAT't
  | FOR_TOK _ => FOR_TOK't
  | FI_TOK _ => FI_TOK't
  | ESAC_TOK _ => ESAC_TOK't
  | EOF_TOK _ => EOF_TOK't
  | ELSE_TOK _ => ELSE_TOK't
  | ELIF_TOK _ => ELIF_TOK't
  | DSEMI _ => DSEMI't
  | DO_TOK _ => DO_TOK't
  | DONE_TOK _ => DONE_TOK't
  | DLESSDASH _ => DLESSDASH't
  | DLESS _ => DLESS't
  | DGREAT _ => DGREAT't
  | CLOBBER _ => CLOBBER't
  | CASE_TOK _ => CASE_TOK't
  | BANG _ => BANG't
  | ASSIGNMENT_WORD _ => ASSIGNMENT_WORD't
  | AND_IF _ => AND_IF't
  | AMP _ => AMP't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | WORD x => x
  | WHILE_TOK x => x
  | UNTIL_TOK x => x
  | THEN_TOK x => x
  | SEMI x => x
  | RPAREN x => x
  | RBRACE x => x
  | PIPE x => x
  | OR_IF x => x
  | NEWLINE x => x
  | NAME x => x
  | LPAREN x => x
  | LESSGREAT x => x
  | LESSAND x => x
  | LESS x => x
  | LBRACE x => x
  | IO_NUMBER x => x
  | IN_TOK x => x
  | IF_TOK x => x
  | GREATAND x => x
  | GREAT x => x
  | FOR_TOK x => x
  | FI_TOK x => x
  | ESAC_TOK x => x
  | EOF_TOK x => x
  | ELSE_TOK x => x
  | ELIF_TOK x => x
  | DSEMI x => x
  | DO_TOK x => x
  | DONE_TOK x => x
  | DLESSDASH x => x
  | DLESS x => x
  | DGREAT x => x
  | CLOBBER x => x
  | CASE_TOK x => x
  | BANG x => x
  | ASSIGNMENT_WORD x => x
  | AND_IF x => x
  | AMP x => x
  end.

Inductive production' : Set :=
| Prod'wlist'1
| Prod'wlist'0
| Prod'while_clause'0
| Prod'until_clause'0
| Prod'term'1
| Prod'term'0
| Prod'suffix'5
| Prod'suffix'4
| Prod'suffix'3
| Prod'suffix'2
| Prod'suffix'1
| Prod'suffix'0
| Prod'subshell'0
| Prod'separator'1
| Prod'separator'0
| Prod'scmd'4
| Prod'scmd'3
| Prod'scmd'2
| Prod'scmd'1
| Prod'scmd'0
| Prod'rlist'1
| Prod'rlist'0
| Prod'program'0
| Prod'prefix'3
| Prod'prefix'2
| Prod'prefix'1
| Prod'prefix'0
| Prod'pipe_sequence'1
| Prod'pipe_sequence'0
| Prod'pattern'1
| Prod'pattern'0
| Prod'list'1
| Prod'list'0
| Prod'io_redirect'17
| Prod'io_redirect'16
| Prod'io_redirect'15
| Prod'io_redirect'14
| Prod'io_redirect'13
| Prod'io_redirect'12
| Prod'io_redirect'11
| Prod'io_redirect'10
| Prod'io_redirect'9
| Prod'io_redirect'8
| Prod'io_redirect'7
| Prod'io_redirect'6
| Prod'io_redirect'5
| Prod'io_redirect'4
| Prod'io_redirect'3
| Prod'io_redirect'2
| Prod'io_redirect'1
| Prod'io_redirect'0
| Prod'if_clause'1
| Prod'if_clause'0
| Prod'function_def'0
| Prod'function_body'1
| Prod'function_body'0
| Prod'for_clause'1
| Prod'for_clause'0
| Prod'else_part'2
| Prod'else_part'1
| Prod'else_part'0
| Prod'do_group'0
| Prod'compound'6
| Prod'compound'5
| Prod'compound'4
| Prod'compound'3
| Prod'compound'2
| Prod'compound'1
| Prod'compound'0
| Prod'command'3
| Prod'command'2
| Prod'command'1
| Prod'command'0
| Prod'clist'2
| Prod'clist'1
| Prod'clist'0
| Prod'case_list'1
| Prod'case_list'0
| Prod'case_item'1
| Prod'case_item'0
| Prod'case_clause'1
| Prod'case_clause'0
| Prod'brace_group'0
| Prod'and_or'3
| Prod'and_or'2
| Prod'and_or'1
| Prod'and_or'0.
Definition production := production'.

Global Program Instance productionNum : MenhirLib.Alphabet.Numbered production :=
  { inj := fun x => match x return _ with
    | Prod'wlist'1 => 1%positive
    | Prod'wlist'0 => 2%positive
    | Prod'while_clause'0 => 3%positive
    | Prod'until_clause'0 => 4%positive
    | Prod'term'1 => 5%positive
    | Prod'term'0 => 6%positive
    | Prod'suffix'5 => 7%positive
    | Prod'suffix'4 => 8%positive
    | Prod'suffix'3 => 9%positive
    | Prod'suffix'2 => 10%positive
    | Prod'suffix'1 => 11%positive
    | Prod'suffix'0 => 12%positive
    | Prod'subshell'0 => 13%positive
    | Prod'separator'1 => 14%positive
    | Prod'separator'0 => 15%positive
    | Prod'scmd'4 => 16%positive
    | Prod'scmd'3 => 17%positive
    | Prod'scmd'2 => 18%positive
    | Prod'scmd'1 => 19%positive
    | Prod'scmd'0 => 20%positive
    | Prod'rlist'1 => 21%positive
    | Prod'rlist'0 => 22%positive
    | Prod'program'0 => 23%positive
    | Prod'prefix'3 => 24%positive
    | Prod'prefix'2 => 25%positive
    | Prod'prefix'1 => 26%positive
    | Prod'prefix'0 => 27%positive
    | Prod'pipe_sequence'1 => 28%positive
    | Prod'pipe_sequence'0 => 29%positive
    | Prod'pattern'1 => 30%positive
    | Prod'pattern'0 => 31%positive
    | Prod'list'1 => 32%positive
    | Prod'list'0 => 33%positive
    | Prod'io_redirect'17 => 34%positive
    | Prod'io_redirect'16 => 35%positive
    | Prod'io_redirect'15 => 36%positive
    | Prod'io_redirect'14 => 37%positive
    | Prod'io_redirect'13 => 38%positive
    | Prod'io_redirect'12 => 39%positive
    | Prod'io_redirect'11 => 40%positive
    | Prod'io_redirect'10 => 41%positive
    | Prod'io_redirect'9 => 42%positive
    | Prod'io_redirect'8 => 43%positive
    | Prod'io_redirect'7 => 44%positive
    | Prod'io_redirect'6 => 45%positive
    | Prod'io_redirect'5 => 46%positive
    | Prod'io_redirect'4 => 47%positive
    | Prod'io_redirect'3 => 48%positive
    | Prod'io_redirect'2 => 49%positive
    | Prod'io_redirect'1 => 50%positive
    | Prod'io_redirect'0 => 51%positive
    | Prod'if_clause'1 => 52%positive
    | Prod'if_clause'0 => 53%positive
    | Prod'function_def'0 => 54%positive
    | Prod'function_body'1 => 55%positive
    | Prod'function_body'0 => 56%positive
    | Prod'for_clause'1 => 57%positive
    | Prod'for_clause'0 => 58%positive
    | Prod'else_part'2 => 59%positive
    | Prod'else_part'1 => 60%positive
    | Prod'else_part'0 => 61%positive
    | Prod'do_group'0 => 62%positive
    | Prod'compound'6 => 63%positive
    | Prod'compound'5 => 64%positive
    | Prod'compound'4 => 65%positive
    | Prod'compound'3 => 66%positive
    | Prod'compound'2 => 67%positive
    | Prod'compound'1 => 68%positive
    | Prod'compound'0 => 69%positive
    | Prod'command'3 => 70%positive
    | Prod'command'2 => 71%positive
    | Prod'command'1 => 72%positive
    | Prod'command'0 => 73%positive
    | Prod'clist'2 => 74%positive
    | Prod'clist'1 => 75%positive
    | Prod'clist'0 => 76%positive
    | Prod'case_list'1 => 77%positive
    | Prod'case_list'0 => 78%positive
    | Prod'case_item'1 => 79%positive
    | Prod'case_item'0 => 80%positive
    | Prod'case_clause'1 => 81%positive
    | Prod'case_clause'0 => 82%positive
    | Prod'brace_group'0 => 83%positive
    | Prod'and_or'3 => 84%positive
    | Prod'and_or'2 => 85%positive
    | Prod'and_or'1 => 86%positive
    | Prod'and_or'0 => 87%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'wlist'1
    | 2%positive => Prod'wlist'0
    | 3%positive => Prod'while_clause'0
    | 4%positive => Prod'until_clause'0
    | 5%positive => Prod'term'1
    | 6%positive => Prod'term'0
    | 7%positive => Prod'suffix'5
    | 8%positive => Prod'suffix'4
    | 9%positive => Prod'suffix'3
    | 10%positive => Prod'suffix'2
    | 11%positive => Prod'suffix'1
    | 12%positive => Prod'suffix'0
    | 13%positive => Prod'subshell'0
    | 14%positive => Prod'separator'1
    | 15%positive => Prod'separator'0
    | 16%positive => Prod'scmd'4
    | 17%positive => Prod'scmd'3
    | 18%positive => Prod'scmd'2
    | 19%positive => Prod'scmd'1
    | 20%positive => Prod'scmd'0
    | 21%positive => Prod'rlist'1
    | 22%positive => Prod'rlist'0
    | 23%positive => Prod'program'0
    | 24%positive => Prod'prefix'3
    | 25%positive => Prod'prefix'2
    | 26%positive => Prod'prefix'1
    | 27%positive => Prod'prefix'0
    | 28%positive => Prod'pipe_sequence'1
    | 29%positive => Prod'pipe_sequence'0
    | 30%positive => Prod'pattern'1
    | 31%positive => Prod'pattern'0
    | 32%positive => Prod'list'1
    | 33%positive => Prod'list'0
    | 34%positive => Prod'io_redirect'17
    | 35%positive => Prod'io_redirect'16
    | 36%positive => Prod'io_redirect'15
    | 37%positive => Prod'io_redirect'14
    | 38%positive => Prod'io_redirect'13
    | 39%positive => Prod'io_redirect'12
    | 40%positive => Prod'io_redirect'11
    | 41%positive => Prod'io_redirect'10
    | 42%positive => Prod'io_redirect'9
    | 43%positive => Prod'io_redirect'8
    | 44%positive => Prod'io_redirect'7
    | 45%positive => Prod'io_redirect'6
    | 46%positive => Prod'io_redirect'5
    | 47%positive => Prod'io_redirect'4
    | 48%positive => Prod'io_redirect'3
    | 49%positive => Prod'io_redirect'2
    | 50%positive => Prod'io_redirect'1
    | 51%positive => Prod'io_redirect'0
    | 52%positive => Prod'if_clause'1
    | 53%positive => Prod'if_clause'0
    | 54%positive => Prod'function_def'0
    | 55%positive => Prod'function_body'1
    | 56%positive => Prod'function_body'0
    | 57%positive => Prod'for_clause'1
    | 58%positive => Prod'for_clause'0
    | 59%positive => Prod'else_part'2
    | 60%positive => Prod'else_part'1
    | 61%positive => Prod'else_part'0
    | 62%positive => Prod'do_group'0
    | 63%positive => Prod'compound'6
    | 64%positive => Prod'compound'5
    | 65%positive => Prod'compound'4
    | 66%positive => Prod'compound'3
    | 67%positive => Prod'compound'2
    | 68%positive => Prod'compound'1
    | 69%positive => Prod'compound'0
    | 70%positive => Prod'command'3
    | 71%positive => Prod'command'2
    | 72%positive => Prod'command'1
    | 73%positive => Prod'command'0
    | 74%positive => Prod'clist'2
    | 75%positive => Prod'clist'1
    | 76%positive => Prod'clist'0
    | 77%positive => Prod'case_list'1
    | 78%positive => Prod'case_list'0
    | 79%positive => Prod'case_item'1
    | 80%positive => Prod'case_item'0
    | 81%positive => Prod'case_clause'1
    | 82%positive => Prod'case_clause'0
    | 83%positive => Prod'brace_group'0
    | 84%positive => Prod'and_or'3
    | 85%positive => Prod'and_or'2
    | 86%positive => Prod'and_or'1
    | 87%positive => Prod'and_or'0
    | _ => Prod'wlist'1
    end)%Z;
    inj_bound := 87%positive }.
Global Instance ProductionAlph : MenhirLib.Alphabet.Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) }
 :=
  let box := existT (fun p =>
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) )
  in
  match p with
  | Prod'and_or'0 => box
    (and_or'nt, [NT pipe_sequence'nt]%list)
    (fun _1 =>
                                                   ( Pipeline false _1 )
)
  | Prod'and_or'1 => box
    (and_or'nt, [NT pipe_sequence'nt; T BANG't]%list)
    (fun _2 _1 =>
                                                   ( Pipeline true _2 )
)
  | Prod'and_or'2 => box
    (and_or'nt, [NT and_or'nt; T AND_IF't; NT and_or'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( AndIf _1 _3 )
)
  | Prod'and_or'3 => box
    (and_or'nt, [NT and_or'nt; T OR_IF't; NT and_or'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( OrIf _1 _3 )
)
  | Prod'brace_group'0 => box
    (brace_group'nt, [T RBRACE't; NT clist'nt; T LBRACE't]%list)
    (fun _3 _2 _1 =>
                                                   ( BraceGroup _2 )
)
  | Prod'case_clause'0 => box
    (case_clause'nt, [T ESAC_TOK't; NT case_list'nt; T IN_TOK't; T WORD't; T CASE_TOK't]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                               ( CaseClause _2 _4 )
)
  | Prod'case_clause'1 => box
    (case_clause'nt, [T ESAC_TOK't; T IN_TOK't; T WORD't; T CASE_TOK't]%list)
    (fun _4 _3 _2 _1 =>
                                                               ( CaseClause _2 [] )
)
  | Prod'case_item'0 => box
    (case_item'nt, [T DSEMI't; NT clist'nt; T RPAREN't; NT pattern'nt]%list)
    (fun _4 _3 _2 _1 =>
                                                   ( (_1, _3) )
)
  | Prod'case_item'1 => box
    (case_item'nt, [T DSEMI't; NT clist'nt; T RPAREN't; NT pattern'nt; T LPAREN't]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                   ( (_2, []) )
)
  | Prod'case_list'0 => box
    (case_list'nt, [NT case_list'nt; NT case_item'nt]%list)
    (fun _2 _1 =>
                                                   ( _1 :: _2 )
)
  | Prod'case_list'1 => box
    (case_list'nt, [NT case_item'nt]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'clist'0 => box
    (clist'nt, [NT term'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'clist'1 => box
    (clist'nt, [T SEMI't; NT term'nt]%list)
    (fun _2 _1 =>
                                                   ( _1 )
)
  | Prod'clist'2 => box
    (clist'nt, [NT clist'nt; T SEMI't; NT term'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( _1 )
)
  | Prod'command'0 => box
    (command'nt, [NT scmd'nt]%list)
    (fun _1 =>
                                                   ( Simple _1 [] )
)
  | Prod'command'1 => box
    (command'nt, [NT compound'nt]%list)
    (fun _1 =>
                                                   ( Compound _1 [] )
)
  | Prod'command'2 => box
    (command'nt, [NT rlist'nt; NT compound'nt]%list)
    (fun _2 _1 =>
                                                   ( Compound _1 _2 )
)
  | Prod'command'3 => box
    (command'nt, [NT function_def'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'0 => box
    (compound'nt, [NT brace_group'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'1 => box
    (compound'nt, [NT subshell'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'2 => box
    (compound'nt, [NT for_clause'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'3 => box
    (compound'nt, [NT case_clause'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'4 => box
    (compound'nt, [NT if_clause'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'5 => box
    (compound'nt, [NT while_clause'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'compound'6 => box
    (compound'nt, [NT until_clause'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'do_group'0 => box
    (do_group'nt, [T DONE_TOK't; NT clist'nt; T DO_TOK't]%list)
    (fun _3 _2 _1 =>
                                                           ( _2 )
)
  | Prod'else_part'0 => box
    (else_part'nt, [NT clist'nt; T ELSE_TOK't]%list)
    (fun _2 _1 =>
                                                       ( [] )
)
  | Prod'else_part'1 => box
    (else_part'nt, [NT clist'nt; T THEN_TOK't; NT clist'nt; T ELIF_TOK't]%list)
    (fun _4 _3 _2 _1 =>
                                                           ( [(_2, _4)] )
)
  | Prod'else_part'2 => box
    (else_part'nt, [NT else_part'nt; NT clist'nt; T THEN_TOK't; NT clist'nt; T ELIF_TOK't]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                           ( (_2, _4) :: _5 )
)
  | Prod'for_clause'0 => box
    (for_clause'nt, [NT do_group'nt; T SEMI't; NT wlist'nt; T IN_TOK't; T NAME't; T FOR_TOK't]%list)
    (fun _6 _5 _4 _3 _2 _1 =>
                                                           ( ForClause _2 (Some _4) _6 )
)
  | Prod'for_clause'1 => box
    (for_clause'nt, [NT do_group'nt; T NAME't; T FOR_TOK't]%list)
    (fun _3 _2 _1 =>
                                                       ( ForClause _2 None _3 )
)
  | Prod'function_body'0 => box
    (function_body'nt, [NT compound'nt]%list)
    (fun _1 =>
                                                   ( Compound _1 [] )
)
  | Prod'function_body'1 => box
    (function_body'nt, [NT rlist'nt; NT compound'nt]%list)
    (fun _2 _1 =>
                                                   ( Compound _1 _2 )
)
  | Prod'function_def'0 => box
    (function_def'nt, [NT function_body'nt; T RPAREN't; T LPAREN't; T NAME't]%list)
    (fun _4 _3 _2 _1 =>
                                                   ( FunctionDef _1 _4 )
)
  | Prod'if_clause'0 => box
    (if_clause'nt, [T FI_TOK't; NT clist'nt; T THEN_TOK't; NT clist'nt; T IF_TOK't]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                               ( IfClause _2 _4 [] None )
)
  | Prod'if_clause'1 => box
    (if_clause'nt, [T FI_TOK't; NT else_part'nt; NT clist'nt; T THEN_TOK't; NT clist'nt; T IF_TOK't]%list)
    (fun _6 _5 _4 _3 _2 _1 =>
                                                               ( IfClause _2 _4 _5 None )
)
  | Prod'io_redirect'0 => box
    (io_redirect'nt, [T WORD't; T LESS't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None Less _2 )
)
  | Prod'io_redirect'1 => box
    (io_redirect'nt, [T WORD't; T GREAT't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None Great _2 )
)
  | Prod'io_redirect'2 => box
    (io_redirect'nt, [T WORD't; T DGREAT't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None DGreat _2 )
)
  | Prod'io_redirect'3 => box
    (io_redirect'nt, [T WORD't; T LESSAND't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None LessAnd _2 )
)
  | Prod'io_redirect'4 => box
    (io_redirect'nt, [T WORD't; T GREATAND't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None GreatAnd _2 )
)
  | Prod'io_redirect'5 => box
    (io_redirect'nt, [T WORD't; T LESSGREAT't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None LessGreat _2 )
)
  | Prod'io_redirect'6 => box
    (io_redirect'nt, [T WORD't; T CLOBBER't]%list)
    (fun _2 _1 =>
                                                   ( IoFile None Clobber _2 )
)
  | Prod'io_redirect'7 => box
    (io_redirect'nt, [T WORD't; T DLESS't]%list)
    (fun _2 _1 =>
                                                   ( IoHere None DLess _2 )
)
  | Prod'io_redirect'8 => box
    (io_redirect'nt, [T WORD't; T DLESSDASH't]%list)
    (fun _2 _1 =>
                                                   ( IoHere None DLessDash _2 )
)
  | Prod'io_redirect'9 => box
    (io_redirect'nt, [T WORD't; T LESS't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) Less _3 )
)
  | Prod'io_redirect'10 => box
    (io_redirect'nt, [T WORD't; T GREAT't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) Great _3 )
)
  | Prod'io_redirect'11 => box
    (io_redirect'nt, [T WORD't; T DGREAT't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) DGreat _3 )
)
  | Prod'io_redirect'12 => box
    (io_redirect'nt, [T WORD't; T LESSAND't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) LessAnd _3 )
)
  | Prod'io_redirect'13 => box
    (io_redirect'nt, [T WORD't; T GREATAND't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) GreatAnd _3 )
)
  | Prod'io_redirect'14 => box
    (io_redirect'nt, [T WORD't; T LESSGREAT't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) LessGreat _3 )
)
  | Prod'io_redirect'15 => box
    (io_redirect'nt, [T WORD't; T CLOBBER't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoFile (Some _1) Clobber _3 )
)
  | Prod'io_redirect'16 => box
    (io_redirect'nt, [T WORD't; T DLESS't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoHere (Some _1) DLess _3 )
)
  | Prod'io_redirect'17 => box
    (io_redirect'nt, [T WORD't; T DLESSDASH't; T IO_NUMBER't]%list)
    (fun _3 _2 _1 =>
                                                   ( IoHere (Some _1) DLessDash _3 )
)
  | Prod'list'0 => box
    (list'nt, [NT and_or'nt; NT separator'nt; NT list'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( List _1 _2 _3 )
)
  | Prod'list'1 => box
    (list'nt, [NT and_or'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'pattern'0 => box
    (pattern'nt, [T WORD't]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'pattern'1 => box
    (pattern'nt, [NT pattern'nt; T WORD't]%list)
    (fun _2 _1 =>
                                                   ( _1 :: _2 )
)
  | Prod'pipe_sequence'0 => box
    (pipe_sequence'nt, [NT command'nt]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'pipe_sequence'1 => box
    (pipe_sequence'nt, [NT command'nt; T PIPE't; NT pipe_sequence'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( _3 :: _1 )
)
  | Prod'prefix'0 => box
    (prefix'nt, [NT io_redirect'nt]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'prefix'1 => box
    (prefix'nt, [NT io_redirect'nt; NT prefix'nt]%list)
    (fun _2 _1 =>
                                                   ( _2 :: _1 )
)
  | Prod'prefix'2 => box
    (prefix'nt, [T ASSIGNMENT_WORD't]%list)
    (fun _1 =>
                                                   ( [Assignment _1] )
)
  | Prod'prefix'3 => box
    (prefix'nt, [T ASSIGNMENT_WORD't; NT prefix'nt]%list)
    (fun _2 _1 =>
                                                   ( Assignment _2 :: _1 )
)
  | Prod'program'0 => box
    (program'nt, [NT list'nt]%list)
    (fun _1 =>
                                                   ( _1 )
)
  | Prod'rlist'0 => box
    (rlist'nt, [NT io_redirect'nt]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'rlist'1 => box
    (rlist'nt, [NT io_redirect'nt; NT rlist'nt]%list)
    (fun _2 _1 =>
                                                   ( _2 :: _1 )
)
  | Prod'scmd'0 => box
    (scmd'nt, [NT suffix'nt; T WORD't; NT prefix'nt]%list)
    (fun _3 _2 _1 =>
                                                   ( Some (_2, []) )
)
  | Prod'scmd'1 => box
    (scmd'nt, [T WORD't; NT prefix'nt]%list)
    (fun _2 _1 =>
                                                   ( Some (_2, []) )
)
  | Prod'scmd'2 => box
    (scmd'nt, [NT prefix'nt]%list)
    (fun _1 =>
                                                   ( None )
)
  | Prod'scmd'3 => box
    (scmd'nt, [NT suffix'nt; T WORD't]%list)
    (fun _2 _1 =>
                                                   ( Some (_1, []) )
)
  | Prod'scmd'4 => box
    (scmd'nt, [T WORD't]%list)
    (fun _1 =>
                                                   ( Some (_1, []) )
)
  | Prod'separator'0 => box
    (separator'nt, [T AMP't]%list)
    (fun _1 =>
                                                   ( Amp )
)
  | Prod'separator'1 => box
    (separator'nt, [T SEMI't]%list)
    (fun _1 =>
                                                   ( Semi )
)
  | Prod'subshell'0 => box
    (subshell'nt, [T RPAREN't; NT clist'nt; T LPAREN't]%list)
    (fun _3 _2 _1 =>
                                                   ( Subshell _2 )
)
  | Prod'suffix'0 => box
    (suffix'nt, [NT io_redirect'nt]%list)
    (fun _1 =>
                                                   ( [] )
)
  | Prod'suffix'1 => box
    (suffix'nt, [NT io_redirect'nt; NT suffix'nt]%list)
    (fun _2 _1 =>
                                                   ( _1 )
)
  | Prod'suffix'2 => box
    (suffix'nt, [T WORD't]%list)
    (fun _1 =>
                                                   ( [Word _1] )
)
  | Prod'suffix'3 => box
    (suffix'nt, [T WORD't; NT suffix'nt]%list)
    (fun _2 _1 =>
                                                   ( Word _2 :: _1 )
)
  | Prod'suffix'4 => box
    (suffix'nt, [T SEMI't]%list)
    (fun _1 =>
                                                   ( [] )
)
  | Prod'suffix'5 => box
    (suffix'nt, [T SEMI't; NT suffix'nt]%list)
    (fun _2 _1 =>
                                                   ( _1 )
)
  | Prod'term'0 => box
    (term'nt, [NT command'nt]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'term'1 => box
    (term'nt, [T SEMI't; NT command'nt]%list)
    (fun _2 _1 =>
                                                   ( [_1] )
)
  | Prod'until_clause'0 => box
    (until_clause'nt, [NT do_group'nt; T DO_TOK't; NT clist'nt; T UNTIL_TOK't]%list)
    (fun _4 _3 _2 _1 =>
                                                           ( UntilClause _2 _4 )
)
  | Prod'while_clause'0 => box
    (while_clause'nt, [NT do_group'nt; T DO_TOK't; NT clist'nt; T WHILE_TOK't]%list)
    (fun _4 _3 _2 _1 =>
                                                           ( WhileClause _2 _4 )
)
  | Prod'wlist'0 => box
    (wlist'nt, [T WORD't]%list)
    (fun _1 =>
                                                   ( [_1] )
)
  | Prod'wlist'1 => box
    (wlist'nt, [T WORD't; NT wlist'nt]%list)
    (fun _2 _1 =>
                                                   ( _2 :: _1 )
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include MenhirLib.Grammar.Defs.

End Gram.

Module Aut <: MenhirLib.Automaton.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | wlist'nt => false
  | while_clause'nt => false
  | until_clause'nt => false
  | term'nt => false
  | suffix'nt => false
  | subshell'nt => false
  | separator'nt => false
  | scmd'nt => false
  | rlist'nt => false
  | program'nt => false
  | prefix'nt => false
  | pipe_sequence'nt => false
  | pattern'nt => false
  | list'nt => false
  | io_redirect'nt => false
  | if_clause'nt => false
  | function_def'nt => false
  | function_body'nt => false
  | for_clause'nt => false
  | else_part'nt => false
  | do_group'nt => false
  | compound'nt => false
  | command'nt => false
  | clist'nt => false
  | case_list'nt => false
  | case_item'nt => false
  | case_clause'nt => false
  | brace_group'nt => false
  | and_or'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | wlist'nt => [WORD't]%list
  | while_clause'nt => [WHILE_TOK't]%list
  | until_clause'nt => [UNTIL_TOK't]%list
  | term'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; ASSIGNMENT_WORD't]%list
  | suffix'nt => [WORD't; SEMI't; LESSGREAT't; LESSAND't; LESS't; IO_NUMBER't; GREATAND't; GREAT't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't]%list
  | subshell'nt => [LPAREN't]%list
  | separator'nt => [SEMI't; AMP't]%list
  | scmd'nt => [WORD't; LESSGREAT't; LESSAND't; LESS't; IO_NUMBER't; GREATAND't; GREAT't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; ASSIGNMENT_WORD't]%list
  | rlist'nt => [LESSGREAT't; LESSAND't; LESS't; IO_NUMBER't; GREATAND't; GREAT't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't]%list
  | program'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; BANG't; ASSIGNMENT_WORD't]%list
  | prefix'nt => [LESSGREAT't; LESSAND't; LESS't; IO_NUMBER't; GREATAND't; GREAT't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; ASSIGNMENT_WORD't]%list
  | pipe_sequence'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; ASSIGNMENT_WORD't]%list
  | pattern'nt => [WORD't]%list
  | list'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; BANG't; ASSIGNMENT_WORD't]%list
  | io_redirect'nt => [LESSGREAT't; LESSAND't; LESS't; IO_NUMBER't; GREATAND't; GREAT't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't]%list
  | if_clause'nt => [IF_TOK't]%list
  | function_def'nt => [NAME't]%list
  | function_body'nt => [WHILE_TOK't; UNTIL_TOK't; LPAREN't; LBRACE't; IF_TOK't; FOR_TOK't; CASE_TOK't]%list
  | for_clause'nt => [FOR_TOK't]%list
  | else_part'nt => [ELSE_TOK't; ELIF_TOK't]%list
  | do_group'nt => [DO_TOK't]%list
  | compound'nt => [WHILE_TOK't; UNTIL_TOK't; LPAREN't; LBRACE't; IF_TOK't; FOR_TOK't; CASE_TOK't]%list
  | command'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; ASSIGNMENT_WORD't]%list
  | clist'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; ASSIGNMENT_WORD't]%list
  | case_list'nt => [WORD't; LPAREN't]%list
  | case_item'nt => [WORD't; LPAREN't]%list
  | case_clause'nt => [CASE_TOK't]%list
  | brace_group'nt => [LBRACE't]%list
  | and_or'nt => [WORD't; WHILE_TOK't; UNTIL_TOK't; NAME't; LPAREN't; LESSGREAT't; LESSAND't; LESS't; LBRACE't; IO_NUMBER't; IF_TOK't; GREATAND't; GREAT't; FOR_TOK't; DLESSDASH't; DLESS't; DGREAT't; CLOBBER't; CASE_TOK't; BANG't; ASSIGNMENT_WORD't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'152
| Nis'151
| Nis'150
| Nis'149
| Nis'148
| Nis'147
| Nis'146
| Nis'145
| Nis'144
| Nis'143
| Nis'142
| Nis'140
| Nis'139
| Nis'138
| Nis'137
| Nis'136
| Nis'135
| Nis'134
| Nis'133
| Nis'132
| Nis'131
| Nis'130
| Nis'129
| Nis'128
| Nis'127
| Nis'126
| Nis'125
| Nis'124
| Nis'123
| Nis'122
| Nis'121
| Nis'120
| Nis'119
| Nis'118
| Nis'117
| Nis'116
| Nis'115
| Nis'114
| Nis'113
| Nis'112
| Nis'111
| Nis'110
| Nis'109
| Nis'108
| Nis'107
| Nis'106
| Nis'105
| Nis'104
| Nis'103
| Nis'102
| Nis'101
| Nis'100
| Nis'99
| Nis'98
| Nis'97
| Nis'96
| Nis'95
| Nis'94
| Nis'93
| Nis'92
| Nis'91
| Nis'90
| Nis'89
| Nis'88
| Nis'87
| Nis'86
| Nis'85
| Nis'84
| Nis'83
| Nis'82
| Nis'81
| Nis'80
| Nis'79
| Nis'78
| Nis'77
| Nis'76
| Nis'75
| Nis'74
| Nis'73
| Nis'72
| Nis'71
| Nis'70
| Nis'69
| Nis'68
| Nis'67
| Nis'66
| Nis'65
| Nis'64
| Nis'63
| Nis'62
| Nis'61
| Nis'60
| Nis'59
| Nis'58
| Nis'57
| Nis'56
| Nis'55
| Nis'54
| Nis'53
| Nis'52
| Nis'51
| Nis'50
| Nis'49
| Nis'48
| Nis'47
| Nis'46
| Nis'45
| Nis'44
| Nis'43
| Nis'42
| Nis'41
| Nis'40
| Nis'39
| Nis'38
| Nis'37
| Nis'36
| Nis'35
| Nis'34
| Nis'33
| Nis'32
| Nis'31
| Nis'30
| Nis'29
| Nis'28
| Nis'27
| Nis'26
| Nis'25
| Nis'24
| Nis'23
| Nis'22
| Nis'21
| Nis'20
| Nis'19
| Nis'18
| Nis'17
| Nis'16
| Nis'15
| Nis'14
| Nis'13
| Nis'12
| Nis'11
| Nis'10
| Nis'9
| Nis'8
| Nis'7
| Nis'6
| Nis'5
| Nis'4
| Nis'3
| Nis'2
| Nis'1.
Definition noninitstate := noninitstate'.

Global Program Instance noninitstateNum : MenhirLib.Alphabet.Numbered noninitstate :=
  { inj := fun x => match x return _ with
    | Nis'152 => 1%positive
    | Nis'151 => 2%positive
    | Nis'150 => 3%positive
    | Nis'149 => 4%positive
    | Nis'148 => 5%positive
    | Nis'147 => 6%positive
    | Nis'146 => 7%positive
    | Nis'145 => 8%positive
    | Nis'144 => 9%positive
    | Nis'143 => 10%positive
    | Nis'142 => 11%positive
    | Nis'140 => 12%positive
    | Nis'139 => 13%positive
    | Nis'138 => 14%positive
    | Nis'137 => 15%positive
    | Nis'136 => 16%positive
    | Nis'135 => 17%positive
    | Nis'134 => 18%positive
    | Nis'133 => 19%positive
    | Nis'132 => 20%positive
    | Nis'131 => 21%positive
    | Nis'130 => 22%positive
    | Nis'129 => 23%positive
    | Nis'128 => 24%positive
    | Nis'127 => 25%positive
    | Nis'126 => 26%positive
    | Nis'125 => 27%positive
    | Nis'124 => 28%positive
    | Nis'123 => 29%positive
    | Nis'122 => 30%positive
    | Nis'121 => 31%positive
    | Nis'120 => 32%positive
    | Nis'119 => 33%positive
    | Nis'118 => 34%positive
    | Nis'117 => 35%positive
    | Nis'116 => 36%positive
    | Nis'115 => 37%positive
    | Nis'114 => 38%positive
    | Nis'113 => 39%positive
    | Nis'112 => 40%positive
    | Nis'111 => 41%positive
    | Nis'110 => 42%positive
    | Nis'109 => 43%positive
    | Nis'108 => 44%positive
    | Nis'107 => 45%positive
    | Nis'106 => 46%positive
    | Nis'105 => 47%positive
    | Nis'104 => 48%positive
    | Nis'103 => 49%positive
    | Nis'102 => 50%positive
    | Nis'101 => 51%positive
    | Nis'100 => 52%positive
    | Nis'99 => 53%positive
    | Nis'98 => 54%positive
    | Nis'97 => 55%positive
    | Nis'96 => 56%positive
    | Nis'95 => 57%positive
    | Nis'94 => 58%positive
    | Nis'93 => 59%positive
    | Nis'92 => 60%positive
    | Nis'91 => 61%positive
    | Nis'90 => 62%positive
    | Nis'89 => 63%positive
    | Nis'88 => 64%positive
    | Nis'87 => 65%positive
    | Nis'86 => 66%positive
    | Nis'85 => 67%positive
    | Nis'84 => 68%positive
    | Nis'83 => 69%positive
    | Nis'82 => 70%positive
    | Nis'81 => 71%positive
    | Nis'80 => 72%positive
    | Nis'79 => 73%positive
    | Nis'78 => 74%positive
    | Nis'77 => 75%positive
    | Nis'76 => 76%positive
    | Nis'75 => 77%positive
    | Nis'74 => 78%positive
    | Nis'73 => 79%positive
    | Nis'72 => 80%positive
    | Nis'71 => 81%positive
    | Nis'70 => 82%positive
    | Nis'69 => 83%positive
    | Nis'68 => 84%positive
    | Nis'67 => 85%positive
    | Nis'66 => 86%positive
    | Nis'65 => 87%positive
    | Nis'64 => 88%positive
    | Nis'63 => 89%positive
    | Nis'62 => 90%positive
    | Nis'61 => 91%positive
    | Nis'60 => 92%positive
    | Nis'59 => 93%positive
    | Nis'58 => 94%positive
    | Nis'57 => 95%positive
    | Nis'56 => 96%positive
    | Nis'55 => 97%positive
    | Nis'54 => 98%positive
    | Nis'53 => 99%positive
    | Nis'52 => 100%positive
    | Nis'51 => 101%positive
    | Nis'50 => 102%positive
    | Nis'49 => 103%positive
    | Nis'48 => 104%positive
    | Nis'47 => 105%positive
    | Nis'46 => 106%positive
    | Nis'45 => 107%positive
    | Nis'44 => 108%positive
    | Nis'43 => 109%positive
    | Nis'42 => 110%positive
    | Nis'41 => 111%positive
    | Nis'40 => 112%positive
    | Nis'39 => 113%positive
    | Nis'38 => 114%positive
    | Nis'37 => 115%positive
    | Nis'36 => 116%positive
    | Nis'35 => 117%positive
    | Nis'34 => 118%positive
    | Nis'33 => 119%positive
    | Nis'32 => 120%positive
    | Nis'31 => 121%positive
    | Nis'30 => 122%positive
    | Nis'29 => 123%positive
    | Nis'28 => 124%positive
    | Nis'27 => 125%positive
    | Nis'26 => 126%positive
    | Nis'25 => 127%positive
    | Nis'24 => 128%positive
    | Nis'23 => 129%positive
    | Nis'22 => 130%positive
    | Nis'21 => 131%positive
    | Nis'20 => 132%positive
    | Nis'19 => 133%positive
    | Nis'18 => 134%positive
    | Nis'17 => 135%positive
    | Nis'16 => 136%positive
    | Nis'15 => 137%positive
    | Nis'14 => 138%positive
    | Nis'13 => 139%positive
    | Nis'12 => 140%positive
    | Nis'11 => 141%positive
    | Nis'10 => 142%positive
    | Nis'9 => 143%positive
    | Nis'8 => 144%positive
    | Nis'7 => 145%positive
    | Nis'6 => 146%positive
    | Nis'5 => 147%positive
    | Nis'4 => 148%positive
    | Nis'3 => 149%positive
    | Nis'2 => 150%positive
    | Nis'1 => 151%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'152
    | 2%positive => Nis'151
    | 3%positive => Nis'150
    | 4%positive => Nis'149
    | 5%positive => Nis'148
    | 6%positive => Nis'147
    | 7%positive => Nis'146
    | 8%positive => Nis'145
    | 9%positive => Nis'144
    | 10%positive => Nis'143
    | 11%positive => Nis'142
    | 12%positive => Nis'140
    | 13%positive => Nis'139
    | 14%positive => Nis'138
    | 15%positive => Nis'137
    | 16%positive => Nis'136
    | 17%positive => Nis'135
    | 18%positive => Nis'134
    | 19%positive => Nis'133
    | 20%positive => Nis'132
    | 21%positive => Nis'131
    | 22%positive => Nis'130
    | 23%positive => Nis'129
    | 24%positive => Nis'128
    | 25%positive => Nis'127
    | 26%positive => Nis'126
    | 27%positive => Nis'125
    | 28%positive => Nis'124
    | 29%positive => Nis'123
    | 30%positive => Nis'122
    | 31%positive => Nis'121
    | 32%positive => Nis'120
    | 33%positive => Nis'119
    | 34%positive => Nis'118
    | 35%positive => Nis'117
    | 36%positive => Nis'116
    | 37%positive => Nis'115
    | 38%positive => Nis'114
    | 39%positive => Nis'113
    | 40%positive => Nis'112
    | 41%positive => Nis'111
    | 42%positive => Nis'110
    | 43%positive => Nis'109
    | 44%positive => Nis'108
    | 45%positive => Nis'107
    | 46%positive => Nis'106
    | 47%positive => Nis'105
    | 48%positive => Nis'104
    | 49%positive => Nis'103
    | 50%positive => Nis'102
    | 51%positive => Nis'101
    | 52%positive => Nis'100
    | 53%positive => Nis'99
    | 54%positive => Nis'98
    | 55%positive => Nis'97
    | 56%positive => Nis'96
    | 57%positive => Nis'95
    | 58%positive => Nis'94
    | 59%positive => Nis'93
    | 60%positive => Nis'92
    | 61%positive => Nis'91
    | 62%positive => Nis'90
    | 63%positive => Nis'89
    | 64%positive => Nis'88
    | 65%positive => Nis'87
    | 66%positive => Nis'86
    | 67%positive => Nis'85
    | 68%positive => Nis'84
    | 69%positive => Nis'83
    | 70%positive => Nis'82
    | 71%positive => Nis'81
    | 72%positive => Nis'80
    | 73%positive => Nis'79
    | 74%positive => Nis'78
    | 75%positive => Nis'77
    | 76%positive => Nis'76
    | 77%positive => Nis'75
    | 78%positive => Nis'74
    | 79%positive => Nis'73
    | 80%positive => Nis'72
    | 81%positive => Nis'71
    | 82%positive => Nis'70
    | 83%positive => Nis'69
    | 84%positive => Nis'68
    | 85%positive => Nis'67
    | 86%positive => Nis'66
    | 87%positive => Nis'65
    | 88%positive => Nis'64
    | 89%positive => Nis'63
    | 90%positive => Nis'62
    | 91%positive => Nis'61
    | 92%positive => Nis'60
    | 93%positive => Nis'59
    | 94%positive => Nis'58
    | 95%positive => Nis'57
    | 96%positive => Nis'56
    | 97%positive => Nis'55
    | 98%positive => Nis'54
    | 99%positive => Nis'53
    | 100%positive => Nis'52
    | 101%positive => Nis'51
    | 102%positive => Nis'50
    | 103%positive => Nis'49
    | 104%positive => Nis'48
    | 105%positive => Nis'47
    | 106%positive => Nis'46
    | 107%positive => Nis'45
    | 108%positive => Nis'44
    | 109%positive => Nis'43
    | 110%positive => Nis'42
    | 111%positive => Nis'41
    | 112%positive => Nis'40
    | 113%positive => Nis'39
    | 114%positive => Nis'38
    | 115%positive => Nis'37
    | 116%positive => Nis'36
    | 117%positive => Nis'35
    | 118%positive => Nis'34
    | 119%positive => Nis'33
    | 120%positive => Nis'32
    | 121%positive => Nis'31
    | 122%positive => Nis'30
    | 123%positive => Nis'29
    | 124%positive => Nis'28
    | 125%positive => Nis'27
    | 126%positive => Nis'26
    | 127%positive => Nis'25
    | 128%positive => Nis'24
    | 129%positive => Nis'23
    | 130%positive => Nis'22
    | 131%positive => Nis'21
    | 132%positive => Nis'20
    | 133%positive => Nis'19
    | 134%positive => Nis'18
    | 135%positive => Nis'17
    | 136%positive => Nis'16
    | 137%positive => Nis'15
    | 138%positive => Nis'14
    | 139%positive => Nis'13
    | 140%positive => Nis'12
    | 141%positive => Nis'11
    | 142%positive => Nis'10
    | 143%positive => Nis'9
    | 144%positive => Nis'8
    | 145%positive => Nis'7
    | 146%positive => Nis'6
    | 147%positive => Nis'5
    | 148%positive => Nis'4
    | 149%positive => Nis'3
    | 150%positive => Nis'2
    | 151%positive => Nis'1
    | _ => Nis'152
    end)%Z;
    inj_bound := 151%positive }.
Global Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T WORD't
  | Nis'2 => T WORD't
  | Nis'3 => T SEMI't
  | Nis'4 => T LESSGREAT't
  | Nis'5 => T WORD't
  | Nis'6 => T LESSAND't
  | Nis'7 => T WORD't
  | Nis'8 => T LESS't
  | Nis'9 => T WORD't
  | Nis'10 => T IO_NUMBER't
  | Nis'11 => T LESSGREAT't
  | Nis'12 => T WORD't
  | Nis'13 => T LESSAND't
  | Nis'14 => T WORD't
  | Nis'15 => T LESS't
  | Nis'16 => T WORD't
  | Nis'17 => T GREATAND't
  | Nis'18 => T WORD't
  | Nis'19 => T GREAT't
  | Nis'20 => T WORD't
  | Nis'21 => T DLESSDASH't
  | Nis'22 => T WORD't
  | Nis'23 => T DLESS't
  | Nis'24 => T WORD't
  | Nis'25 => T DGREAT't
  | Nis'26 => T WORD't
  | Nis'27 => T CLOBBER't
  | Nis'28 => T WORD't
  | Nis'29 => T GREATAND't
  | Nis'30 => T WORD't
  | Nis'31 => T GREAT't
  | Nis'32 => T WORD't
  | Nis'33 => T DLESSDASH't
  | Nis'34 => T WORD't
  | Nis'35 => T DLESS't
  | Nis'36 => T WORD't
  | Nis'37 => T DGREAT't
  | Nis'38 => T WORD't
  | Nis'39 => T CLOBBER't
  | Nis'40 => T WORD't
  | Nis'41 => NT suffix'nt
  | Nis'42 => T WORD't
  | Nis'43 => T SEMI't
  | Nis'44 => NT io_redirect'nt
  | Nis'45 => NT io_redirect'nt
  | Nis'46 => T WHILE_TOK't
  | Nis'47 => T UNTIL_TOK't
  | Nis'48 => T NAME't
  | Nis'49 => T LPAREN't
  | Nis'50 => T RPAREN't
  | Nis'51 => T LPAREN't
  | Nis'52 => T LBRACE't
  | Nis'53 => T IF_TOK't
  | Nis'54 => T FOR_TOK't
  | Nis'55 => T NAME't
  | Nis'56 => T IN_TOK't
  | Nis'57 => T WORD't
  | Nis'58 => NT wlist'nt
  | Nis'59 => T WORD't
  | Nis'60 => T SEMI't
  | Nis'61 => T DO_TOK't
  | Nis'62 => T CASE_TOK't
  | Nis'63 => T WORD't
  | Nis'64 => T IN_TOK't
  | Nis'65 => T WORD't
  | Nis'66 => NT pattern'nt
  | Nis'67 => T LPAREN't
  | Nis'68 => NT pattern'nt
  | Nis'69 => T RPAREN't
  | Nis'70 => T ASSIGNMENT_WORD't
  | Nis'71 => NT while_clause'nt
  | Nis'72 => NT until_clause'nt
  | Nis'73 => NT term'nt
  | Nis'74 => T SEMI't
  | Nis'75 => NT subshell'nt
  | Nis'76 => NT scmd'nt
  | Nis'77 => NT prefix'nt
  | Nis'78 => T WORD't
  | Nis'79 => NT suffix'nt
  | Nis'80 => T ASSIGNMENT_WORD't
  | Nis'81 => NT io_redirect'nt
  | Nis'82 => NT io_redirect'nt
  | Nis'83 => NT if_clause'nt
  | Nis'84 => NT function_def'nt
  | Nis'85 => NT for_clause'nt
  | Nis'86 => NT compound'nt
  | Nis'87 => NT rlist'nt
  | Nis'88 => NT io_redirect'nt
  | Nis'89 => NT io_redirect'nt
  | Nis'90 => NT command'nt
  | Nis'91 => T SEMI't
  | Nis'92 => NT clist'nt
  | Nis'93 => NT case_clause'nt
  | Nis'94 => NT brace_group'nt
  | Nis'95 => NT clist'nt
  | Nis'96 => T DSEMI't
  | Nis'97 => T ESAC_TOK't
  | Nis'98 => NT pattern'nt
  | Nis'99 => T RPAREN't
  | Nis'100 => NT clist'nt
  | Nis'101 => T DSEMI't
  | Nis'102 => NT case_list'nt
  | Nis'103 => T ESAC_TOK't
  | Nis'104 => NT case_item'nt
  | Nis'105 => NT case_list'nt
  | Nis'106 => NT clist'nt
  | Nis'107 => T DONE_TOK't
  | Nis'108 => NT do_group'nt
  | Nis'109 => NT do_group'nt
  | Nis'110 => NT clist'nt
  | Nis'111 => T THEN_TOK't
  | Nis'112 => NT clist'nt
  | Nis'113 => T FI_TOK't
  | Nis'114 => T ELSE_TOK't
  | Nis'115 => NT clist'nt
  | Nis'116 => T ELIF_TOK't
  | Nis'117 => NT clist'nt
  | Nis'118 => T THEN_TOK't
  | Nis'119 => NT clist'nt
  | Nis'120 => NT else_part'nt
  | Nis'121 => NT else_part'nt
  | Nis'122 => T FI_TOK't
  | Nis'123 => NT clist'nt
  | Nis'124 => T RBRACE't
  | Nis'125 => NT clist'nt
  | Nis'126 => T RPAREN't
  | Nis'127 => NT function_body'nt
  | Nis'128 => NT compound'nt
  | Nis'129 => NT rlist'nt
  | Nis'130 => NT clist'nt
  | Nis'131 => T DO_TOK't
  | Nis'132 => NT do_group'nt
  | Nis'133 => NT clist'nt
  | Nis'134 => T DO_TOK't
  | Nis'135 => NT do_group'nt
  | Nis'136 => T BANG't
  | Nis'137 => NT pipe_sequence'nt
  | Nis'138 => T PIPE't
  | Nis'139 => NT command'nt
  | Nis'140 => NT command'nt
  | Nis'142 => NT pipe_sequence'nt
  | Nis'143 => NT list'nt
  | Nis'144 => T SEMI't
  | Nis'145 => T AMP't
  | Nis'146 => NT separator'nt
  | Nis'147 => NT and_or'nt
  | Nis'148 => T OR_IF't
  | Nis'149 => NT and_or'nt
  | Nis'150 => T AND_IF't
  | Nis'151 => NT and_or'nt
  | Nis'152 => NT and_or'nt
  end.

Inductive initstate' : Set :=
| Init'0.
Definition initstate := initstate'.

Global Program Instance initstateNum : MenhirLib.Alphabet.Numbered initstate :=
  { inj := fun x => match x return _ with
    | Init'0 => 1%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Init'0
    | _ => Init'0
    end)%Z;
    inj_bound := 1%positive }.
Global Instance InitStateAlph : MenhirLib.Alphabet.Alphabet initstate := _.

Include MenhirLib.Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => program'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | BANG't => Shift_act Nis'136 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'2 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'scmd'4
    | SEMI't => Shift_act Nis'3 (eq_refl _)
    | RPAREN't => Reduce_act Prod'scmd'4
    | RBRACE't => Reduce_act Prod'scmd'4
    | PIPE't => Reduce_act Prod'scmd'4
    | OR_IF't => Reduce_act Prod'scmd'4
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'scmd'4
    | ELSE_TOK't => Reduce_act Prod'scmd'4
    | ELIF_TOK't => Reduce_act Prod'scmd'4
    | DSEMI't => Reduce_act Prod'scmd'4
    | DO_TOK't => Reduce_act Prod'scmd'4
    | DONE_TOK't => Reduce_act Prod'scmd'4
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'scmd'4
    | AMP't => Reduce_act Prod'scmd'4
    | _ => Fail_act
    end)
  | Ninit Nis'2 => Default_reduce_act Prod'suffix'2
  | Ninit Nis'3 => Default_reduce_act Prod'suffix'4
  | Ninit Nis'4 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'5 => Default_reduce_act Prod'io_redirect'5
  | Ninit Nis'6 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'7 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'7 => Default_reduce_act Prod'io_redirect'3
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Default_reduce_act Prod'io_redirect'0
  | Ninit Nis'10 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LESSGREAT't => Shift_act Nis'11 (eq_refl _)
    | LESSAND't => Shift_act Nis'13 (eq_refl _)
    | LESS't => Shift_act Nis'15 (eq_refl _)
    | GREATAND't => Shift_act Nis'17 (eq_refl _)
    | GREAT't => Shift_act Nis'19 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'21 (eq_refl _)
    | DLESS't => Shift_act Nis'23 (eq_refl _)
    | DGREAT't => Shift_act Nis'25 (eq_refl _)
    | CLOBBER't => Shift_act Nis'27 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'12 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Default_reduce_act Prod'io_redirect'14
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'14 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Default_reduce_act Prod'io_redirect'12
  | Ninit Nis'15 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'16 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'16 => Default_reduce_act Prod'io_redirect'9
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'18 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Default_reduce_act Prod'io_redirect'13
  | Ninit Nis'19 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'20 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'20 => Default_reduce_act Prod'io_redirect'10
  | Ninit Nis'21 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'22 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'22 => Default_reduce_act Prod'io_redirect'17
  | Ninit Nis'23 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'24 => Default_reduce_act Prod'io_redirect'16
  | Ninit Nis'25 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'26 => Default_reduce_act Prod'io_redirect'11
  | Ninit Nis'27 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'28 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Default_reduce_act Prod'io_redirect'15
  | Ninit Nis'29 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'30 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'30 => Default_reduce_act Prod'io_redirect'4
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Default_reduce_act Prod'io_redirect'1
  | Ninit Nis'33 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'34 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'34 => Default_reduce_act Prod'io_redirect'8
  | Ninit Nis'35 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'36 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'36 => Default_reduce_act Prod'io_redirect'7
  | Ninit Nis'37 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'38 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'38 => Default_reduce_act Prod'io_redirect'2
  | Ninit Nis'39 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'40 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'40 => Default_reduce_act Prod'io_redirect'6
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'42 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'scmd'3
    | SEMI't => Shift_act Nis'43 (eq_refl _)
    | RPAREN't => Reduce_act Prod'scmd'3
    | RBRACE't => Reduce_act Prod'scmd'3
    | PIPE't => Reduce_act Prod'scmd'3
    | OR_IF't => Reduce_act Prod'scmd'3
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'scmd'3
    | ELSE_TOK't => Reduce_act Prod'scmd'3
    | ELIF_TOK't => Reduce_act Prod'scmd'3
    | DSEMI't => Reduce_act Prod'scmd'3
    | DO_TOK't => Reduce_act Prod'scmd'3
    | DONE_TOK't => Reduce_act Prod'scmd'3
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'scmd'3
    | AMP't => Reduce_act Prod'scmd'3
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Default_reduce_act Prod'suffix'3
  | Ninit Nis'43 => Default_reduce_act Prod'suffix'5
  | Ninit Nis'44 => Default_reduce_act Prod'suffix'1
  | Ninit Nis'45 => Default_reduce_act Prod'suffix'0
  | Ninit Nis'46 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'47 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'48 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'49 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'49 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'50 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'50 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'51 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'52 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'53 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'54 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | NAME't => Shift_act Nis'55 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'55 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | IN_TOK't => Shift_act Nis'56 (eq_refl _)
    | DO_TOK't => Shift_act Nis'61 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'56 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'57 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'57 => Default_reduce_act Prod'wlist'0
  | Ninit Nis'58 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'59 (eq_refl _)
    | SEMI't => Shift_act Nis'60 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'59 => Default_reduce_act Prod'wlist'1
  | Ninit Nis'60 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DO_TOK't => Shift_act Nis'61 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'61 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'62 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'63 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'63 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | IN_TOK't => Shift_act Nis'64 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'64 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'65 (eq_refl _)
    | LPAREN't => Shift_act Nis'67 (eq_refl _)
    | ESAC_TOK't => Shift_act Nis'97 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'65 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'65 (eq_refl _)
    | RPAREN't => Reduce_act Prod'pattern'0
    | _ => Fail_act
    end)
  | Ninit Nis'66 => Default_reduce_act Prod'pattern'1
  | Ninit Nis'67 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'65 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'68 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'69 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'69 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'70 => Default_reduce_act Prod'prefix'2
  | Ninit Nis'71 => Default_reduce_act Prod'compound'5
  | Ninit Nis'72 => Default_reduce_act Prod'compound'6
  | Ninit Nis'73 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'clist'0
    | SEMI't => Shift_act Nis'74 (eq_refl _)
    | RPAREN't => Reduce_act Prod'clist'0
    | RBRACE't => Reduce_act Prod'clist'0
    | FI_TOK't => Reduce_act Prod'clist'0
    | ELSE_TOK't => Reduce_act Prod'clist'0
    | ELIF_TOK't => Reduce_act Prod'clist'0
    | DSEMI't => Reduce_act Prod'clist'0
    | DO_TOK't => Reduce_act Prod'clist'0
    | DONE_TOK't => Reduce_act Prod'clist'0
    | _ => Fail_act
    end)
  | Ninit Nis'74 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'clist'1
    | RPAREN't => Reduce_act Prod'clist'1
    | RBRACE't => Reduce_act Prod'clist'1
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'clist'1
    | ELSE_TOK't => Reduce_act Prod'clist'1
    | ELIF_TOK't => Reduce_act Prod'clist'1
    | DSEMI't => Reduce_act Prod'clist'1
    | DO_TOK't => Reduce_act Prod'clist'1
    | DONE_TOK't => Reduce_act Prod'clist'1
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'75 => Default_reduce_act Prod'compound'1
  | Ninit Nis'76 => Default_reduce_act Prod'command'0
  | Ninit Nis'77 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'78 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'scmd'2
    | SEMI't => Reduce_act Prod'scmd'2
    | RPAREN't => Reduce_act Prod'scmd'2
    | RBRACE't => Reduce_act Prod'scmd'2
    | PIPE't => Reduce_act Prod'scmd'2
    | OR_IF't => Reduce_act Prod'scmd'2
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'scmd'2
    | ELSE_TOK't => Reduce_act Prod'scmd'2
    | ELIF_TOK't => Reduce_act Prod'scmd'2
    | DSEMI't => Reduce_act Prod'scmd'2
    | DO_TOK't => Reduce_act Prod'scmd'2
    | DONE_TOK't => Reduce_act Prod'scmd'2
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'80 (eq_refl _)
    | AND_IF't => Reduce_act Prod'scmd'2
    | AMP't => Reduce_act Prod'scmd'2
    | _ => Fail_act
    end)
  | Ninit Nis'78 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'2 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'scmd'1
    | SEMI't => Shift_act Nis'3 (eq_refl _)
    | RPAREN't => Reduce_act Prod'scmd'1
    | RBRACE't => Reduce_act Prod'scmd'1
    | PIPE't => Reduce_act Prod'scmd'1
    | OR_IF't => Reduce_act Prod'scmd'1
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'scmd'1
    | ELSE_TOK't => Reduce_act Prod'scmd'1
    | ELIF_TOK't => Reduce_act Prod'scmd'1
    | DSEMI't => Reduce_act Prod'scmd'1
    | DO_TOK't => Reduce_act Prod'scmd'1
    | DONE_TOK't => Reduce_act Prod'scmd'1
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'scmd'1
    | AMP't => Reduce_act Prod'scmd'1
    | _ => Fail_act
    end)
  | Ninit Nis'79 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'42 (eq_refl _)
    | THEN_TOK't => Reduce_act Prod'scmd'0
    | SEMI't => Shift_act Nis'43 (eq_refl _)
    | RPAREN't => Reduce_act Prod'scmd'0
    | RBRACE't => Reduce_act Prod'scmd'0
    | PIPE't => Reduce_act Prod'scmd'0
    | OR_IF't => Reduce_act Prod'scmd'0
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'scmd'0
    | ELSE_TOK't => Reduce_act Prod'scmd'0
    | ELIF_TOK't => Reduce_act Prod'scmd'0
    | DSEMI't => Reduce_act Prod'scmd'0
    | DO_TOK't => Reduce_act Prod'scmd'0
    | DONE_TOK't => Reduce_act Prod'scmd'0
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'scmd'0
    | AMP't => Reduce_act Prod'scmd'0
    | _ => Fail_act
    end)
  | Ninit Nis'80 => Default_reduce_act Prod'prefix'3
  | Ninit Nis'81 => Default_reduce_act Prod'prefix'1
  | Ninit Nis'82 => Default_reduce_act Prod'prefix'0
  | Ninit Nis'83 => Default_reduce_act Prod'compound'4
  | Ninit Nis'84 => Default_reduce_act Prod'command'3
  | Ninit Nis'85 => Default_reduce_act Prod'compound'2
  | Ninit Nis'86 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'command'1
    | SEMI't => Reduce_act Prod'command'1
    | RPAREN't => Reduce_act Prod'command'1
    | RBRACE't => Reduce_act Prod'command'1
    | PIPE't => Reduce_act Prod'command'1
    | OR_IF't => Reduce_act Prod'command'1
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'command'1
    | ELSE_TOK't => Reduce_act Prod'command'1
    | ELIF_TOK't => Reduce_act Prod'command'1
    | DSEMI't => Reduce_act Prod'command'1
    | DO_TOK't => Reduce_act Prod'command'1
    | DONE_TOK't => Reduce_act Prod'command'1
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'command'1
    | AMP't => Reduce_act Prod'command'1
    | _ => Fail_act
    end)
  | Ninit Nis'87 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'command'2
    | SEMI't => Reduce_act Prod'command'2
    | RPAREN't => Reduce_act Prod'command'2
    | RBRACE't => Reduce_act Prod'command'2
    | PIPE't => Reduce_act Prod'command'2
    | OR_IF't => Reduce_act Prod'command'2
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'command'2
    | ELSE_TOK't => Reduce_act Prod'command'2
    | ELIF_TOK't => Reduce_act Prod'command'2
    | DSEMI't => Reduce_act Prod'command'2
    | DO_TOK't => Reduce_act Prod'command'2
    | DONE_TOK't => Reduce_act Prod'command'2
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'command'2
    | AMP't => Reduce_act Prod'command'2
    | _ => Fail_act
    end)
  | Ninit Nis'88 => Default_reduce_act Prod'rlist'1
  | Ninit Nis'89 => Default_reduce_act Prod'rlist'0
  | Ninit Nis'90 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'term'0
    | SEMI't => Shift_act Nis'91 (eq_refl _)
    | RPAREN't => Reduce_act Prod'term'0
    | RBRACE't => Reduce_act Prod'term'0
    | FI_TOK't => Reduce_act Prod'term'0
    | ELSE_TOK't => Reduce_act Prod'term'0
    | ELIF_TOK't => Reduce_act Prod'term'0
    | DSEMI't => Reduce_act Prod'term'0
    | DO_TOK't => Reduce_act Prod'term'0
    | DONE_TOK't => Reduce_act Prod'term'0
    | _ => Fail_act
    end)
  | Ninit Nis'91 => Default_reduce_act Prod'term'1
  | Ninit Nis'92 => Default_reduce_act Prod'clist'2
  | Ninit Nis'93 => Default_reduce_act Prod'compound'3
  | Ninit Nis'94 => Default_reduce_act Prod'compound'0
  | Ninit Nis'95 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DSEMI't => Shift_act Nis'96 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'96 => Default_reduce_act Prod'case_item'1
  | Ninit Nis'97 => Default_reduce_act Prod'case_clause'1
  | Ninit Nis'98 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'99 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'99 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'100 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DSEMI't => Shift_act Nis'101 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'101 => Default_reduce_act Prod'case_item'0
  | Ninit Nis'102 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ESAC_TOK't => Shift_act Nis'103 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'103 => Default_reduce_act Prod'case_clause'0
  | Ninit Nis'104 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'65 (eq_refl _)
    | LPAREN't => Shift_act Nis'67 (eq_refl _)
    | ESAC_TOK't => Reduce_act Prod'case_list'1
    | _ => Fail_act
    end)
  | Ninit Nis'105 => Default_reduce_act Prod'case_list'0
  | Ninit Nis'106 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DONE_TOK't => Shift_act Nis'107 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'107 => Default_reduce_act Prod'do_group'0
  | Ninit Nis'108 => Default_reduce_act Prod'for_clause'0
  | Ninit Nis'109 => Default_reduce_act Prod'for_clause'1
  | Ninit Nis'110 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Shift_act Nis'111 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'111 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'112 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | FI_TOK't => Shift_act Nis'113 (eq_refl _)
    | ELSE_TOK't => Shift_act Nis'114 (eq_refl _)
    | ELIF_TOK't => Shift_act Nis'116 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'113 => Default_reduce_act Prod'if_clause'0
  | Ninit Nis'114 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'115 => Default_reduce_act Prod'else_part'0
  | Ninit Nis'116 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'117 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Shift_act Nis'118 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'118 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'119 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | FI_TOK't => Reduce_act Prod'else_part'1
    | ELSE_TOK't => Shift_act Nis'114 (eq_refl _)
    | ELIF_TOK't => Shift_act Nis'116 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'120 => Default_reduce_act Prod'else_part'2
  | Ninit Nis'121 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | FI_TOK't => Shift_act Nis'122 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'122 => Default_reduce_act Prod'if_clause'1
  | Ninit Nis'123 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RBRACE't => Shift_act Nis'124 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'124 => Default_reduce_act Prod'brace_group'0
  | Ninit Nis'125 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'126 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'126 => Default_reduce_act Prod'subshell'0
  | Ninit Nis'127 => Default_reduce_act Prod'function_def'0
  | Ninit Nis'128 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'function_body'0
    | SEMI't => Reduce_act Prod'function_body'0
    | RPAREN't => Reduce_act Prod'function_body'0
    | RBRACE't => Reduce_act Prod'function_body'0
    | PIPE't => Reduce_act Prod'function_body'0
    | OR_IF't => Reduce_act Prod'function_body'0
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'function_body'0
    | ELSE_TOK't => Reduce_act Prod'function_body'0
    | ELIF_TOK't => Reduce_act Prod'function_body'0
    | DSEMI't => Reduce_act Prod'function_body'0
    | DO_TOK't => Reduce_act Prod'function_body'0
    | DONE_TOK't => Reduce_act Prod'function_body'0
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'function_body'0
    | AMP't => Reduce_act Prod'function_body'0
    | _ => Fail_act
    end)
  | Ninit Nis'129 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | THEN_TOK't => Reduce_act Prod'function_body'1
    | SEMI't => Reduce_act Prod'function_body'1
    | RPAREN't => Reduce_act Prod'function_body'1
    | RBRACE't => Reduce_act Prod'function_body'1
    | PIPE't => Reduce_act Prod'function_body'1
    | OR_IF't => Reduce_act Prod'function_body'1
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FI_TOK't => Reduce_act Prod'function_body'1
    | ELSE_TOK't => Reduce_act Prod'function_body'1
    | ELIF_TOK't => Reduce_act Prod'function_body'1
    | DSEMI't => Reduce_act Prod'function_body'1
    | DO_TOK't => Reduce_act Prod'function_body'1
    | DONE_TOK't => Reduce_act Prod'function_body'1
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | AND_IF't => Reduce_act Prod'function_body'1
    | AMP't => Reduce_act Prod'function_body'1
    | _ => Fail_act
    end)
  | Ninit Nis'130 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DO_TOK't => Shift_act Nis'131 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'131 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DO_TOK't => Shift_act Nis'61 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'132 => Default_reduce_act Prod'until_clause'0
  | Ninit Nis'133 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DO_TOK't => Shift_act Nis'134 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'134 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DO_TOK't => Shift_act Nis'61 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'135 => Default_reduce_act Prod'while_clause'0
  | Ninit Nis'136 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'137 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'and_or'1
    | PIPE't => Shift_act Nis'138 (eq_refl _)
    | OR_IF't => Reduce_act Prod'and_or'1
    | AND_IF't => Reduce_act Prod'and_or'1
    | AMP't => Reduce_act Prod'and_or'1
    | _ => Fail_act
    end)
  | Ninit Nis'138 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'139 => Default_reduce_act Prod'pipe_sequence'1
  | Ninit Nis'140 => Default_reduce_act Prod'pipe_sequence'0
  | Ninit Nis'142 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'and_or'0
    | PIPE't => Shift_act Nis'138 (eq_refl _)
    | OR_IF't => Reduce_act Prod'and_or'0
    | AND_IF't => Reduce_act Prod'and_or'0
    | AMP't => Reduce_act Prod'and_or'0
    | _ => Fail_act
    end)
  | Ninit Nis'143 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Shift_act Nis'144 (eq_refl _)
    | AMP't => Shift_act Nis'145 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'144 => Default_reduce_act Prod'separator'1
  | Ninit Nis'145 => Default_reduce_act Prod'separator'0
  | Ninit Nis'146 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | BANG't => Shift_act Nis'136 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'147 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'list'0
    | OR_IF't => Shift_act Nis'148 (eq_refl _)
    | AND_IF't => Shift_act Nis'150 (eq_refl _)
    | AMP't => Reduce_act Prod'list'0
    | _ => Fail_act
    end)
  | Ninit Nis'148 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | BANG't => Shift_act Nis'136 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'149 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'and_or'3
    | OR_IF't => Shift_act Nis'148 (eq_refl _)
    | AND_IF't => Shift_act Nis'150 (eq_refl _)
    | AMP't => Reduce_act Prod'and_or'3
    | _ => Fail_act
    end)
  | Ninit Nis'150 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | WORD't => Shift_act Nis'1 (eq_refl _)
    | WHILE_TOK't => Shift_act Nis'46 (eq_refl _)
    | UNTIL_TOK't => Shift_act Nis'47 (eq_refl _)
    | NAME't => Shift_act Nis'48 (eq_refl _)
    | LPAREN't => Shift_act Nis'51 (eq_refl _)
    | LESSGREAT't => Shift_act Nis'4 (eq_refl _)
    | LESSAND't => Shift_act Nis'6 (eq_refl _)
    | LESS't => Shift_act Nis'8 (eq_refl _)
    | LBRACE't => Shift_act Nis'52 (eq_refl _)
    | IO_NUMBER't => Shift_act Nis'10 (eq_refl _)
    | IF_TOK't => Shift_act Nis'53 (eq_refl _)
    | GREATAND't => Shift_act Nis'29 (eq_refl _)
    | GREAT't => Shift_act Nis'31 (eq_refl _)
    | FOR_TOK't => Shift_act Nis'54 (eq_refl _)
    | DLESSDASH't => Shift_act Nis'33 (eq_refl _)
    | DLESS't => Shift_act Nis'35 (eq_refl _)
    | DGREAT't => Shift_act Nis'37 (eq_refl _)
    | CLOBBER't => Shift_act Nis'39 (eq_refl _)
    | CASE_TOK't => Shift_act Nis'62 (eq_refl _)
    | BANG't => Shift_act Nis'136 (eq_refl _)
    | ASSIGNMENT_WORD't => Shift_act Nis'70 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'151 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'and_or'2
    | OR_IF't => Shift_act Nis'148 (eq_refl _)
    | AND_IF't => Shift_act Nis'150 (eq_refl _)
    | AMP't => Reduce_act Prod'and_or'2
    | _ => Fail_act
    end)
  | Ninit Nis'152 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | SEMI't => Reduce_act Prod'list'1
    | OR_IF't => Shift_act Nis'148 (eq_refl _)
    | AND_IF't => Shift_act Nis'150 (eq_refl _)
    | AMP't => Reduce_act Prod'list'1
    | _ => Fail_act
    end)
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Init Init'0, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Init Init'0, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Init Init'0, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Init Init'0, program'nt => None  | Init Init'0, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Init Init'0, pipe_sequence'nt => Some (exist _ Nis'142 (eq_refl _))
  | Init Init'0, list'nt => Some (exist _ Nis'143 (eq_refl _))
  | Init Init'0, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Init Init'0, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Init Init'0, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Init Init'0, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Init Init'0, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Init Init'0, command'nt => Some (exist _ Nis'140 (eq_refl _))
  | Init Init'0, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Init Init'0, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Init Init'0, and_or'nt => Some (exist _ Nis'152 (eq_refl _))
  | Ninit Nis'1, suffix'nt => Some (exist _ Nis'41 (eq_refl _))
  | Ninit Nis'1, io_redirect'nt => Some (exist _ Nis'45 (eq_refl _))
  | Ninit Nis'41, io_redirect'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'46, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'46, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'46, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'46, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'46, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'46, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'46, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'46, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'46, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'46, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'46, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'46, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'46, clist'nt => Some (exist _ Nis'133 (eq_refl _))
  | Ninit Nis'46, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'46, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'47, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'47, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'47, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'47, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'47, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'47, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'47, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'47, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'47, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'47, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'47, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'47, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'47, clist'nt => Some (exist _ Nis'130 (eq_refl _))
  | Ninit Nis'47, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'47, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'50, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'50, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'50, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'50, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'50, function_body'nt => Some (exist _ Nis'127 (eq_refl _))
  | Ninit Nis'50, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'50, compound'nt => Some (exist _ Nis'128 (eq_refl _))
  | Ninit Nis'50, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'50, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'51, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'51, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'51, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'51, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'51, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'51, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'51, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'51, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'51, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'51, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'51, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'51, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'51, clist'nt => Some (exist _ Nis'125 (eq_refl _))
  | Ninit Nis'51, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'51, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'52, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'52, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'52, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'52, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'52, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'52, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'52, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'52, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'52, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'52, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'52, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'52, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'52, clist'nt => Some (exist _ Nis'123 (eq_refl _))
  | Ninit Nis'52, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'52, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'53, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'53, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'53, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'53, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'53, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'53, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'53, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'53, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'53, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'53, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'53, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'53, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'53, clist'nt => Some (exist _ Nis'110 (eq_refl _))
  | Ninit Nis'53, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'53, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'55, do_group'nt => Some (exist _ Nis'109 (eq_refl _))
  | Ninit Nis'56, wlist'nt => Some (exist _ Nis'58 (eq_refl _))
  | Ninit Nis'60, do_group'nt => Some (exist _ Nis'108 (eq_refl _))
  | Ninit Nis'61, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'61, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'61, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'61, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'61, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'61, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'61, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'61, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'61, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'61, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'61, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'61, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'61, clist'nt => Some (exist _ Nis'106 (eq_refl _))
  | Ninit Nis'61, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'61, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'64, pattern'nt => Some (exist _ Nis'98 (eq_refl _))
  | Ninit Nis'64, case_list'nt => Some (exist _ Nis'102 (eq_refl _))
  | Ninit Nis'64, case_item'nt => Some (exist _ Nis'104 (eq_refl _))
  | Ninit Nis'65, pattern'nt => Some (exist _ Nis'66 (eq_refl _))
  | Ninit Nis'67, pattern'nt => Some (exist _ Nis'68 (eq_refl _))
  | Ninit Nis'69, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'69, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'69, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'69, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'69, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'69, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'69, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'69, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'69, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'69, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'69, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'69, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'69, clist'nt => Some (exist _ Nis'95 (eq_refl _))
  | Ninit Nis'69, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'69, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'74, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'74, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'74, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'74, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'74, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'74, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'74, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'74, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'74, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'74, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'74, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'74, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'74, clist'nt => Some (exist _ Nis'92 (eq_refl _))
  | Ninit Nis'74, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'74, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'77, io_redirect'nt => Some (exist _ Nis'81 (eq_refl _))
  | Ninit Nis'78, suffix'nt => Some (exist _ Nis'79 (eq_refl _))
  | Ninit Nis'78, io_redirect'nt => Some (exist _ Nis'45 (eq_refl _))
  | Ninit Nis'79, io_redirect'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'86, rlist'nt => Some (exist _ Nis'87 (eq_refl _))
  | Ninit Nis'86, io_redirect'nt => Some (exist _ Nis'89 (eq_refl _))
  | Ninit Nis'87, io_redirect'nt => Some (exist _ Nis'88 (eq_refl _))
  | Ninit Nis'99, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'99, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'99, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'99, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'99, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'99, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'99, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'99, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'99, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'99, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'99, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'99, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'99, clist'nt => Some (exist _ Nis'100 (eq_refl _))
  | Ninit Nis'99, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'99, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'104, pattern'nt => Some (exist _ Nis'98 (eq_refl _))
  | Ninit Nis'104, case_list'nt => Some (exist _ Nis'105 (eq_refl _))
  | Ninit Nis'104, case_item'nt => Some (exist _ Nis'104 (eq_refl _))
  | Ninit Nis'111, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'111, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'111, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'111, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'111, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'111, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'111, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'111, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'111, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'111, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'111, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'111, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'111, clist'nt => Some (exist _ Nis'112 (eq_refl _))
  | Ninit Nis'111, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'111, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'112, else_part'nt => Some (exist _ Nis'121 (eq_refl _))
  | Ninit Nis'114, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'114, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'114, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'114, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'114, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'114, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'114, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'114, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'114, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'114, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'114, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'114, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'114, clist'nt => Some (exist _ Nis'115 (eq_refl _))
  | Ninit Nis'114, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'114, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'116, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'116, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'116, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'116, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'116, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'116, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'116, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'116, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'116, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'116, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'116, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'116, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'116, clist'nt => Some (exist _ Nis'117 (eq_refl _))
  | Ninit Nis'116, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'116, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'118, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'118, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'118, term'nt => Some (exist _ Nis'73 (eq_refl _))
  | Ninit Nis'118, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'118, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'118, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'118, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'118, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'118, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'118, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'118, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'118, command'nt => Some (exist _ Nis'90 (eq_refl _))
  | Ninit Nis'118, clist'nt => Some (exist _ Nis'119 (eq_refl _))
  | Ninit Nis'118, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'118, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'119, else_part'nt => Some (exist _ Nis'120 (eq_refl _))
  | Ninit Nis'128, rlist'nt => Some (exist _ Nis'129 (eq_refl _))
  | Ninit Nis'128, io_redirect'nt => Some (exist _ Nis'89 (eq_refl _))
  | Ninit Nis'129, io_redirect'nt => Some (exist _ Nis'88 (eq_refl _))
  | Ninit Nis'131, do_group'nt => Some (exist _ Nis'132 (eq_refl _))
  | Ninit Nis'134, do_group'nt => Some (exist _ Nis'135 (eq_refl _))
  | Ninit Nis'136, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'136, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'136, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'136, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'136, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'136, pipe_sequence'nt => Some (exist _ Nis'137 (eq_refl _))
  | Ninit Nis'136, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'136, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'136, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'136, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'136, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'136, command'nt => Some (exist _ Nis'140 (eq_refl _))
  | Ninit Nis'136, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'136, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'138, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'138, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'138, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'138, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'138, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'138, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'138, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'138, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'138, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'138, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'138, command'nt => Some (exist _ Nis'139 (eq_refl _))
  | Ninit Nis'138, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'138, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'143, separator'nt => Some (exist _ Nis'146 (eq_refl _))
  | Ninit Nis'146, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'146, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'146, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'146, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'146, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'146, pipe_sequence'nt => Some (exist _ Nis'142 (eq_refl _))
  | Ninit Nis'146, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'146, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'146, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'146, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'146, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'146, command'nt => Some (exist _ Nis'140 (eq_refl _))
  | Ninit Nis'146, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'146, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'146, and_or'nt => Some (exist _ Nis'147 (eq_refl _))
  | Ninit Nis'148, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'148, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'148, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'148, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'148, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'148, pipe_sequence'nt => Some (exist _ Nis'142 (eq_refl _))
  | Ninit Nis'148, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'148, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'148, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'148, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'148, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'148, command'nt => Some (exist _ Nis'140 (eq_refl _))
  | Ninit Nis'148, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'148, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'148, and_or'nt => Some (exist _ Nis'149 (eq_refl _))
  | Ninit Nis'150, while_clause'nt => Some (exist _ Nis'71 (eq_refl _))
  | Ninit Nis'150, until_clause'nt => Some (exist _ Nis'72 (eq_refl _))
  | Ninit Nis'150, subshell'nt => Some (exist _ Nis'75 (eq_refl _))
  | Ninit Nis'150, scmd'nt => Some (exist _ Nis'76 (eq_refl _))
  | Ninit Nis'150, prefix'nt => Some (exist _ Nis'77 (eq_refl _))
  | Ninit Nis'150, pipe_sequence'nt => Some (exist _ Nis'142 (eq_refl _))
  | Ninit Nis'150, io_redirect'nt => Some (exist _ Nis'82 (eq_refl _))
  | Ninit Nis'150, if_clause'nt => Some (exist _ Nis'83 (eq_refl _))
  | Ninit Nis'150, function_def'nt => Some (exist _ Nis'84 (eq_refl _))
  | Ninit Nis'150, for_clause'nt => Some (exist _ Nis'85 (eq_refl _))
  | Ninit Nis'150, compound'nt => Some (exist _ Nis'86 (eq_refl _))
  | Ninit Nis'150, command'nt => Some (exist _ Nis'140 (eq_refl _))
  | Ninit Nis'150, case_clause'nt => Some (exist _ Nis'93 (eq_refl _))
  | Ninit Nis'150, brace_group'nt => Some (exist _ Nis'94 (eq_refl _))
  | Ninit Nis'150, and_or'nt => Some (exist _ Nis'151 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => []%list
  | Nis'4 => []%list
  | Nis'5 => [T LESSGREAT't]%list
  | Nis'6 => []%list
  | Nis'7 => [T LESSAND't]%list
  | Nis'8 => []%list
  | Nis'9 => [T LESS't]%list
  | Nis'10 => []%list
  | Nis'11 => [T IO_NUMBER't]%list
  | Nis'12 => [T LESSGREAT't; T IO_NUMBER't]%list
  | Nis'13 => [T IO_NUMBER't]%list
  | Nis'14 => [T LESSAND't; T IO_NUMBER't]%list
  | Nis'15 => [T IO_NUMBER't]%list
  | Nis'16 => [T LESS't; T IO_NUMBER't]%list
  | Nis'17 => [T IO_NUMBER't]%list
  | Nis'18 => [T GREATAND't; T IO_NUMBER't]%list
  | Nis'19 => [T IO_NUMBER't]%list
  | Nis'20 => [T GREAT't; T IO_NUMBER't]%list
  | Nis'21 => [T IO_NUMBER't]%list
  | Nis'22 => [T DLESSDASH't; T IO_NUMBER't]%list
  | Nis'23 => [T IO_NUMBER't]%list
  | Nis'24 => [T DLESS't; T IO_NUMBER't]%list
  | Nis'25 => [T IO_NUMBER't]%list
  | Nis'26 => [T DGREAT't; T IO_NUMBER't]%list
  | Nis'27 => [T IO_NUMBER't]%list
  | Nis'28 => [T CLOBBER't; T IO_NUMBER't]%list
  | Nis'29 => []%list
  | Nis'30 => [T GREATAND't]%list
  | Nis'31 => []%list
  | Nis'32 => [T GREAT't]%list
  | Nis'33 => []%list
  | Nis'34 => [T DLESSDASH't]%list
  | Nis'35 => []%list
  | Nis'36 => [T DLESS't]%list
  | Nis'37 => []%list
  | Nis'38 => [T DGREAT't]%list
  | Nis'39 => []%list
  | Nis'40 => [T CLOBBER't]%list
  | Nis'41 => [T WORD't]%list
  | Nis'42 => [NT suffix'nt]%list
  | Nis'43 => [NT suffix'nt]%list
  | Nis'44 => [NT suffix'nt]%list
  | Nis'45 => []%list
  | Nis'46 => []%list
  | Nis'47 => []%list
  | Nis'48 => []%list
  | Nis'49 => [T NAME't]%list
  | Nis'50 => [T LPAREN't; T NAME't]%list
  | Nis'51 => []%list
  | Nis'52 => []%list
  | Nis'53 => []%list
  | Nis'54 => []%list
  | Nis'55 => [T FOR_TOK't]%list
  | Nis'56 => [T NAME't; T FOR_TOK't]%list
  | Nis'57 => []%list
  | Nis'58 => [T IN_TOK't; T NAME't; T FOR_TOK't]%list
  | Nis'59 => [NT wlist'nt]%list
  | Nis'60 => [NT wlist'nt; T IN_TOK't; T NAME't; T FOR_TOK't]%list
  | Nis'61 => []%list
  | Nis'62 => []%list
  | Nis'63 => [T CASE_TOK't]%list
  | Nis'64 => [T WORD't; T CASE_TOK't]%list
  | Nis'65 => []%list
  | Nis'66 => [T WORD't]%list
  | Nis'67 => []%list
  | Nis'68 => [T LPAREN't]%list
  | Nis'69 => [NT pattern'nt; T LPAREN't]%list
  | Nis'70 => []%list
  | Nis'71 => []%list
  | Nis'72 => []%list
  | Nis'73 => []%list
  | Nis'74 => [NT term'nt]%list
  | Nis'75 => []%list
  | Nis'76 => []%list
  | Nis'77 => []%list
  | Nis'78 => [NT prefix'nt]%list
  | Nis'79 => [T WORD't; NT prefix'nt]%list
  | Nis'80 => [NT prefix'nt]%list
  | Nis'81 => [NT prefix'nt]%list
  | Nis'82 => []%list
  | Nis'83 => []%list
  | Nis'84 => []%list
  | Nis'85 => []%list
  | Nis'86 => []%list
  | Nis'87 => [NT compound'nt]%list
  | Nis'88 => [NT rlist'nt]%list
  | Nis'89 => []%list
  | Nis'90 => []%list
  | Nis'91 => [NT command'nt]%list
  | Nis'92 => [T SEMI't; NT term'nt]%list
  | Nis'93 => []%list
  | Nis'94 => []%list
  | Nis'95 => [T RPAREN't; NT pattern'nt; T LPAREN't]%list
  | Nis'96 => [NT clist'nt; T RPAREN't; NT pattern'nt; T LPAREN't]%list
  | Nis'97 => [T IN_TOK't; T WORD't; T CASE_TOK't]%list
  | Nis'98 => []%list
  | Nis'99 => [NT pattern'nt]%list
  | Nis'100 => [T RPAREN't; NT pattern'nt]%list
  | Nis'101 => [NT clist'nt; T RPAREN't; NT pattern'nt]%list
  | Nis'102 => [T IN_TOK't; T WORD't; T CASE_TOK't]%list
  | Nis'103 => [NT case_list'nt; T IN_TOK't; T WORD't; T CASE_TOK't]%list
  | Nis'104 => []%list
  | Nis'105 => [NT case_item'nt]%list
  | Nis'106 => [T DO_TOK't]%list
  | Nis'107 => [NT clist'nt; T DO_TOK't]%list
  | Nis'108 => [T SEMI't; NT wlist'nt; T IN_TOK't; T NAME't; T FOR_TOK't]%list
  | Nis'109 => [T NAME't; T FOR_TOK't]%list
  | Nis'110 => [T IF_TOK't]%list
  | Nis'111 => [NT clist'nt; T IF_TOK't]%list
  | Nis'112 => [T THEN_TOK't; NT clist'nt; T IF_TOK't]%list
  | Nis'113 => [NT clist'nt; T THEN_TOK't; NT clist'nt; T IF_TOK't]%list
  | Nis'114 => []%list
  | Nis'115 => [T ELSE_TOK't]%list
  | Nis'116 => []%list
  | Nis'117 => [T ELIF_TOK't]%list
  | Nis'118 => [NT clist'nt; T ELIF_TOK't]%list
  | Nis'119 => [T THEN_TOK't; NT clist'nt; T ELIF_TOK't]%list
  | Nis'120 => [NT clist'nt; T THEN_TOK't; NT clist'nt; T ELIF_TOK't]%list
  | Nis'121 => [NT clist'nt; T THEN_TOK't; NT clist'nt; T IF_TOK't]%list
  | Nis'122 => [NT else_part'nt; NT clist'nt; T THEN_TOK't; NT clist'nt; T IF_TOK't]%list
  | Nis'123 => [T LBRACE't]%list
  | Nis'124 => [NT clist'nt; T LBRACE't]%list
  | Nis'125 => [T LPAREN't]%list
  | Nis'126 => [NT clist'nt; T LPAREN't]%list
  | Nis'127 => [T RPAREN't; T LPAREN't; T NAME't]%list
  | Nis'128 => []%list
  | Nis'129 => [NT compound'nt]%list
  | Nis'130 => [T UNTIL_TOK't]%list
  | Nis'131 => [NT clist'nt; T UNTIL_TOK't]%list
  | Nis'132 => [T DO_TOK't; NT clist'nt; T UNTIL_TOK't]%list
  | Nis'133 => [T WHILE_TOK't]%list
  | Nis'134 => [NT clist'nt; T WHILE_TOK't]%list
  | Nis'135 => [T DO_TOK't; NT clist'nt; T WHILE_TOK't]%list
  | Nis'136 => []%list
  | Nis'137 => [T BANG't]%list
  | Nis'138 => [NT pipe_sequence'nt]%list
  | Nis'139 => [T PIPE't; NT pipe_sequence'nt]%list
  | Nis'140 => []%list
  | Nis'142 => []%list
  | Nis'143 => []%list
  | Nis'144 => []%list
  | Nis'145 => []%list
  | Nis'146 => [NT list'nt]%list
  | Nis'147 => [NT separator'nt; NT list'nt]%list
  | Nis'148 => [NT and_or'nt]%list
  | Nis'149 => [T OR_IF't; NT and_or'nt]%list
  | Nis'150 => [NT and_or'nt]%list
  | Nis'151 => [T AND_IF't; NT and_or'nt]%list
  | Nis'152 => []%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'46 | Ninit Nis'47 | Ninit Nis'51 | Ninit Nis'52 | Ninit Nis'53 | Ninit Nis'61 | Ninit Nis'69 | Ninit Nis'74 | Ninit Nis'99 | Ninit Nis'111 | Ninit Nis'114 | Ninit Nis'116 | Ninit Nis'118 | Ninit Nis'136 | Ninit Nis'138 | Ninit Nis'146 | Ninit Nis'148 | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Ninit Nis'1 | Ninit Nis'78 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'1 | Ninit Nis'41 | Ninit Nis'46 | Ninit Nis'47 | Ninit Nis'51 | Ninit Nis'52 | Ninit Nis'53 | Ninit Nis'61 | Ninit Nis'69 | Ninit Nis'74 | Ninit Nis'77 | Ninit Nis'78 | Ninit Nis'79 | Ninit Nis'86 | Ninit Nis'87 | Ninit Nis'99 | Ninit Nis'111 | Ninit Nis'114 | Ninit Nis'116 | Ninit Nis'118 | Ninit Nis'128 | Ninit Nis'129 | Ninit Nis'136 | Ninit Nis'138 | Ninit Nis'146 | Ninit Nis'148 | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'4 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'6 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'10 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'15 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'19 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'21 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'23 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'27 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'29 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'31 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'33 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'35 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'1 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'41 | Ninit Nis'79 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'46 | Ninit Nis'47 | Ninit Nis'50 | Ninit Nis'51 | Ninit Nis'52 | Ninit Nis'53 | Ninit Nis'61 | Ninit Nis'69 | Ninit Nis'74 | Ninit Nis'99 | Ninit Nis'111 | Ninit Nis'114 | Ninit Nis'116 | Ninit Nis'118 | Ninit Nis'136 | Ninit Nis'138 | Ninit Nis'146 | Ninit Nis'148 | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'49 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'54 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'55 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Ninit Nis'56 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'58 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'55 | Ninit Nis'60 | Ninit Nis'131 | Ninit Nis'134 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Ninit Nis'62 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'63 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'64 | Ninit Nis'65 | Ninit Nis'67 | Ninit Nis'104 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'65 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition state_set_37 (s:state) : bool :=
  match s with
  | Ninit Nis'64 | Ninit Nis'104 => true
  | _ => false
  end.
Extract Inlined Constant state_set_37 => "assert false".

Definition state_set_38 (s:state) : bool :=
  match s with
  | Ninit Nis'67 => true
  | _ => false
  end.
Extract Inlined Constant state_set_38 => "assert false".

Definition state_set_39 (s:state) : bool :=
  match s with
  | Ninit Nis'68 => true
  | _ => false
  end.
Extract Inlined Constant state_set_39 => "assert false".

Definition state_set_40 (s:state) : bool :=
  match s with
  | Ninit Nis'46 | Ninit Nis'47 | Ninit Nis'51 | Ninit Nis'52 | Ninit Nis'53 | Ninit Nis'61 | Ninit Nis'69 | Ninit Nis'74 | Ninit Nis'99 | Ninit Nis'111 | Ninit Nis'114 | Ninit Nis'116 | Ninit Nis'118 => true
  | _ => false
  end.
Extract Inlined Constant state_set_40 => "assert false".

Definition state_set_41 (s:state) : bool :=
  match s with
  | Ninit Nis'73 => true
  | _ => false
  end.
Extract Inlined Constant state_set_41 => "assert false".

Definition state_set_42 (s:state) : bool :=
  match s with
  | Ninit Nis'77 => true
  | _ => false
  end.
Extract Inlined Constant state_set_42 => "assert false".

Definition state_set_43 (s:state) : bool :=
  match s with
  | Ninit Nis'78 => true
  | _ => false
  end.
Extract Inlined Constant state_set_43 => "assert false".

Definition state_set_44 (s:state) : bool :=
  match s with
  | Ninit Nis'86 => true
  | _ => false
  end.
Extract Inlined Constant state_set_44 => "assert false".

Definition state_set_45 (s:state) : bool :=
  match s with
  | Ninit Nis'86 | Ninit Nis'128 => true
  | _ => false
  end.
Extract Inlined Constant state_set_45 => "assert false".

Definition state_set_46 (s:state) : bool :=
  match s with
  | Ninit Nis'87 | Ninit Nis'129 => true
  | _ => false
  end.
Extract Inlined Constant state_set_46 => "assert false".

Definition state_set_47 (s:state) : bool :=
  match s with
  | Ninit Nis'90 => true
  | _ => false
  end.
Extract Inlined Constant state_set_47 => "assert false".

Definition state_set_48 (s:state) : bool :=
  match s with
  | Ninit Nis'74 => true
  | _ => false
  end.
Extract Inlined Constant state_set_48 => "assert false".

Definition state_set_49 (s:state) : bool :=
  match s with
  | Ninit Nis'69 => true
  | _ => false
  end.
Extract Inlined Constant state_set_49 => "assert false".

Definition state_set_50 (s:state) : bool :=
  match s with
  | Ninit Nis'95 => true
  | _ => false
  end.
Extract Inlined Constant state_set_50 => "assert false".

Definition state_set_51 (s:state) : bool :=
  match s with
  | Ninit Nis'64 => true
  | _ => false
  end.
Extract Inlined Constant state_set_51 => "assert false".

Definition state_set_52 (s:state) : bool :=
  match s with
  | Ninit Nis'98 => true
  | _ => false
  end.
Extract Inlined Constant state_set_52 => "assert false".

Definition state_set_53 (s:state) : bool :=
  match s with
  | Ninit Nis'99 => true
  | _ => false
  end.
Extract Inlined Constant state_set_53 => "assert false".

Definition state_set_54 (s:state) : bool :=
  match s with
  | Ninit Nis'100 => true
  | _ => false
  end.
Extract Inlined Constant state_set_54 => "assert false".

Definition state_set_55 (s:state) : bool :=
  match s with
  | Ninit Nis'102 => true
  | _ => false
  end.
Extract Inlined Constant state_set_55 => "assert false".

Definition state_set_56 (s:state) : bool :=
  match s with
  | Ninit Nis'104 => true
  | _ => false
  end.
Extract Inlined Constant state_set_56 => "assert false".

Definition state_set_57 (s:state) : bool :=
  match s with
  | Ninit Nis'61 => true
  | _ => false
  end.
Extract Inlined Constant state_set_57 => "assert false".

Definition state_set_58 (s:state) : bool :=
  match s with
  | Ninit Nis'106 => true
  | _ => false
  end.
Extract Inlined Constant state_set_58 => "assert false".

Definition state_set_59 (s:state) : bool :=
  match s with
  | Ninit Nis'60 => true
  | _ => false
  end.
Extract Inlined Constant state_set_59 => "assert false".

Definition state_set_60 (s:state) : bool :=
  match s with
  | Ninit Nis'53 => true
  | _ => false
  end.
Extract Inlined Constant state_set_60 => "assert false".

Definition state_set_61 (s:state) : bool :=
  match s with
  | Ninit Nis'110 => true
  | _ => false
  end.
Extract Inlined Constant state_set_61 => "assert false".

Definition state_set_62 (s:state) : bool :=
  match s with
  | Ninit Nis'111 => true
  | _ => false
  end.
Extract Inlined Constant state_set_62 => "assert false".

Definition state_set_63 (s:state) : bool :=
  match s with
  | Ninit Nis'112 => true
  | _ => false
  end.
Extract Inlined Constant state_set_63 => "assert false".

Definition state_set_64 (s:state) : bool :=
  match s with
  | Ninit Nis'112 | Ninit Nis'119 => true
  | _ => false
  end.
Extract Inlined Constant state_set_64 => "assert false".

Definition state_set_65 (s:state) : bool :=
  match s with
  | Ninit Nis'114 => true
  | _ => false
  end.
Extract Inlined Constant state_set_65 => "assert false".

Definition state_set_66 (s:state) : bool :=
  match s with
  | Ninit Nis'116 => true
  | _ => false
  end.
Extract Inlined Constant state_set_66 => "assert false".

Definition state_set_67 (s:state) : bool :=
  match s with
  | Ninit Nis'117 => true
  | _ => false
  end.
Extract Inlined Constant state_set_67 => "assert false".

Definition state_set_68 (s:state) : bool :=
  match s with
  | Ninit Nis'118 => true
  | _ => false
  end.
Extract Inlined Constant state_set_68 => "assert false".

Definition state_set_69 (s:state) : bool :=
  match s with
  | Ninit Nis'119 => true
  | _ => false
  end.
Extract Inlined Constant state_set_69 => "assert false".

Definition state_set_70 (s:state) : bool :=
  match s with
  | Ninit Nis'121 => true
  | _ => false
  end.
Extract Inlined Constant state_set_70 => "assert false".

Definition state_set_71 (s:state) : bool :=
  match s with
  | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_71 => "assert false".

Definition state_set_72 (s:state) : bool :=
  match s with
  | Ninit Nis'123 => true
  | _ => false
  end.
Extract Inlined Constant state_set_72 => "assert false".

Definition state_set_73 (s:state) : bool :=
  match s with
  | Ninit Nis'51 => true
  | _ => false
  end.
Extract Inlined Constant state_set_73 => "assert false".

Definition state_set_74 (s:state) : bool :=
  match s with
  | Ninit Nis'125 => true
  | _ => false
  end.
Extract Inlined Constant state_set_74 => "assert false".

Definition state_set_75 (s:state) : bool :=
  match s with
  | Ninit Nis'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_75 => "assert false".

Definition state_set_76 (s:state) : bool :=
  match s with
  | Ninit Nis'128 => true
  | _ => false
  end.
Extract Inlined Constant state_set_76 => "assert false".

Definition state_set_77 (s:state) : bool :=
  match s with
  | Ninit Nis'47 => true
  | _ => false
  end.
Extract Inlined Constant state_set_77 => "assert false".

Definition state_set_78 (s:state) : bool :=
  match s with
  | Ninit Nis'130 => true
  | _ => false
  end.
Extract Inlined Constant state_set_78 => "assert false".

Definition state_set_79 (s:state) : bool :=
  match s with
  | Ninit Nis'131 => true
  | _ => false
  end.
Extract Inlined Constant state_set_79 => "assert false".

Definition state_set_80 (s:state) : bool :=
  match s with
  | Ninit Nis'46 => true
  | _ => false
  end.
Extract Inlined Constant state_set_80 => "assert false".

Definition state_set_81 (s:state) : bool :=
  match s with
  | Ninit Nis'133 => true
  | _ => false
  end.
Extract Inlined Constant state_set_81 => "assert false".

Definition state_set_82 (s:state) : bool :=
  match s with
  | Ninit Nis'134 => true
  | _ => false
  end.
Extract Inlined Constant state_set_82 => "assert false".

Definition state_set_83 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'146 | Ninit Nis'148 | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_83 => "assert false".

Definition state_set_84 (s:state) : bool :=
  match s with
  | Ninit Nis'136 => true
  | _ => false
  end.
Extract Inlined Constant state_set_84 => "assert false".

Definition state_set_85 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'136 | Ninit Nis'146 | Ninit Nis'148 | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_85 => "assert false".

Definition state_set_86 (s:state) : bool :=
  match s with
  | Ninit Nis'137 | Ninit Nis'142 => true
  | _ => false
  end.
Extract Inlined Constant state_set_86 => "assert false".

Definition state_set_87 (s:state) : bool :=
  match s with
  | Ninit Nis'138 => true
  | _ => false
  end.
Extract Inlined Constant state_set_87 => "assert false".

Definition state_set_88 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_88 => "assert false".

Definition state_set_89 (s:state) : bool :=
  match s with
  | Ninit Nis'143 => true
  | _ => false
  end.
Extract Inlined Constant state_set_89 => "assert false".

Definition state_set_90 (s:state) : bool :=
  match s with
  | Ninit Nis'146 => true
  | _ => false
  end.
Extract Inlined Constant state_set_90 => "assert false".

Definition state_set_91 (s:state) : bool :=
  match s with
  | Ninit Nis'147 | Ninit Nis'149 | Ninit Nis'151 | Ninit Nis'152 => true
  | _ => false
  end.
Extract Inlined Constant state_set_91 => "assert false".

Definition state_set_92 (s:state) : bool :=
  match s with
  | Ninit Nis'148 => true
  | _ => false
  end.
Extract Inlined Constant state_set_92 => "assert false".

Definition state_set_93 (s:state) : bool :=
  match s with
  | Ninit Nis'150 => true
  | _ => false
  end.
Extract Inlined Constant state_set_93 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [state_set_1]%list
  | Nis'2 => [state_set_2]%list
  | Nis'3 => [state_set_2]%list
  | Nis'4 => [state_set_3]%list
  | Nis'5 => [state_set_4; state_set_3]%list
  | Nis'6 => [state_set_3]%list
  | Nis'7 => [state_set_5; state_set_3]%list
  | Nis'8 => [state_set_3]%list
  | Nis'9 => [state_set_6; state_set_3]%list
  | Nis'10 => [state_set_3]%list
  | Nis'11 => [state_set_7; state_set_3]%list
  | Nis'12 => [state_set_8; state_set_7; state_set_3]%list
  | Nis'13 => [state_set_7; state_set_3]%list
  | Nis'14 => [state_set_9; state_set_7; state_set_3]%list
  | Nis'15 => [state_set_7; state_set_3]%list
  | Nis'16 => [state_set_10; state_set_7; state_set_3]%list
  | Nis'17 => [state_set_7; state_set_3]%list
  | Nis'18 => [state_set_11; state_set_7; state_set_3]%list
  | Nis'19 => [state_set_7; state_set_3]%list
  | Nis'20 => [state_set_12; state_set_7; state_set_3]%list
  | Nis'21 => [state_set_7; state_set_3]%list
  | Nis'22 => [state_set_13; state_set_7; state_set_3]%list
  | Nis'23 => [state_set_7; state_set_3]%list
  | Nis'24 => [state_set_14; state_set_7; state_set_3]%list
  | Nis'25 => [state_set_7; state_set_3]%list
  | Nis'26 => [state_set_15; state_set_7; state_set_3]%list
  | Nis'27 => [state_set_7; state_set_3]%list
  | Nis'28 => [state_set_16; state_set_7; state_set_3]%list
  | Nis'29 => [state_set_3]%list
  | Nis'30 => [state_set_17; state_set_3]%list
  | Nis'31 => [state_set_3]%list
  | Nis'32 => [state_set_18; state_set_3]%list
  | Nis'33 => [state_set_3]%list
  | Nis'34 => [state_set_19; state_set_3]%list
  | Nis'35 => [state_set_3]%list
  | Nis'36 => [state_set_20; state_set_3]%list
  | Nis'37 => [state_set_3]%list
  | Nis'38 => [state_set_21; state_set_3]%list
  | Nis'39 => [state_set_3]%list
  | Nis'40 => [state_set_22; state_set_3]%list
  | Nis'41 => [state_set_23; state_set_1]%list
  | Nis'42 => [state_set_24; state_set_2]%list
  | Nis'43 => [state_set_24; state_set_2]%list
  | Nis'44 => [state_set_24; state_set_2]%list
  | Nis'45 => [state_set_2]%list
  | Nis'46 => [state_set_25]%list
  | Nis'47 => [state_set_25]%list
  | Nis'48 => [state_set_1]%list
  | Nis'49 => [state_set_26; state_set_1]%list
  | Nis'50 => [state_set_27; state_set_26; state_set_1]%list
  | Nis'51 => [state_set_25]%list
  | Nis'52 => [state_set_25]%list
  | Nis'53 => [state_set_25]%list
  | Nis'54 => [state_set_25]%list
  | Nis'55 => [state_set_28; state_set_25]%list
  | Nis'56 => [state_set_29; state_set_28; state_set_25]%list
  | Nis'57 => [state_set_30]%list
  | Nis'58 => [state_set_30; state_set_29; state_set_28; state_set_25]%list
  | Nis'59 => [state_set_31; state_set_30]%list
  | Nis'60 => [state_set_31; state_set_30; state_set_29; state_set_28; state_set_25]%list
  | Nis'61 => [state_set_32]%list
  | Nis'62 => [state_set_25]%list
  | Nis'63 => [state_set_33; state_set_25]%list
  | Nis'64 => [state_set_34; state_set_33; state_set_25]%list
  | Nis'65 => [state_set_35]%list
  | Nis'66 => [state_set_36; state_set_35]%list
  | Nis'67 => [state_set_37]%list
  | Nis'68 => [state_set_38; state_set_37]%list
  | Nis'69 => [state_set_39; state_set_38; state_set_37]%list
  | Nis'70 => [state_set_1]%list
  | Nis'71 => [state_set_25]%list
  | Nis'72 => [state_set_25]%list
  | Nis'73 => [state_set_40]%list
  | Nis'74 => [state_set_41; state_set_40]%list
  | Nis'75 => [state_set_25]%list
  | Nis'76 => [state_set_1]%list
  | Nis'77 => [state_set_1]%list
  | Nis'78 => [state_set_42; state_set_1]%list
  | Nis'79 => [state_set_43; state_set_42; state_set_1]%list
  | Nis'80 => [state_set_42; state_set_1]%list
  | Nis'81 => [state_set_42; state_set_1]%list
  | Nis'82 => [state_set_1]%list
  | Nis'83 => [state_set_25]%list
  | Nis'84 => [state_set_1]%list
  | Nis'85 => [state_set_25]%list
  | Nis'86 => [state_set_1]%list
  | Nis'87 => [state_set_44; state_set_1]%list
  | Nis'88 => [state_set_46; state_set_45]%list
  | Nis'89 => [state_set_45]%list
  | Nis'90 => [state_set_40]%list
  | Nis'91 => [state_set_47; state_set_40]%list
  | Nis'92 => [state_set_48; state_set_41; state_set_40]%list
  | Nis'93 => [state_set_25]%list
  | Nis'94 => [state_set_25]%list
  | Nis'95 => [state_set_49; state_set_39; state_set_38; state_set_37]%list
  | Nis'96 => [state_set_50; state_set_49; state_set_39; state_set_38; state_set_37]%list
  | Nis'97 => [state_set_51; state_set_34; state_set_33; state_set_25]%list
  | Nis'98 => [state_set_37]%list
  | Nis'99 => [state_set_52; state_set_37]%list
  | Nis'100 => [state_set_53; state_set_52; state_set_37]%list
  | Nis'101 => [state_set_54; state_set_53; state_set_52; state_set_37]%list
  | Nis'102 => [state_set_51; state_set_34; state_set_33; state_set_25]%list
  | Nis'103 => [state_set_55; state_set_51; state_set_34; state_set_33; state_set_25]%list
  | Nis'104 => [state_set_37]%list
  | Nis'105 => [state_set_56; state_set_37]%list
  | Nis'106 => [state_set_57; state_set_32]%list
  | Nis'107 => [state_set_58; state_set_57; state_set_32]%list
  | Nis'108 => [state_set_59; state_set_31; state_set_30; state_set_29; state_set_28; state_set_25]%list
  | Nis'109 => [state_set_29; state_set_28; state_set_25]%list
  | Nis'110 => [state_set_60; state_set_25]%list
  | Nis'111 => [state_set_61; state_set_60; state_set_25]%list
  | Nis'112 => [state_set_62; state_set_61; state_set_60; state_set_25]%list
  | Nis'113 => [state_set_63; state_set_62; state_set_61; state_set_60; state_set_25]%list
  | Nis'114 => [state_set_64]%list
  | Nis'115 => [state_set_65; state_set_64]%list
  | Nis'116 => [state_set_64]%list
  | Nis'117 => [state_set_66; state_set_64]%list
  | Nis'118 => [state_set_67; state_set_66; state_set_64]%list
  | Nis'119 => [state_set_68; state_set_67; state_set_66; state_set_64]%list
  | Nis'120 => [state_set_69; state_set_68; state_set_67; state_set_66; state_set_64]%list
  | Nis'121 => [state_set_63; state_set_62; state_set_61; state_set_60; state_set_25]%list
  | Nis'122 => [state_set_70; state_set_63; state_set_62; state_set_61; state_set_60; state_set_25]%list
  | Nis'123 => [state_set_71; state_set_25]%list
  | Nis'124 => [state_set_72; state_set_71; state_set_25]%list
  | Nis'125 => [state_set_73; state_set_25]%list
  | Nis'126 => [state_set_74; state_set_73; state_set_25]%list
  | Nis'127 => [state_set_75; state_set_27; state_set_26; state_set_1]%list
  | Nis'128 => [state_set_75]%list
  | Nis'129 => [state_set_76; state_set_75]%list
  | Nis'130 => [state_set_77; state_set_25]%list
  | Nis'131 => [state_set_78; state_set_77; state_set_25]%list
  | Nis'132 => [state_set_79; state_set_78; state_set_77; state_set_25]%list
  | Nis'133 => [state_set_80; state_set_25]%list
  | Nis'134 => [state_set_81; state_set_80; state_set_25]%list
  | Nis'135 => [state_set_82; state_set_81; state_set_80; state_set_25]%list
  | Nis'136 => [state_set_83]%list
  | Nis'137 => [state_set_84; state_set_83]%list
  | Nis'138 => [state_set_86; state_set_85]%list
  | Nis'139 => [state_set_87; state_set_86; state_set_85]%list
  | Nis'140 => [state_set_85]%list
  | Nis'142 => [state_set_83]%list
  | Nis'143 => [state_set_88]%list
  | Nis'144 => [state_set_89]%list
  | Nis'145 => [state_set_89]%list
  | Nis'146 => [state_set_89; state_set_88]%list
  | Nis'147 => [state_set_90; state_set_89; state_set_88]%list
  | Nis'148 => [state_set_91; state_set_83]%list
  | Nis'149 => [state_set_92; state_set_91; state_set_83]%list
  | Nis'150 => [state_set_91; state_set_83]%list
  | Nis'151 => [state_set_93; state_set_91; state_set_83]%list
  | Nis'152 => [state_set_88]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition items_of_state (s:state): list item := []%list.
Extract Constant items_of_state => "fun _ -> assert false".

Definition N_of_state (s:state) : N :=
  match s with
  | Init Init'0 => 0%N
  | Ninit Nis'1 => 1%N
  | Ninit Nis'2 => 2%N
  | Ninit Nis'3 => 3%N
  | Ninit Nis'4 => 4%N
  | Ninit Nis'5 => 5%N
  | Ninit Nis'6 => 6%N
  | Ninit Nis'7 => 7%N
  | Ninit Nis'8 => 8%N
  | Ninit Nis'9 => 9%N
  | Ninit Nis'10 => 10%N
  | Ninit Nis'11 => 11%N
  | Ninit Nis'12 => 12%N
  | Ninit Nis'13 => 13%N
  | Ninit Nis'14 => 14%N
  | Ninit Nis'15 => 15%N
  | Ninit Nis'16 => 16%N
  | Ninit Nis'17 => 17%N
  | Ninit Nis'18 => 18%N
  | Ninit Nis'19 => 19%N
  | Ninit Nis'20 => 20%N
  | Ninit Nis'21 => 21%N
  | Ninit Nis'22 => 22%N
  | Ninit Nis'23 => 23%N
  | Ninit Nis'24 => 24%N
  | Ninit Nis'25 => 25%N
  | Ninit Nis'26 => 26%N
  | Ninit Nis'27 => 27%N
  | Ninit Nis'28 => 28%N
  | Ninit Nis'29 => 29%N
  | Ninit Nis'30 => 30%N
  | Ninit Nis'31 => 31%N
  | Ninit Nis'32 => 32%N
  | Ninit Nis'33 => 33%N
  | Ninit Nis'34 => 34%N
  | Ninit Nis'35 => 35%N
  | Ninit Nis'36 => 36%N
  | Ninit Nis'37 => 37%N
  | Ninit Nis'38 => 38%N
  | Ninit Nis'39 => 39%N
  | Ninit Nis'40 => 40%N
  | Ninit Nis'41 => 41%N
  | Ninit Nis'42 => 42%N
  | Ninit Nis'43 => 43%N
  | Ninit Nis'44 => 44%N
  | Ninit Nis'45 => 45%N
  | Ninit Nis'46 => 46%N
  | Ninit Nis'47 => 47%N
  | Ninit Nis'48 => 48%N
  | Ninit Nis'49 => 49%N
  | Ninit Nis'50 => 50%N
  | Ninit Nis'51 => 51%N
  | Ninit Nis'52 => 52%N
  | Ninit Nis'53 => 53%N
  | Ninit Nis'54 => 54%N
  | Ninit Nis'55 => 55%N
  | Ninit Nis'56 => 56%N
  | Ninit Nis'57 => 57%N
  | Ninit Nis'58 => 58%N
  | Ninit Nis'59 => 59%N
  | Ninit Nis'60 => 60%N
  | Ninit Nis'61 => 61%N
  | Ninit Nis'62 => 62%N
  | Ninit Nis'63 => 63%N
  | Ninit Nis'64 => 64%N
  | Ninit Nis'65 => 65%N
  | Ninit Nis'66 => 66%N
  | Ninit Nis'67 => 67%N
  | Ninit Nis'68 => 68%N
  | Ninit Nis'69 => 69%N
  | Ninit Nis'70 => 70%N
  | Ninit Nis'71 => 71%N
  | Ninit Nis'72 => 72%N
  | Ninit Nis'73 => 73%N
  | Ninit Nis'74 => 74%N
  | Ninit Nis'75 => 75%N
  | Ninit Nis'76 => 76%N
  | Ninit Nis'77 => 77%N
  | Ninit Nis'78 => 78%N
  | Ninit Nis'79 => 79%N
  | Ninit Nis'80 => 80%N
  | Ninit Nis'81 => 81%N
  | Ninit Nis'82 => 82%N
  | Ninit Nis'83 => 83%N
  | Ninit Nis'84 => 84%N
  | Ninit Nis'85 => 85%N
  | Ninit Nis'86 => 86%N
  | Ninit Nis'87 => 87%N
  | Ninit Nis'88 => 88%N
  | Ninit Nis'89 => 89%N
  | Ninit Nis'90 => 90%N
  | Ninit Nis'91 => 91%N
  | Ninit Nis'92 => 92%N
  | Ninit Nis'93 => 93%N
  | Ninit Nis'94 => 94%N
  | Ninit Nis'95 => 95%N
  | Ninit Nis'96 => 96%N
  | Ninit Nis'97 => 97%N
  | Ninit Nis'98 => 98%N
  | Ninit Nis'99 => 99%N
  | Ninit Nis'100 => 100%N
  | Ninit Nis'101 => 101%N
  | Ninit Nis'102 => 102%N
  | Ninit Nis'103 => 103%N
  | Ninit Nis'104 => 104%N
  | Ninit Nis'105 => 105%N
  | Ninit Nis'106 => 106%N
  | Ninit Nis'107 => 107%N
  | Ninit Nis'108 => 108%N
  | Ninit Nis'109 => 109%N
  | Ninit Nis'110 => 110%N
  | Ninit Nis'111 => 111%N
  | Ninit Nis'112 => 112%N
  | Ninit Nis'113 => 113%N
  | Ninit Nis'114 => 114%N
  | Ninit Nis'115 => 115%N
  | Ninit Nis'116 => 116%N
  | Ninit Nis'117 => 117%N
  | Ninit Nis'118 => 118%N
  | Ninit Nis'119 => 119%N
  | Ninit Nis'120 => 120%N
  | Ninit Nis'121 => 121%N
  | Ninit Nis'122 => 122%N
  | Ninit Nis'123 => 123%N
  | Ninit Nis'124 => 124%N
  | Ninit Nis'125 => 125%N
  | Ninit Nis'126 => 126%N
  | Ninit Nis'127 => 127%N
  | Ninit Nis'128 => 128%N
  | Ninit Nis'129 => 129%N
  | Ninit Nis'130 => 130%N
  | Ninit Nis'131 => 131%N
  | Ninit Nis'132 => 132%N
  | Ninit Nis'133 => 133%N
  | Ninit Nis'134 => 134%N
  | Ninit Nis'135 => 135%N
  | Ninit Nis'136 => 136%N
  | Ninit Nis'137 => 137%N
  | Ninit Nis'138 => 138%N
  | Ninit Nis'139 => 139%N
  | Ninit Nis'140 => 140%N
  | Ninit Nis'142 => 142%N
  | Ninit Nis'143 => 143%N
  | Ninit Nis'144 => 144%N
  | Ninit Nis'145 => 145%N
  | Ninit Nis'146 => 146%N
  | Ninit Nis'147 => 147%N
  | Ninit Nis'148 => 148%N
  | Ninit Nis'149 => 149%N
  | Ninit Nis'150 => 150%N
  | Ninit Nis'151 => 151%N
  | Ninit Nis'152 => 152%N
  end.
End Aut.

Module MenhirLibParser := MenhirLib.Main.Make Aut.
Theorem safe:
  MenhirLibParser.safe_validator tt = true.
Proof eq_refl true<:MenhirLibParser.safe_validator tt = true.

Definition program : nat -> MenhirLibParser.Inter.buffer -> MenhirLibParser.Inter.parse_result        (FullAst.exp) := MenhirLibParser.parse safe Aut.Init'0.

Theorem program_correct (log_fuel : nat) (buffer : MenhirLibParser.Inter.buffer):
  match program log_fuel buffer with
  | MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : Gram.parse_tree (NT program'nt) word),
        buffer = MenhirLibParser.Inter.app_buf word buffer_new /\
        Gram.pt_sem tree = sem
  | _ => True
  end.
Proof. apply MenhirLibParser.parse_correct with (init:=Aut.Init'0). Qed.


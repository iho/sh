(lang dune 3.8)

(using menhir 2.1)
(using coq 0.8)

(package
 (name ush)
 (version 0.0.1)
 (depends ocaml dune zarith menhir coq coq-simple-io))

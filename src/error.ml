exception Parser of int * string * string

let prettyPrintExn : exn -> unit = function
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintExn ex; default

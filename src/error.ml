exception Parser of int * string * string

type 'a result =
  | Ok of 'a
  | Error of string

let prettyPrintExn : exn -> unit = function
  | ex -> Printf.printf "Uncaught exception: %s\n" (Printexc.to_string ex)

let prettyPrintError : string -> unit = function
  | msg -> Printf.printf "Error: %s\n" msg

let handleErrors (f : 'a -> 'b result) (x : 'a) (default : 'b) : 'b =
  match f x with
  | Ok result -> result
  | Error msg -> prettyPrintError msg; default

(* Note: safeCall removed for Coq compatibility - all functions should return result types directly *)

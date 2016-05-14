open Syntax
open Mgmt
open Nk


(* === Proof assistant interface === *)
let pipein = not (Unix.isatty Unix.stdin)
let lexbuf = Lexing.from_channel stdin
let read_command : unit -> command = fun () ->
  try
    let com = Parser.main Lexer.token lexbuf in
    if pipein then Printf.printf "%s\n" (string_of_command com);
    com
  with
    Parsing.Parse_error -> print_endline "parse error"; Invalid
  | Lexer.Eof -> print_endline "eof exiting"; exit 0

let rec prove : sequent list -> unit = function
  | h::t ->
     begin
       Printf.printf "Current goal: %s\n" (string_of_sequent h);
       print_string "> "; flush stdout;
       match (read_command ()) with
         Axiom -> prove ((axiom h)@t)
       | Impl_i -> prove ((impl_i h)@t)
       | Impl_e a -> prove ((impl_e (dbix a) h)@t)
       | And_i -> prove ((and_i h)@t)
       | And_e_l a -> prove ((and_e_l (dbix a) h)@t)
       | And_e_r a -> prove ((and_e_r (dbix a) h)@t)
       | Or_i_l -> prove ((or_i_l h)@t)
       | Or_i_r -> prove ((or_i_r h)@t)
       | Or_e (a,b) -> prove ((or_e (dbix a) (dbix b) h)@t)
       | Not_i -> prove ((not_i h)@t)
       | Not_e a -> prove ((not_e (dbix a) h)@t)
       | Forall_i -> prove ((forall_i h)@t)
       | Forall_e a -> prove ((forall_e (dbix a) h)@t)
       | Exists_i s -> prove ((exists_i s h)@t)
       | Exists_e a -> prove ((exists_e (dbix a) h)@t)
       | Absurd ->  prove ((absurd h)@t)
       | Prove _ -> failwith "finish the current proof first"
       | _ -> failwith "invalid command"
     end
  | [] -> print_endline "done"


(* === Main === *)
let _ =
  while true do
    print_string "> "; flush stdout;
    match (read_command ()) with
      Prove s -> prove [(sequent_de_bruijn_index s)]
    | _ -> print_endline "No!"
  done

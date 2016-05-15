open Syntax
open Mgmt
open Nk
open Proof


(* === Proof assistant interface === *)
let pipein = not (Unix.isatty Unix.stdin)
let lexbuf = Lexing.from_channel stdin
let read_command : unit -> command = fun () ->
  try
    let com = Parser.main Lexer.token lexbuf in
    if pipein then Printf.printf "%s\n" (string_of_command com);
    com
  with
    Parsing.Parse_error -> Printf.eprintf "Error: Parsing error\n"; Invalid
  | Lexer.Eof -> Printf.eprintf "EOF exit\n"; exit 0

let rec prove : sequent -> proof = fun h ->
  Printf.printf "Current goal: %s\n" (string_of_sequent h);
  Printf.printf "> "; flush stdout;
  match (read_command ()) with
    Axiom -> Rule (h, List.map prove (axiom h))
  | Impl_i -> Rule (h, List.map prove (impl_i h))
  | Impl_e a -> Rule (h, List.map prove (impl_e (dbix a) h))
  | And_i -> Rule (h, List.map prove (and_i h))
  | And_e_l a -> Rule (h, List.map prove (and_e_l (dbix a) h))
  | And_e_r a -> Rule (h, List.map prove (and_e_r (dbix a) h))
  | Or_i_l -> Rule (h, List.map prove (or_i_l h))
  | Or_i_r -> Rule (h, List.map prove (or_i_r h))
  | Or_e (a,b) -> Rule (h, List.map prove (or_e (dbix a) (dbix b) h))
  | Not_i -> Rule (h, List.map prove (not_i h))
  | Not_e a -> Rule (h, List.map prove (not_e (dbix a) h))
  | Forall_i -> Rule (h, List.map prove (forall_i h))
  | Forall_e a -> Rule (h, List.map prove (forall_e (dbix a) h))
  | Exists_i s -> Rule (h, List.map prove (exists_i s h))
  | Exists_e a -> Rule (h, List.map prove (exists_e (dbix a) h))
  | Absurd -> Rule (h, List.map prove (absurd h))
  | Prove _ -> Printf.eprintf "Error: invalid command here\n"; prove h
  | _ -> Printf.eprintf "Error: invalid command here\n"; prove h


(* === Main === *)
let _ =
  while true do
    Printf.printf "> "; flush stdout;
    match (read_command ()) with
      Prove s ->
	export_proof "out.tex" (prove (sequent_de_bruijn_index s));
	Printf.printf "Proof done\n"
    | _ -> Printf.eprintf "Error: Invalid command here\n"
  done

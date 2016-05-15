open Syntax
open Mgmt
open Nk
open Proof
open Env


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
    Axiom -> Rule (h, "\\textrm{\\small ax}", List.map prove (axiom h))
  | Impl_i -> Rule (h, "\\Rightarrow_i", List.map prove (impl_i h))
  | Impl_e a -> Rule (h, "\\Rightarrow_e", List.map prove (impl_e (dbix a) h))
  | And_i -> Rule (h, "\\wedge_i", List.map prove (and_i h))
  | And_e_l a -> Rule (h, "\\wedge_e^l", List.map prove (and_e_l (dbix a) h))
  | And_e_r a -> Rule (h, "\\wedge_e^r", List.map prove (and_e_r (dbix a) h))
  | Or_i_l -> Rule (h, "\\vee_i^l", List.map prove (or_i_l h))
  | Or_i_r -> Rule (h, "\\vee_i^r", List.map prove (or_i_r h))
  | Or_e (a,b) -> Rule (h, "\\vee_e", List.map prove (or_e (dbix a) (dbix b) h))
  | Not_i -> Rule (h, "\\neg_i", List.map prove (not_i h))
  | Not_e a -> Rule (h, "\\neg_e", List.map prove (not_e (dbix a) h))
  | Forall_i -> Rule (h, "\\forall_i", List.map prove (forall_i h))
  | Forall_e a -> Rule (h, "\\forall_e", List.map prove (forall_e (dbix a) h))
  | Exists_i s -> Rule (h, "\\exists_i", List.map prove (exists_i s h))
  | Exists_e a -> Rule (h, "\\exists_e", List.map prove (exists_e (dbix a) h))
  | Absurd -> Rule (h, "\\bot_c", List.map prove (absurd h))
  | Invalid -> Printf.eprintf "Error: invalid command\n"; prove h
  | _ -> Printf.eprintf "Error: invalid command here\n"; prove h



(* === Main === *)
let _ =
  while true do
    Printf.printf "> "; flush stdout;
    match (read_command ()) with
      Prove s ->
	let s = sequent_de_bruijn_index s in
	let p =	prove s in
	env_push s p;
	Printf.printf "Proof done, saved as %s\n" (env_hd_id ())
    | Export tid ->
       begin
	 match env_get tid with
	   Some (_,p) ->
	     let fn = Printf.sprintf "%s.tex" tid in
	     export_proof (Printf.sprintf "%s.tex" tid) p;
	     Printf.printf "Proof exported to %s\n" fn
	 | None -> Printf.eprintf "Error: Theorem not found\n"
       end
    | Listenv -> print_env ()
    | _ -> Printf.eprintf "Error: Invalid command here\n"
  done

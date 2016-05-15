open Syntax
open Proof

type thm_id = string
type env_thm = thm_id * (sequent * proof)
type env = env_thm list


(* === Environment management === *)
let env : env ref = ref []
let thm_count = ref 0
let fresh_thm_id : unit -> thm_id = fun () ->
  incr thm_count;
  Printf.sprintf "th%d" !thm_count

let env_push : sequent -> proof -> unit = fun t p ->
  env := (fresh_thm_id (), (t,p))::(!env)

let env_get : thm_id -> (sequent * proof) option = fun tid ->
  try Some (List.assoc tid !env)
  with Not_found -> None

let env_hd_id : unit -> thm_id = fun () ->
  fst (List.hd !env)

let print_env : unit -> unit = fun () ->
  List.iter (fun (tid,(s,_)) -> Printf.printf "%s: %s\n" tid (string_of_sequent s)) !env

open Syntax

type proof = Rule of sequent * (proof list)

    
(* === LaTeX proof package proof tree export === *)
let rec latex_of_term : term -> string = function
  | Var id -> id
  | BVar id -> Printf.sprintf "x_%d" id
  | Func (id,[]) -> id
  | Func (id,tl) -> Printf.sprintf "%s(%s)" id (latex_of_term_list tl)

and latex_of_term_list : term list -> string = function
  | [] -> ""
  | [h] -> latex_of_term h
  | h::t -> Printf.sprintf "%s, %s" (latex_of_term h) (latex_of_term_list t)

let rec latex_of_formula : formula -> string = function
  | Pred (id,[]) -> id
  | Pred (id,tl) -> Printf.sprintf "%s(%s)" id (latex_of_term_list tl)
  | Bot -> "\\bot"
  | Or (a,b) -> Printf.sprintf "%s \\vee %s" (latex_of_formula a) (latex_of_formula b)
  | And (a,b) -> Printf.sprintf "%s \\wedge %s" (latex_of_formula a) (latex_of_formula b)
  | Impl (a,b) -> Printf.sprintf "%s \\Rightarrow %s" (latex_of_formula a) (latex_of_formula b)
  | Not a -> Printf.sprintf "\\neg %s" (latex_of_formula a)
  | BForall (id,a) -> Printf.sprintf "\\forall x_%d %s" id (latex_of_formula a)
  | BExists (id,a) -> Printf.sprintf "\\exists x_%d %s" id (latex_of_formula a)
  | _ -> failwith "latex_of_formula"

and latex_of_formula_list : formula list -> string = function
  | [] -> ""
  | [h] -> latex_of_formula h
  | h::t -> Printf.sprintf "%s, %s" (latex_of_formula h) (latex_of_formula_list t)

let latex_of_sequent : sequent -> string = fun (hyp,a) ->
  Printf.sprintf "%s \\vdash %s" (latex_of_formula_list hyp) (latex_of_formula a)

let rec latex_of_proof : proof -> string = function
  | Rule (s,pl) -> Printf.sprintf "\\infer{%s}{%s}\n" (latex_of_sequent s) (latex_of_proof_list pl)

and latex_of_proof_list : proof list -> string = function
  | [h] -> latex_of_proof h
  | h::t -> Printf.sprintf "%s & %s" (latex_of_proof h) (latex_of_proof_list t)
  | _ -> ""

let export_proof : string -> proof -> unit = fun fn p ->
  let f = open_out fn in
  Printf.fprintf f "\\documentclass[border=1mm]{standalone}\n";
  Printf.fprintf f "\\usepackage{proof}\n";
  Printf.fprintf f "\\begin{document}\n";
  Printf.fprintf f "$%s$\n" (latex_of_proof p);
  Printf.fprintf f "\\end{document}\n";
  close_out f

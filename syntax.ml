(* === Type declarations === *)
type var_id = string
type bvar_id = int (* de Bruijn index *)
type func_id = string
type pred_id = string
  
type term =
    Var of var_id
  | BVar of bvar_id
  | Func of func_id * (term list)

type formula =
    Pred of pred_id * (term list)
  | Bot
  | Or of formula * formula
  | And of formula * formula
  | Impl of formula * formula
  | Not of formula
  | Forall of var_id * formula
  | Exists of var_id * formula
  | BForall of bvar_id * formula
  | BExists of bvar_id * formula

type sequent = (formula list) * formula

type command =
    Axiom
  | Impl_i
  | Impl_e of formula
  | And_i
  | And_e_l of formula
  | And_e_r of formula
  | Or_i_l
  | Or_i_r
  | Or_e of formula * formula
  | Not_i
  | Not_e of formula
  | Absurd
  | Forall_i
  | Forall_e of term
  | Exists_i of term
  | Exists_e of formula
  | Prove of sequent
  | Invalid

type scope = (var_id * bvar_id) list


(* === Auxiliary functions === *)
let scope_push : scope -> var_id -> scope = fun s id ->
  match s with
    [] -> [(id,0)]
  | (_,n)::t -> (id,n+1)::s

let scope_find : scope -> var_id -> bvar_id option = fun s id ->
  try Some (List.assoc id s)
  with Not_found -> None


(* === Printing functions === *)
let rec string_of_term : term -> string = function
  | Var id -> id
  | BVar id -> Printf.sprintf "x_%d" id
  | Func (id,[]) -> id
  | Func (id,tl) -> Printf.sprintf "%s(%s)" id (string_of_term_list tl)

and string_of_term_list : term list -> string = function
  | [] -> ""
  | [h] -> string_of_term h
  | h::t -> Printf.sprintf "%s, %s" (string_of_term h) (string_of_term_list t)
     
let rec string_of_formula : formula -> string = function
  | Pred (id,[]) -> id
  | Pred (id,tl) -> Printf.sprintf "%s(%s)" id (string_of_term_list tl)
  | Bot -> "_|_"
  | Or (a,b) -> Printf.sprintf "%s \\/ %s" (string_of_formula a) (string_of_formula b)
  | And (a,b) -> Printf.sprintf "%s /\\ %s" (string_of_formula a) (string_of_formula b)
  | Impl (a,b) -> Printf.sprintf "%s => %s" (string_of_formula a) (string_of_formula b)
  | Not a -> Printf.sprintf "not %s" (string_of_formula a)
  | Forall (id,a) -> Printf.sprintf "A %s, %s" id (string_of_formula a)
  | Exists (id,a) -> Printf.sprintf "E %s, %s" id (string_of_formula a)
  | BForall (id,a) -> Printf.sprintf "A x_%d, %s" id (string_of_formula a)
  | BExists (id,a) -> Printf.sprintf "E x_%d, %s" id (string_of_formula a)

and string_of_formula_list : formula list -> string = function
  | [] -> ""
  | [h] -> string_of_formula h
  | h::t -> Printf.sprintf "%s; %s" (string_of_formula h) (string_of_formula_list t)
     
let string_of_sequent : sequent -> string = fun (hyp,a) ->
  Printf.sprintf "%s |- %s" (string_of_formula_list hyp) (string_of_formula a)

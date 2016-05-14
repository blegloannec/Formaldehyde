open Syntax


(* === De Bruijn indexes management === *)
let rec term_de_bruijn_index : scope -> term -> term = fun s -> function
  | Var id as v ->
     begin
       match scope_find s id with
       | Some bid -> BVar bid
       | None -> v
     end
  | Func (id,tl) -> Func (id, terml_de_bruijn_index s tl)
  | _ -> failwith "term_de_bruijn_index: invalid variable"

and terml_de_bruijn_index : scope -> term list -> term list = fun s tl ->
  List.map (term_de_bruijn_index s) tl
     
let rec de_bruijn_index : scope -> formula -> formula = fun s -> function
  | Pred (id,tl) -> Pred (id, terml_de_bruijn_index s tl)
  | Bot -> Bot
  | Or (a,b) -> Or ((de_bruijn_index s a), (de_bruijn_index s b))
  | And (a,b) -> And ((de_bruijn_index s a), (de_bruijn_index s b))
  | Impl (a,b) -> Impl ((de_bruijn_index s a), (de_bruijn_index s b))
  | Not a -> Not (de_bruijn_index s a)
  | Forall (id,a) ->
     let ns = scope_push s id in
     BForall ((snd (List.hd ns)), de_bruijn_index ns a)
  | Exists (id,a) ->
     let ns = scope_push s id in
     BExists ((snd (List.hd ns)), de_bruijn_index ns a)
  | _ -> failwith "de_bruijn_index: invalid quantifier"

let dbix : formula -> formula = de_bruijn_index []
     
let sequent_de_bruijn_index : sequent -> sequent = fun (hyp,a) ->
  ((List.map dbix hyp), dbix a)
     
let rec term_index_decr : term -> term -> term = fun s -> function
  | BVar 0 -> s
  | BVar n -> BVar (n-1)
  | Func (id,tl) -> Func (id, terml_index_decr s tl)
  | t -> t

and terml_index_decr : term -> term list -> term list = fun s tl ->
  List.map (term_index_decr s) tl
     
let rec index_decr : term -> formula -> formula = fun s -> function
  | Pred (id,tl) -> Pred (id, terml_index_decr s tl)
  | Bot -> Bot
  | Or (a,b) -> Or ((index_decr s a), (index_decr s b))
  | And (a,b) -> And ((index_decr s a), (index_decr s b))
  | Impl (a,b) -> Impl ((index_decr s a), (index_decr s b))
  | Not a -> Not (index_decr s a)
  | BForall (id,a) when id>0 -> BForall (id-1, (index_decr s a))
  | BExists (id,a) when id>0 -> BExists (id-1, (index_decr s a))
  | _ -> failwith "index_decr: invalid quantifier"


(* === Free variables management === *)
let rec term_free_variables : term -> var_id list = function
  | Var id -> [id]
  | BVar _ -> []
  | Func (_,tl) -> terml_free_variables tl

and terml_free_variables : term list -> var_id list = fun tl ->
  List.fold_left (fun l t -> (term_free_variables t)@l) [] tl
     
let rec free_variables : formula -> var_id list = function
  | Pred (_,tl) -> terml_free_variables tl
  | Bot -> []
  | Or (a,b) | And (a,b) | Impl (a,b)-> (free_variables a)@(free_variables b)
  | Not a | BForall (_,a) | BExists (_,a)-> free_variables a
  | _ -> failwith "free_variables: invalid quantifier"

let free_vars : formula list -> var_id list =
  List.fold_left (fun l f -> (free_variables f)@l) []

let fresh_free_name : var_id list -> var_id = fun l ->
  let rec aux n =
    let id = Printf.sprintf "y%d" n in
    if List.mem (Printf.sprintf "y%d" n) l then aux (n+1)
    else id
  in aux 0

open Syntax

(* === De Bruijn indices management === *)
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


(* === NK proof system === *)
let axiom : sequent -> sequent list = fun (hyp,a) ->
  if (List.mem a hyp) then []
  else failwith "axiom"
  
let impl_i : sequent -> sequent list = function
  | hyp, Impl (a,b) -> [(a::hyp,b)]
  | _ -> failwith "impl_i"

let impl_e : formula -> sequent -> sequent list = fun a (hyp,b) ->
  [(hyp,Impl (a,b)); (hyp,a)]

let and_i : sequent -> sequent list = function
  | hyp, And (a,b) -> [(hyp,a); (hyp,b)]
  | _ -> failwith "and_i"

let and_e_l : formula -> sequent -> sequent list = fun b (hyp,a) ->
  [(hyp,And (a,b))]

let and_e_r : formula -> sequent -> sequent list = fun a (hyp,b) ->
  [(hyp,And (a,b))]

let or_i_l : sequent -> sequent list = function
  | hyp, Or (a,b) -> [(hyp,a)]
  | _ -> failwith "or_i_l"

let or_i_r : sequent -> sequent list = function
  | hyp, Or (a,b) -> [(hyp,b)]
  | _ -> failwith "or_i_r"

let or_e : formula -> formula -> sequent -> sequent list = fun a b (hyp,c) ->
  [(hyp,Or (a,b)); (a::hyp,c); (b::hyp,c)]

let not_i : sequent -> sequent list = function
  | hyp,Not a -> [(a::hyp,Bot)]
  | _ -> failwith "not_i"

let not_e : formula -> sequent -> sequent list = fun a -> function
  | hyp,Bot -> [(hyp,Not a); (hyp,a)]
  | _ -> failwith "not_e"

let absurd : sequent -> sequent list = fun (hyp,a) ->
  [((Not a)::hyp,Bot)]

let forall_i : sequent -> sequent list = function
  | hyp,BForall (0,a) ->
     let fid = fresh_free_name (free_vars hyp) in
     [(hyp, (index_decr (Var fid) a))]
  | _ -> failwith "forall_i"

let exists_i : term -> sequent -> sequent list = fun t -> function
  | hyp,BExists(0,a) -> [(hyp, index_decr t a)]
  | _ -> failwith "exists_i"
     
let exists_e : formula -> sequent -> sequent list = fun ea (hyp,c) ->
  match ea with
    BExists (0,b) ->
      let fid = fresh_free_name (free_vars (c::hyp)) in
      [(hyp,ea); ((index_decr (Var fid) ea)::hyp,c)]
  | _ -> failwith "exists_e"

let rec term_sub_check : term -> term -> (bool * (term option)) = fun s1 s2 ->
  match s1,s2 with
    BVar 0, t2 -> (true, Some t2)
  | BVar n1, BVar n2 when n1=n2 -> (true, None)
  | Func (id1,tl1), Func (id2,tl2) when id1=id2 -> terml_sub_check tl1 tl2
  | _ -> (false, None)

and terml_sub_check : term list -> term list -> (bool * (term option)) = fun tl1 tl2 ->
  match tl1,tl2 with
  | h1::t1, h2::t2 ->
     begin
       let r0 = term_sub_check h1 h2 and r = terml_sub_check t1 t2 in
       match r0,r with
	 (true, Some t1), (true, Some t2) when t1=t2 -> r0
       | (true, None), (true, _) -> r
       | (true, _), (true, None) -> r0
       | _ -> (false, None)
     end
  | [],[] -> (true, None)
  | _ -> (false, None)
  
     
let rec sub_check : formula -> formula -> (bool * (term option)) = fun f1 f2 ->
  match f1,f2 with
  | Pred (id1,tl1), Pred(id2,tl2) when id1=id2 -> terml_sub_check tl1 tl2
  | Bot,Bot -> (true, None)
  | Or (a1,b1), Or (a2,b2) ->
     begin
       let r1 = sub_check a1 a2 and r2 = sub_check b1 b2 in
       match r1,r2 with
	 (true, Some t1), (true, Some t2) when t1=t2 -> r1
       | (true, None), (true, _) -> r2
       | (true, _), (true, None) -> r1
       | _ -> (false, None)
     end
  | And (a1,b1), And (a2,b2) ->
     begin
       let r1 = sub_check a1 a2 and r2 = sub_check b1 b2 in
       match r1,r2 with
	 (true, Some t1), (true, Some t2) -> if t1=t2 then r1 else (false,None)
       | (true, None), (true, _) -> r2
       | (true, _), (true, None) -> r1
       | _ -> (false, None)
     end
  | Impl (a1,b1), Impl (a2,b2) ->
     begin
       let r1 = sub_check a1 a2 and r2 = sub_check b1 b2 in
       match r1,r2 with
	 (true, Some t1), (true, Some t2) -> if t1=t2 then r1 else (false,None)
       | (true, None), (true, _) -> r2
       | (true, _), (true, None) -> r1
       | _ -> (false, None)
     end
  | Not a1, Not a2 -> sub_check a1 a2
  | Forall (id1,a1), Forall (id2, a2) when id1=id2 -> sub_check a1 a2
  | Exists (id1,a1), Exists (id2,a2) when id1=id2 -> sub_check a1 a2
  | _ -> (false,None)
     
let forall_e : formula -> sequent -> sequent list = fun fa (hyp,a) ->
  match fa with
    BForall (0,a0) when (fst (sub_check a0 a)) -> [(hyp,fa)]
  | _ -> failwith "forall_e"


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

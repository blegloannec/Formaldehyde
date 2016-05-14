open Syntax
open Mgmt


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
      [(hyp,ea); ((index_decr (Var fid) b)::hyp,c)]
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

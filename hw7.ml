open List

type ident = string

type tident = int

type typ = Tint | Tbool | Tarrow of typ * typ | Ttuple of typ * typ
           | Tsum of typ * typ | Tvar of tident

type exp = Var of ident | Fun of ident * exp | App of exp * exp
           | Int of int | Bool of bool | Add of exp * exp | Eq of exp * exp
           | If of exp * exp * exp
           | Tuple of exp * exp | Fst of exp | Snd of exp
           | Inl of exp | Inr of exp
           | Match of exp * ident * exp * ident * exp

type context = ident -> typ option

let empty_context : context = fun _ -> None
let update g x t = fun y -> if y = x then Some t else g y
             
type constraints = (typ * typ) list

let next = ref 0

let fresh_tident (u : unit) : tident = next := !next + 1; !next
                
let rec get_constraints (gamma : context) (e : exp)
        : (typ * constraints) option =
  match e with
  | Var x -> (match gamma x with Some t -> Some (t, []) | None -> None)
  | Fun (x, e) ->
     let t1 = fresh_tident () in
     (match get_constraints (update gamma x (Tvar t1)) e with
      | Some (t2, c) -> Some (Tarrow (Tvar t1, t2), c)
      | None -> None)
  | App (e1, e2) ->
     (match get_constraints gamma e1, get_constraints gamma e2 with
      | Some (t1, c1), Some (t2, c2) ->
         let t = fresh_tident () in
         Some (Tvar t, (t1, Tarrow (t2, Tvar t)) :: c1 @ c2)
      | _, _ -> None)

  | Int i -> Some (Tint,[])

  | Bool b -> Some(Tbool,[])

  | Add(e1,e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some(t1,c1), Some(t2,c2) -> Some(Tint, ( (t1, Tint) :: (t2, Tint) :: c1 @ c2) )
                    | None, None -> None
                    | None, _ -> None
                    | _, None -> None )


  | Eq (e1,e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                    | Some(t1,c1), Some(t2,c2) -> Some(Tbool, ((t1,t2):: c1@ c2))
                    | None,None -> None
                    | _,None -> None
                    | None,_ -> None)


  | If (e1,e2,e3) -> (match get_constraints gamma e1, get_constraints gamma e2, get_constraints gamma e3 with
                    | Some(t,c), Some(t1,c1), Some(t2,c2) -> Some(t1, ((t,Tbool)::(t1,t2)::c@c1@c2))
                    | _,_,_ -> None)


  | Fst e -> let t1 = fresh_tident () in 
             let t2 = fresh_tident () in 
              (match get_constraints gamma e with
                | Some(t,c) -> Some(Tvar t1, (  (t, Ttuple(Tvar(t1), Tvar(t2)))  :: c))
                | None -> None)


  | Snd e -> let t1 = fresh_tident () in 
             let t2 = fresh_tident () in 
              (match get_constraints gamma e with
                | Some(t,c) -> Some(Tvar t2, (  (t, Ttuple(Tvar(t1), Tvar(t2)))  :: c))
                | None -> None)


  | Tuple(e1,e2) -> (match get_constraints gamma e1, get_constraints gamma e2 with
                      | Some(t1,c1), Some(t2,c2) -> Some( Ttuple(t1,t2), c1 @ c2 )
                      | _,_ -> None)


  | Inl e -> let t2 = fresh_tident () in 
              (match get_constraints gamma e with 
                | Some(t,c) -> Some(Tsum(t, Tvar t2), c)
                | _ -> None)


  | Inr e -> let t1 = fresh_tident () in
              ( match get_constraints gamma e with
                | Some(t,c) -> Some( Tsum(Tvar t1, t), c) 
                | _ -> None)


  | Match (e , i1,  e2, i2, e3) -> 
                let tl = fresh_tident () in
                let tr = fresh_tident () in 
                let tc = (match get_constraints gamma e with
                            | Some(t,c) -> Some(t,c) 
                            | _ -> None) in
                let t1c1 = (match get_constraints (update gamma i1 (Tvar tl) ) e2  with
                              | Some(t,c) -> Some(t,c) 
                              | _ -> None ) in
                let t2c2 = (match get_constraints (update gamma i2 (Tvar tr)) e3 with
                              | Some(t,c) -> Some(t,c)
                              | _ -> None) in
                (match tc, t1c1, t2c2 with
                | Some(t,c), Some(t1,c1), Some(t2,c2) -> Some(t1, (t, Tsum(Tvar tl, Tvar tr)) :: (t1,t2) :: c @ c1 @ c2 )
                | _,_,_ -> None)

           
(* unification: for testing purposes only *)
type substitution = tident -> typ option
let empty_subst : substitution = fun _ -> None

let single_subst x t : substitution = update empty_subst x t
                                        
let rec apply_subst (s : substitution) (t : typ) : typ =
  match t with
  | Tint -> Tint
  | Tbool -> Tbool
  | Tarrow (t1, t2) -> Tarrow (apply_subst s t1, apply_subst s t2)
  | Ttuple (t1, t2) -> Ttuple (apply_subst s t1, apply_subst s t2)
  | Tsum (t1, t2) -> Tsum (apply_subst s t1, apply_subst s t2)
  | Tvar x -> (match s x with Some t -> t | None -> Tvar x)

let compose_subst s1 s2 = fun x ->
  match s2 x with
  | Some t -> Some (apply_subst s1 t)
  | None -> s1 x

let apply_subst_c (s : substitution) (c : constraints) : constraints =
  map (fun (t1, t2) -> (apply_subst s t1, apply_subst s t2)) c

let rec fv (t : typ) =
  match t with
  | Tvar x -> [x]
  | Tarrow (t1, t2) -> fv t1 @ fv t2
  | Ttuple (t1, t2) -> fv t1 @ fv t2
  | Tsum (t1, t2) -> fv t1 @ fv t2
  | _ -> []
  
let rec unify (c : constraints) : substitution option =
  match c with
  | [] -> Some empty_subst
  | (s, t) :: rest ->
     if s = t then unify rest else
       match s, t with
       | Tvar x, _ -> if exists (fun y -> y = x) (fv t) then None else
                        let s1 = single_subst x t in
                        (match unify (apply_subst_c s1 rest) with
                         | Some s' -> Some (compose_subst s' s1)
                         | None -> None)
       | _, Tvar x -> if exists (fun y -> y = x) (fv s) then None else
                        let s1 = single_subst x s in
                        (match unify (apply_subst_c s1 rest) with
                         | Some s' -> Some (compose_subst s' s1)
                         | None -> None)
       | Tarrow (s1, s2), Tarrow (t1, t2) -> unify ((s1, t1) :: (s2, t2) :: rest)
       | Ttuple (s1, s2), Ttuple (t1, t2) -> unify ((s1, t1) :: (s2, t2) :: rest)
       | Tsum (s1, s2), Tsum (t1, t2) -> unify ((s1, t1) :: (s2, t2) :: rest)
       | _, _ -> None

let infer_type (e : exp) =
  match get_constraints empty_context e with
  | Some (t, c) ->
     (match unify c with
      | Some s -> Some (apply_subst s t)
      | None -> None)
  | None -> None
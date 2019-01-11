open List

(* syntax *)
type ident = string

type typ = Tint | Tclass of ident
type exp = Int of int | Add of exp * exp | Mul of exp * exp | Var of ident
         | GetField of exp * ident

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
           | New of ident * ident * exp list | SetField of exp * ident * exp
           | Invoke of ident * exp * ident * exp list | Return of exp
           | IfC of exp * cmd * cmd


type mdecl = MDecl of typ * ident * (typ * ident) list * cmd

type cdecl = Class of ident * ident * (typ * ident) list * mdecl list

(* values and states *)
type class_table = ident -> cdecl option
                 
type ref = int
type value = IntV of int | RefV of ref
type obj = Obj of ident * value list

type env = ident -> value option
type store = (ref -> obj option) * ref
let empty_state = fun x -> None
let update s x v = fun y -> if y = x then Some v else s y

let empty_store : store = (empty_state, 0)
let store_lookup (s : store) = fst s
let next_ref (s : store) = snd s
let update_store (s : store) (r : ref) (o : obj) : store =
  (update (store_lookup s) r o, next_ref s)

(* field and method lookup *)
let rec fields (ct : class_table) (c : ident) : (typ * ident) list =
  if c = "Object" then [] else
    match ct c with
    | Some (Class (_, d, lf, _)) -> fields ct d @ lf
    | _ -> []

let rec field_index_aux (l : (typ * ident) list) (f : ident) (n : int) =
  match l with
  | [] -> None
  | (_, g) :: rest ->
     if f = g then Some n else field_index_aux rest f (n - 1)

let field_index ct c f =
  field_index_aux (rev (fields ct c)) f (length (fields ct c) - 1)

let rec methods (ct : class_table) (c : ident) : mdecl list =
  if c = "Object" then [] else
    match ct c with
    | Some (Class (_, d, _, lm)) -> methods ct d @ lm
    | _ -> []

let lookup_method_aux (l : mdecl list) (m : ident) : mdecl option =
  find_opt (fun d -> match d with MDecl (_, n, _, _) -> n = m) l

let lookup_method ct c m =
  lookup_method_aux (rev (methods ct c)) m
  
let replace l pos a  = mapi (fun i x -> if i = pos then a else x) l

                     
(* evaluating expressions (based on big-step rules) *)
let rec eval_exp (ct : class_table) (e : exp) (r : env) (s : store)
        : value option =
  match e with
  | Var x -> r x
  | Int i -> Some (IntV i)
  | Add (e1, e2) ->
     (match eval_exp ct e1 r s, eval_exp ct e2 r s with
      | Some (IntV i1), Some (IntV i2) -> Some (IntV (i1 + i2))
      | _, _ -> None)
  | Mul (e1, e2) ->
     (match eval_exp ct e1 r s, eval_exp ct e2 r s with
      | Some (IntV i1), Some (IntV i2) -> Some (IntV (i1 * i2))
      | _, _ -> None)

  | GetField (e, f) ->
     (match eval_exp ct e r s with
      | Some (RefV p) ->
         (match store_lookup s p with
          | Some (Obj (c, lv)) ->
             (match field_index ct c f with
              | Some i -> nth_opt lv i
              | None -> None)
          | _ -> None)
      | _ -> None)

let rec eval_exps (ct : class_table) (le : exp list) (r : env) (s : store)
        : value list option =
  match le with
  | [] -> Some []
  | e :: rest ->
     (match eval_exp ct e r s, eval_exps ct rest r s with
      | Some v, Some lv -> Some (v :: lv)
      | _, _ -> None)
    
let ct1 d = if d = "Shape" then
              Some (Class ("Shape", "Object", [(Tint, "id")],
                           [MDecl (Tint, "area", [],
                                   Return (Int 0))]))
            else if d = "Square" then
              Some (Class ("Square", "Shape", [(Tint, "side")],
                           [MDecl (Tint, "area", [],
                                   Seq (Assign ("x", GetField (Var "this", "side")),
                                        Return (Mul (Var "x", Var "x"))))]))
            else None

let rec create_env(li: ident list) (lv: value list) (st: env): env =
  match li, lv with 
    | (variable::rest), (var_value::restv) -> create_env rest restv (update st variable var_value)
    | ([]),([]) -> st
    | _,_ -> st

(* The actual make_env function which retruns an environment of identifiers to values mapped using create_env function*)
let make_env(li: ident list) (lv: value list): env =
  create_env li lv empty_state  
  
let rec make_new_env(li: (typ*ident) list) (lv: value list)(en:env):env =
  (match li, lv with
  | ((t,x)::restv),(val_v::restval) -> make_new_env restv restval (update en x val_v)
  | ([],[]) -> en
  | _,_ -> en)

(* evaluating commands (based on small-step rules) *)          
type stack = (env * ident) list          
type config = cmd * stack * env * store

let rec step_cmd (ct : class_table) (c : cmd) (k : stack) (r : env) (s : store)
        : config option =
  match c with
  | Assign (x, e) ->
     (match eval_exp ct e r s with
      | Some v -> Some (Skip, k, update r x v, s)
      | None -> None)
  | Seq (Skip, c2) -> Some (c2, k, r, s)
  | Seq (c1, c2) ->
     (match step_cmd ct c1 k r s with
      | Some (c1', k', r', s') -> Some (Seq (c1', c2), k', r', s')
      | None -> None)
  | Skip -> None


  | IfC (expr, c1, c2) -> 
    (match eval_exp ct expr r s with
      | Some (IntV i) -> if i = 0 then Some(c2,k,r,s) else Some(c1,k,r,s)
      | _ -> None)


  | Invoke (x,e,m,args) -> 
  (*Extracting C by first fetching p and then doing a store lookup to get c*)
  let c = (
    match eval_exp ct e r s with
    | Some (RefV p) -> (match (store_lookup s) p with
                        | Some(Obj(c,_)) -> c
                        | None -> "x"  )  
    | _ -> "x"
    ) in 
    (*Extracting vals by using eval_exps*)
    let vals = match eval_exps ct args r s with
      | Some vals -> vals
      | _ -> []
    in 
    (*Extracting body and params using lookup method and then pattern matching it with MDecl constructor*)
    let (params:(typ*ident) list), (body:cmd) = match lookup_method ct c m with
      | Some(MDecl (_,_,param_list,body)) -> param_list, body
    in
    (*Creating a new environment with params = vals*)
    let new_env = make_new_env params vals (empty_state) 
    in
    let p = match eval_exp ct e r s with
    | Some (IntV p) -> p
    | _ -> 0
    in
    (*Adding this = p binding to the created environment*)
    let f_env:env = update new_env "this" (RefV p)
    in
    (*Pushing current environment and the variable to be assigned x to the stack*)
    let new_stack:stack = [(r,x)]@k
    in
    (*Now we have all we need which is just returned here*)
    Some(body,new_stack,f_env,s)



    | Return (e) -> 
      (*Evaluating e to get v*)
      let v = match eval_exp ct e r s with
      | Some (IntV v) -> v
      | _ -> 0
      in
      (*Extracting the old stack by popping the top entry*)
      let (old_stack:stack),(old_ro:env),x = match k with
      | (ro,x)::k_old -> k_old,ro,x
      | (ro,x)::[] -> [],ro,x
      
      in
      (*Updating the old environment with a binding from variable being assigned with return value of the function *)
      let updated_env = update old_ro x (IntV v)
      in
      (*We have everything now and we just return*)
      Some(Skip,old_stack,updated_env,s)


  | New (x, c, args) ->
     (match eval_exps ct args r s with
      | Some lv ->
         let p = next_ref s in
         Some (Skip, k, update r x (RefV p),
               (update (store_lookup s) p (Obj (c, lv)), p + 1))
      | None -> None)

  | SetField (e, f, e1) ->
     (match eval_exp ct e r s, eval_exp ct e1 r s with
      | Some (RefV p), Some v ->
         (match store_lookup s p with
          | Some (Obj (c, lv)) ->
             (match field_index ct c f with
              | Some i -> Some (Skip, k, r, update_store s p (Obj (c, replace lv i v)))
              | None -> None)
          | None -> None)
      | _, _ -> None)

  | _ -> None

let rec run_config (ct : class_table) (con : config) : config =
  let (c, k, r, s) = con in
  match step_cmd ct c k r s with
  | Some con' -> run_config ct con'
  | None -> con

let run_prog (ct : class_table) (c : cmd) =
  run_config ct (c, [], empty_state, empty_store)


(*Helper function to debug and step through each step in step_cmd*)
(* let get_config (con:config option) = 
  match con with
  | Some cc -> cc *)

(* test cases *)  
let test0 : cmd =
  Seq (New ("s", "Square", [Int 0; Int 2]),
       (* s = new Square(0, 2); *)
       SetField (Var "s", "side", Add (GetField (Var "s", "side"), Int 1)))
       (* s.side = s.side + 1; *)


let test1 : cmd =
  Seq (Assign ("x", Int 1),
       IfC (Var "x", Assign ("x", Int 2), Assign ("x", Int 3)))
  
let test2 : cmd =
  Seq (New ("s", "Shape", [Int 2]),
       (* s = new Shape(2); *)
       Invoke ("x", Var "s", "area", []))
       (* x = s.area(); *)

let test3 : cmd =
  Seq (New ("s", "Square", [Int 0; Int 2]),
       (* s = new Square(0, 2); *)
  Seq (SetField (Var "s", "side", Add (GetField (Var "s", "side"), Int 1)),
       (* s.side = s.side + 1; *)
       Invoke ("x", Var "s", "area", [])))
       (* x = s.area(); *)


       
       
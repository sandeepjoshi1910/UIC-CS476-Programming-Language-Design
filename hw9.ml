open List

(* syntax *)
type ident = string

type typ = Tint | Ttid

type exp = Int of int | Add of exp * exp | Var of ident | Global of ident
                                                                  
type cmd = Assign of ident * exp
           | Call of ident * ident * exp list | Return of exp
           | SetGlobal of ident * exp
           | Fork of ident * ident | Join of exp

type fdecl = FDecl of typ * ident * (typ * ident) list * cmd list


(* values and states *)
type tid = int

type value = IntV of int | TidV of tid

type env = ident -> value option
let empty_state = fun x -> None
let update s x v = fun y -> if y = x then Some v else s y

let next_tid = ref 0
let fresh_tid (u : unit) = next_tid := !next_tid + 1; !next_tid

(* evaluating expressions (based on big-step rules) *)
let rec eval_exp (e : exp) (r : env) (g : env) : value option =
  match e with
  | Var x -> r x
  | Global x -> g x
  | Int i -> Some (IntV i)
  | Add (e1, e2) ->
     (match eval_exp e1 r g, eval_exp e2 r g with
      | Some (IntV i1), Some (IntV i2) -> Some (IntV (i1 + i2))
      | _, _ -> None)

let rec eval_exps (le : exp list) (r : env) (g : env)
        : value list option =
  match le with
  | [] -> Some []
  | e :: rest ->
     (match eval_exp e r g, eval_exps rest r g with
      | Some v, Some lv -> Some (v :: lv)
      | _, _ -> None)
    
(* evaluating commands (based on small-step rules) *)          
type stack = (env * ident) list          
type config1 = cmd list * stack * env * env

type fundecls = ident -> fdecl option
             
let rec make_env (li : ident list) (lv : value list) : env =
  match li, lv with
  | i :: irest, v :: vrest -> update (make_env irest vrest) i v
  | _, _ -> empty_state
           
let rec step_cmd1 (funs : fundecls) (lc : cmd list) (k : stack) (r : env) (g : env)
        : config1 option =
  match lc with
  | [] -> None
  | c :: rest ->
     (match c with
      | Assign (x, e) ->
         (match eval_exp e r g with
          | Some v -> Some (rest, k, update r x v, g)
          | None -> None)
      | SetGlobal (x, e) ->
         (match eval_exp e r g with
          | Some v -> Some (rest, k, r, update g x v)
          | None -> None)
      | Call (x, f, args) ->
         (match eval_exps args r g with
          | Some vals ->
             (match funs f with
              | Some (FDecl (_, _, params, body)) ->
                 Some (body @ rest, (r, x) :: k, make_env (map snd params) (vals), g)
              | None -> None)
          | _ -> None)
      | Return e ->
         (match eval_exp e r g, k with
          | Some v, (r0, x) :: k0 ->
             Some (rest, k0, update r0 x v, g)
          | _, _ -> None)
      | _ -> None)

type thread = tid * cmd list * stack * env
type config = thread list * env

let terminated (i : tid) (t : thread) : bool =
  (match t with
    | (tid, lc, k, r) -> (match lc with
                        | Return _ :: _ -> if (tid = i && k = []) then true else false 
                        | _ -> false)
    )
  

let rec thread_exists (threads: thread list) (t: tid) : bool =
  (match threads with
    | (tid,lc,k,r) :: rest -> if (terminated t (tid,lc,k,r)) then true else thread_exists rest t
    | [] -> false)


let step_cmd (funs : fundecls) (threads : thread list)
      (i : tid) (lc : cmd list) (k : stack) (r : env) (g : env) : config =
  let fail_config = (threads @ [(i, lc, k, r)], g) in
  match lc with
  | Fork (x, f) :: rest -> (match funs f with
                            | Some FDecl(_,_,_,c) -> let new_tid = fresh_tid() in
                                                  (threads @ [(i,rest,k,update r x (IntV new_tid));(new_tid,c,[],empty_state)],g) 
                            | _ -> fail_config  )
  | Join e :: rest -> (match eval_exp e r g with
                      |Some (IntV v) -> if  (thread_exists threads v) then ([i,rest,k,r] @ threads,g) else fail_config
                      | _ -> fail_config)
  | _ -> (match step_cmd1 funs lc k r g with
          | Some (lc1 ,k1 , r1 , g1) -> (threads @ [(i, lc1, k1, r1)], g1)
          | _ -> fail_config)


(* for testing *)       
let step_config (funs : fundecls) (con : config) : config =
  let (threads, g) = con in
  match threads with
  | (i, c, k, r) :: rest -> step_cmd funs rest i c k r g
  | _ -> con
    
let rec run_config (funs : fundecls) (con : config) : config =
  match find_opt (fun (i, c, k, _) -> i = 0 && c = [] && k = []) (fst con) with
  | Some _ -> con
  | None ->
     run_config funs (step_config funs con)

let run_prog (funs : fundecls) (globals : env) (c : cmd list) =
  run_config funs ([(0, c, [], empty_state)], globals)

let rec run_config_n (n : int) (funs : fundecls) (con : config) : config =
  if n <= 0 then con else
  match find_opt (fun (i, c, k, _) -> i = 0 && c = [] && k = []) (fst con) with
  | Some _ -> con
  | None ->
     run_config_n (n - 1) funs (step_config funs con)

let run_prog_n (n : int) (funs : fundecls) (globals : env) (c : cmd list) =
  run_config_n n funs ([(0, c, [], empty_state)], globals)


(* test cases *)  
let funs0 : fundecls = fun y ->
  if y = "thread_fun" then Some (FDecl (Tint, "thread_fun", [],
                                        [SetGlobal ("x", Add (Global "x", Int 1));
                                         Return (Int 0)]))
  else None
                                        
let globals0 : env = fun y -> if y = "x" then Some (IntV 0) else None

let test_seq : cmd list =
  [SetGlobal ("x", Int 1);
   (* x = 1; *)
   SetGlobal ("y", Int 2)]
   (* y = 2; *)

let test_con : cmd list =
  [Fork ("t", "thread_fun");
   (* t = fork(thread_fun); *)
   SetGlobal ("x", Add (Global "x", Int 1));
   (* x = x + 1; *)
   Join (Var "t")]
    (* join(t); *)

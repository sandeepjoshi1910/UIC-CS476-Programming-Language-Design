type ident = string

type exp = Int of int | Add of exp * exp | Sub of exp * exp | Div of exp * exp
         | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp

type cmd = Assign of ident * exp | Seq of cmd * cmd | Skip
           | IfC of exp * cmd * cmd | While of exp * cmd | Throw | Try of cmd * cmd

type value = IntV of int | BoolV of bool
type exp_res = Val of value | Exc

type state = ident -> value option
let empty_state = fun x -> None
let update s x v = fun y -> if y = x then Some v else None
           
let rec eval_exp (e : exp) (s : state) : exp_res option =
  match e with
  | Int i -> Some (Val (IntV i))
  | Add (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val (IntV i1)), Some (Val (IntV i2)) -> Some (Val (IntV (i1 + i2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | Sub (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val (IntV i1)), Some (Val (IntV i2)) -> Some (Val (IntV (i1 - i2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | Div (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val (IntV i1)), Some (Val (IntV i2)) ->
                        if i2 = 0 then Some Exc else Some (Val (IntV (i1 / i2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | Bool b -> Some (Val (BoolV b))
  | And (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 && b2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | Or (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val (BoolV b1)), Some (Val (BoolV b2)) -> Some (Val (BoolV (b1 || b2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | Eq (e1, e2) -> (match eval_exp e1 s, eval_exp e2 s with
                     | Some (Val v1), Some (Val v2) -> Some (Val (BoolV (v1 = v2)))
                     | Some Exc, _ | Some _, Some Exc -> Some Exc
                     | _, _ -> None)
  | If (e, e1, e2) -> (match eval_exp e s with
                       | Some (Val (BoolV true)) -> eval_exp e1 s
                       | Some (Val (BoolV false)) -> eval_exp e2 s
                       | Some Exc -> Some Exc
                       | _ -> None)

let rec step_cmd (c : cmd) (s : state) : (cmd * state) option =
  match c with
  | Assign (x, e) -> (match eval_exp e s with
                      | Some (Val v) -> Some (Skip, update s x v)
                      | Some Exc -> Some( Throw, s)
                      | None -> None)
  
  | Seq(Throw,c2) -> Some(Throw,s)
  | Seq (Skip, c2) -> Some (c2, s)
  | Seq (c1, c2) -> (match step_cmd c1 s with
                     | Some (Throw, s) -> Some(Seq(Throw,c2),s)
                     | Some (c1', s') -> Some (Seq (c1', c2), s')
                     | None -> None)
  
  | Skip -> None
  | IfC (e, c1, c2) -> (match eval_exp e s with
                        | Some (Val (BoolV true)) -> Some (c1, s)
                        | Some (Val (BoolV false)) -> Some (c2, s)
                        | Some Exc -> Some (Throw,s)
                        | _ -> None)
  | While (e, c) -> Some (IfC (e, Seq (c, While (e, c)), Skip), s)

  | Throw -> Some (Throw, s)
  
  | Try (c1, c2) -> (match step_cmd c1 s with
      |Some (Throw, s) -> Some(c2,s) 
      |Some(c1',s') -> Some(Try(c1',c2),s')
      |None -> Some(Skip, s) );;
  

(* step_cmd (Seq (Assign ("x", Div (Int 1, Int 0)), Skip)) empty_state;;
step_cmd (Try (Throw, Assign ("x", Int 2))) empty_state;;

step_cmd (Assign("y",Div(Int 1, Int 0))) empty_state;;
step_cmd (Seq(Assign("y",Div(Int 1, Int 0)),Assign("y",Int 6))) empty_state;;

step_cmd (Seq(Throw,Try(Assign("y",Int 7),Skip))) empty_state;;

step_cmd (IfC(Div (Int 1, Int 0),Assign("y",Bool true),Skip)) empty_state;;

step_cmd (Try(Assign("x",Int 10),Seq(Assign("x",Bool false),Assign("y", Int 10)))) empty_state;;

step_cmd (Try(Skip,Seq(Assign("x",Bool false),Assign("y", Int 10)))) empty_state;;

step_cmd (Try(Throw,Seq(Assign("x",Bool false),Assign("y", Int 10)))) empty_state;; *)




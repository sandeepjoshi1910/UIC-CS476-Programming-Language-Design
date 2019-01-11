
(* CS 476 Programming Language Design : Fall 2018 : HW2 – Syntax and Type Checking *)

(* 1. Write datatypes ast A and ast D of abstract syntax trees for A and D *)
type ast_A =  Cons of string | On of ast_A * ast_A | Func of string * ast_A
type ast_D = Decl of string * ast_A | RecDecl of string * ast_A;;

(* 2. Define a value tree1 : ast D that is an AST for the term let y = fun f -> (fun x -> f on x) on f *)
let tree1 : ast_D = Decl("y", Func ("f", On ( Func ("x", On (Cons "f", Cons "x")), Cons "f")));;

(* Write a function count funs : ast D -> int that counts the number of fun nodes in an AST for D *)
let rec count_funs_A(ast:ast_A):int =
  match ast with
  | Cons x -> 0
  | On (x,y) -> count_funs_A(x) + count_funs_A(y)
  | Func (x,y) -> 1 + count_funs_A(y)

let count_funs (d : ast_D) : int =
  match d with
  | Decl(x,y) -> count_funs_A(y)
  | _-> 0

(* Write a function count id : string -> ast D -> int that takes a string s and an AST for D and counts the number of times s appears as an identifier in the AST *)
let rec count_str (str:string)  (ast:ast_A) =
  match ast with
  | Cons x -> if x = str then 1 else 0
  | On (x,y) -> count_str str x + count_str str y
  | Func (x,y) -> if x = str then 1 + count_str str y else count_str str y

let count_id (s : string) (d : ast_D) =
  match d with
  | Decl(x, y) -> count_str s y
  | _ -> 0


(* 3. Write a function typecheck : exp -> typ -> bool that returns true if the given expression has the given type, and false otherwise.*)
type exp = Int of int | Add of exp * exp | Sub of exp * exp
         | Bool of bool | And of exp * exp | Or of exp * exp
         | Eq of exp * exp | If of exp * exp * exp

type typ = Tint | Tbool

type value = IntV of int | BoolV of bool


let rec typeexp (e:exp): value option =
  match e with
  | Int i -> Some(IntV i)
  | Bool x -> Some(BoolV x)
  | Add (x,y) | Sub (x,y) -> 
        (match typeexp x, typeexp y with
        | Some(IntV i1), Some(IntV i2) -> Some(BoolV true)
        | _,_ -> Some(BoolV false))
  
  | And (x,y) | Or (x,y) ->
      (match typeexp x, typeexp y with
        | Some(BoolV i1), Some(BoolV i2) -> Some(BoolV true)
        | _,_ -> Some(BoolV false))
  
  | Eq (x,y) ->
        (match typeexp x, typeexp y with
        | Some(BoolV i1), Some(BoolV i2) -> Some(BoolV true)
        | Some(IntV i1), Some(IntV i2) -> Some(BoolV true)
        | _,_ -> Some(BoolV false))

  | If (x,y,z) -> 
        (match typeexp x, typeexp y, typeexp z with
        | Some(BoolV i1), Some(BoolV i2), Some(BoolV i3) -> Some(BoolV true)
        | Some(BoolV i1), Some(IntV i2), Some(IntV i3) -> Some(IntV 0) 
        | _,_,_ -> Some(BoolV false))

  
  let rec typecheck (e : exp) (t : typ): bool =
    match e with
    | Add (x,y) | Sub (x,y) -> (match (typeexp e) with
                    | Some(BoolV b) -> if t = Tint then if b = true then true else false else false
                    | _ -> false)
  
    | And (x,y) | Or (x,y) | Eq (x,y) -> (match (typeexp e) with
                    | Some(BoolV b) -> if t = Tbool then if b = true then true else false else false
                    | _ -> false)
  
    | If (x,y,z) -> (match (typeexp e) with 
                    | Some(BoolV b) -> if t = Tbool then if b = true then true else false else false
                    | Some(IntV i) -> if t = Tint then true else false
                    | _ -> false )
    | Int x  -> if t = Tint then true else false
    | Bool b -> if t = Tbool then true else false;;


    (* Test Cases *)
    (* typecheck (Add (Int 3, Bool true)) Tint = false;;

    typecheck (Add (Int 3, Int 4)) Tbool = false;;
    
    typecheck (If (Bool false, Bool true, Bool true)) Tbool = true;;
    
    typecheck (And (Bool true, Bool false)) Tbool = true;;
    
    typecheck (And (Bool true, Bool false)) Tint = false;;
    
    typecheck (Eq (Bool true, Bool false)) Tbool = true;;
    
    typecheck (Eq (Int 3, Int 4)) Tbool = true;;
    
    typecheck (Eq (Int 3, Int 4)) Tint = false;; *)
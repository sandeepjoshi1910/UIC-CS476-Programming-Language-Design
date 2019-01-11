(*CS 476: Programming Language Design - HW 1*)
type intlist = Nil | Cons of int * intlist;;
(* Write a function is nil : intlist -> bool that is true for Nil and false for
any non-Nil list. For instance, is nil Nil should be true, and is nil (Cons
(1, Nil)) should be false.*)
let is_nil(lt:intlist):bool =
  match lt with
  | Nil -> true
  | Cons(_,_) -> false
(* Write a function sum : intlist -> int that returns the sum of all the
elements of an intlist. For instance, is nil Nil should be 0, and is nil (Cons
(2, Cons (3, Nil))) should be 5.*)
let rec sum(lt:intlist):int =
  match lt with
    | Nil -> 0
    | Cons(x, y) -> x + sum(y)
(*Define a type int or list that has two constructors: Int, which
takes an int, and List, which takes an intlist. Write a function is pos :
int or list -> bool that is true for any positive int and any list whose sum (as
defined in problem 2) is positive, and false otherwise. (A number is positive if it
is greater than 0.) For instance, is pos (Int 0) and is pos (List Nil) should
be false, and is pos (Int 3) and is pos (List (Cons (1, Nil))) should be
true.*)
type int_or_list = Int of int | List of intlist
let is_pos(x:int_or_list):bool =
  match x with
  | Int x -> if x > 0 then true else false
  | List(x) -> if sum(x) > 0 then true else false
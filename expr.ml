(*
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions
 *)

type unop =
  | Negate
;;

type binop =
  | Plus
  | Minus
  | Times
  | Equals
  | LessThan
  | Fplus
  | Fminus
  | Ftimes
;;

type varid = string ;;

type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* decimals *)
  | Char of char                         (* characters *)
  | Str of string                        (* strings *)
  | Unit                                 (* unit *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;

(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;

(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var v -> SS.add v SS.empty
  | Unop (_u, ex) -> free_vars ex
  | Binop (_b, ex1, ex2) -> SS.union (free_vars ex1) (free_vars ex2)
  | Conditional (ex1, ex2, ex3) ->
      SS.union (free_vars ex3) (SS.union (free_vars ex1) (free_vars ex2))
  | Fun (v, ex) -> SS.remove v (free_vars ex)
  | Let (v, ex1, ex2) ->
      SS.union (SS.remove v (free_vars ex2)) (free_vars ex1)
  | Letrec (v, ex1, ex2) ->
      SS.union (SS.remove v (free_vars ex2)) (SS.remove v (free_vars ex1))
  | App (ex1, ex2) -> SS.union (free_vars ex1) (free_vars ex2)
  | Raise
  | Unassigned
  | Num _
  | Float _
  | Str _
  | Char _
  | Unit
  | Bool _ -> SS.empty

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)
let new_varname : unit -> varid =
    let ctr = ref 0 in
    fun () ->
      let v = "var" ^ string_of_int !ctr in
      ctr := !ctr + 1;
      v ;;

(*......................................................................
  Substitution

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  (* replace varids? *)
  match exp with
  | Var v -> if v = var_name then repl else exp
  | Unop (u, ex) -> Unop(u, subst var_name repl ex)
  | Binop (b, ex1, ex2) ->
      Binop(b, subst var_name repl ex1, subst var_name repl ex2)
  | Conditional (ex1, ex2, ex3) ->
      Conditional(subst var_name repl ex1,
                  subst var_name repl ex2,
                  subst var_name repl ex3)
  | Fun (v, ex) ->
      if v = var_name then exp
      else if SS.mem v (free_vars repl) then
        let fresh = new_varname () in
        Fun(fresh, subst var_name repl (subst v (Var fresh) ex))
      else Fun(v, subst var_name repl ex)
  | Let (v, ex1, ex2) ->
      if v = var_name then Let(v, subst var_name repl ex1, ex2)
      else if SS.mem v (free_vars repl) then
        let fresh = new_varname () in
        Let(fresh, subst var_name repl ex1,
            subst var_name repl (subst v (Var fresh) ex2))
      else Let(v, subst var_name repl ex1, subst var_name repl ex2)
  | Letrec (v, ex1, ex2) ->
      if v = var_name then Letrec(v, subst var_name repl ex1, ex2)
      else if SS.mem v (free_vars repl) then
        let fresh = new_varname () in
        Letrec(fresh,
               subst var_name repl ex1,
               subst var_name repl (subst v (Var fresh) ex2))
      else Letrec(v, subst var_name repl ex1, subst var_name repl ex2)
  | App (ex1, ex2) -> App(subst var_name repl ex1, subst var_name repl ex2)
  | Raise
  | Unassigned
  | Num _
  | Float _
  | Str _
  | Char _
  | Unit
  | Bool _ -> exp

(*......................................................................
  String representations of expressions
 *)
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Num i -> string_of_int i
  | Float f -> string_of_float f
  | Str s -> "\"" ^ s ^ "\""
  | Char c -> "'" ^ Char.escaped c ^ "'"
  | Unit -> "()"
  | Bool b -> string_of_bool b
  | Unop (_unop, ex) -> "Negate(" ^ exp_to_concrete_string ex ^ ")"
  | Binop (bin, ex1, ex2) ->
      exp_to_concrete_string ex1 ^
      (match bin with
       | Plus ->  " + "
       | Minus -> " - "
       | Times -> " * "
       | Fplus -> " +. "
       | Fminus -> " -. "
       | Ftimes -> " *. "
       | Equals -> " = "
       | LessThan -> " < ")
      ^ exp_to_concrete_string ex2
  | Conditional (ex1, ex2, ex3) ->
      "if " ^ exp_to_concrete_string ex1 ^
      " then " ^ exp_to_concrete_string ex2 ^
      " else " ^ exp_to_concrete_string ex3
  | Fun (v, ex) -> "fun " ^ v ^ " -> " ^ exp_to_concrete_string ex
  | Let (v, ex1, ex2) ->
      "let " ^ v ^ " = " ^ exp_to_concrete_string ex1 ^
      " in " ^ exp_to_concrete_string ex2
  | Letrec (v, ex1, ex2) ->
      "let rec " ^ v ^ " = " ^ exp_to_concrete_string ex1 ^
      " in " ^ exp_to_concrete_string ex2
  | Raise -> "Exception raised"
  | Unassigned -> "Unassigned"
  | App (f, a) -> exp_to_concrete_string f ^ " " ^ exp_to_concrete_string a ;;

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var(" ^ v ^ ")"
  | Num i -> "Num(" ^ string_of_int i ^ ")"
  | Float f -> "Float(" ^ string_of_float f ^ ")"
  | Str s -> "Str(" ^ s ^ ")"
  | Char c -> "Char(" ^ Char.escaped c ^ ")"
  | Unit -> "Unit"
  | Bool b -> "Bool(" ^ string_of_bool b ^ ")"
  | Unop (_unop, ex) -> "Unop(Negate, " ^ exp_to_abstract_string ex ^ ")"
  | Binop (bin, ex1, ex2) ->
      "Binop(" ^
      (match bin with
       | Plus -> "Plus, "
       | Minus -> "Minus, "
       | Times -> "Times, "
       | Fplus -> "Fplus, "
       | Fminus -> "Fminus, "
       | Ftimes -> "Ftimes, "
       | Equals -> "Equals, "
       | LessThan -> "LessThan, ")
      ^ exp_to_abstract_string ex1 ^ ", " ^ exp_to_abstract_string ex2 ^ ")"
  | Conditional (ex1, ex2, ex3) ->
      "Conditional(" ^
      exp_to_abstract_string ex1 ^ ", " ^
      exp_to_abstract_string ex2 ^ ", " ^
      exp_to_abstract_string ex3 ^ ")"
  | Fun (v, ex) -> "Fun(" ^ v ^ ", " ^ exp_to_abstract_string ex ^ ")"
  | Let (v, ex1, ex2) ->
      "Let(" ^ v ^ ", " ^ exp_to_abstract_string ex1 ^ ", " ^
      exp_to_abstract_string ex2 ^ ")"
  | Letrec (v, ex1, ex2) ->
      "Letrec(" ^ v ^ ", " ^ exp_to_abstract_string ex1 ^ ", " ^
      exp_to_abstract_string ex2 ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (f, a) ->
      "App(" ^ exp_to_abstract_string f ^ ", " ^ exp_to_abstract_string a ^ ")"

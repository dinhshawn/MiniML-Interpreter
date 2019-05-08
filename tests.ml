open Expr ;;
open Evaluation ;;
open Miniml ;;
(*| Var of varid                         (* variables *)
| Num of int                           (* integers *)
| Bool of bool                         (* booleans *)
| Unop of unop * expr                  (* unary operators *)
| Binop of binop * expr * expr         (* binary operators *)
| Conditional of expr * expr * expr    (* if then else *)
| Fun of varid * expr                  (* function definitions *)
| Let of varid * expr * expr           (* local naming *)
| Letrec of varid * expr * expr        (* recursive local naming *)
| Raise                                (* exceptions *)
| Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr *)

let exp2str () =
  let v1 = Var("x") in
  let v2 = Var("y") in
  let n1 = Num(3) in
  let n2 = Num(~-3) in
  let n3 = Num(4) in
  let n4 = Num(2) in
  let n5 = Num(7) in
  let b1 = Bool(true) in
  let fun1 = Fun("f",Binop(Plus,Var("f"),Num(9))) in
  let reclet = Letrec("f",Fun("x",Conditional(Binop(Equals,v1,Num(0)),Num(1),
                      Binop(Times,v1,App(Var("f"),Binop(Minus,v1,Num(1)))))),
                      App(Var("f"),n3)) in
  let free_reclet = Letrec("f",Fun("x",Conditional(Binop(Equals,v1,Num(0)),Num(1),
                           Binop(Times,v1,App(Var("f"),Binop(Minus,v1,Var("z")))))),
                           App(Var("f"),Var("a"))) in

  (* exp_to_abstract_string *)
  assert(exp_to_abstract_string v1 = "Var(x)");
  assert(exp_to_abstract_string n1 = "Num(3)");
  assert(exp_to_abstract_string n2 = "Num(-3)");
  assert(exp_to_abstract_string b1 = "Bool(true)");
  assert(exp_to_abstract_string (Unop(Negate,n1)) = "Unop(Negate, Num(3))");
  assert(exp_to_abstract_string (Binop(Plus,n1,n3)) =
         "Binop(Plus, Num(3), Num(4))");
  assert(exp_to_abstract_string (Binop(Plus,Binop(Times,n4,n4),Binop(Minus,n5,n3))) =
         "Binop(Plus, Binop(Times, Num(2), Num(2)), Binop(Minus, Num(7), Num(4)))");
  assert(exp_to_abstract_string (Conditional(b1,v1,v2)) =
         "Conditional(Bool(true), Var(x), Var(y))");
  assert(exp_to_abstract_string fun1 =
         "Fun(f, Binop(Plus, Var(f), Num(9)))");
  assert(exp_to_abstract_string (Let("x",n3,Binop(Times,v1,v1))) =
         "Let(x, Num(4), Binop(Times, Var(x), Var(x)))");
  assert(exp_to_abstract_string reclet =
         "Letrec(f, Fun(x, Conditional(Binop(Equals, Var(x), Num(0)), Num(1)," ^
         " Binop(Times, Var(x), App(Var(f), Binop(Minus, Var(x), Num(1))))))," ^
         " App(Var(f), Num(4)))");
  assert(exp_to_abstract_string Raise = "Raise");
  assert(exp_to_abstract_string Unassigned = "Unassigned");
  assert(exp_to_abstract_string (App(fun1,n3)) =
         "App(Fun(f, Binop(Plus, Var(f), Num(9))), Num(4))");

  (* exp_to_concrete_string *)
  assert(exp_to_concrete_string v1 = "x");
  assert(exp_to_concrete_string n1 = "3");
  assert(exp_to_concrete_string n2 = "-3");
  assert(exp_to_concrete_string b1 = "true");
  assert(exp_to_concrete_string (Unop(Negate,n1)) = "Negate(3)");
  assert(exp_to_concrete_string (Binop(Plus,n1,n3)) = "3 + 4");
  assert(exp_to_concrete_string (Binop(Plus,Binop(Times,n4,n4),Binop(Minus,n5,n3))) =
         "2 * 2 + 7 - 4");
  assert(exp_to_concrete_string (Conditional(b1,v1,v2)) = "if true then x else y");
  assert(exp_to_concrete_string (fun1) = "fun f -> f + 9");
  assert(exp_to_concrete_string (Let("x",n3,Binop(Times,v1,v1))) =
         "let x = 4 in x * x");
  assert(exp_to_concrete_string reclet =
         "let rec f = fun x -> if x = 0 then 1 else x * f x - 1 in f 4");
  assert(exp_to_concrete_string Raise = "Exception raised");
  assert(exp_to_concrete_string Unassigned = "Unassigned");
  assert(exp_to_concrete_string (App(fun1,n3)) = "fun f -> f + 9 4");

  (* free_vars *)
  assert(same_vars (free_vars v1) (vars_of_list ["x"]));
  assert(same_vars (free_vars n1) (vars_of_list []));
  assert(same_vars (free_vars (Fun("f", Binop(Plus, Var("x"), Var("f")))))
                   (vars_of_list ["x"]));
  assert(same_vars (free_vars (Binop(Plus, v1, v2))) (vars_of_list ["x";"y"]));
  assert(same_vars (free_vars (App(fun1,v2))) (vars_of_list ["y"]));
  assert(same_vars (free_vars (Let("x",v2,Binop(Times,v1,Var("z")))))
                   (vars_of_list ["y";"z"]));
  assert(same_vars (free_vars free_reclet) (vars_of_list ["z";"a"]));

  (* subst *)
  assert((subst "x" b1 v1) = b1);
  assert((subst "x" n1 (Binop(Plus, v1, v2))) = Binop(Plus, n1, v2));
  assert((subst "x" n1 (Binop(Plus, v1, v1))) = Binop(Plus, n1, n1));
  assert((subst "y" b1 (App(Fun("x",Conditional(Var("x"),n1,n2)),v2))) =
          App(Fun("x",Conditional(Var("x"),n1,n2)),b1));
  assert((subst "y" (Bool(false)) (App(Fun("x",Conditional(Var("x"),b1,v2)),v2))) =
          App(Fun("x",Conditional(Var("x"),b1,(Bool(false)))),Bool(false)));
  assert((subst "x" b1 v2) = v2);
  assert((subst "x" b1 v1) = b1);
  assert((subst "x" b1 v1) = b1);;

let evaluations () =
  (* substitution evaluation *)
  let test_sub (str : string) : string =
    Env.value_to_string (eval_s (str_to_exp (str ^ ";;")) (Env.create ())) in
  assert((test_sub "3") = "3");
  assert((test_sub "true") = "true");
  assert((test_sub "3 - 3") = "0");
  assert((test_sub "3 * ~-3") = "-9");
  assert((test_sub "3 + 3") = "6");
  assert((test_sub "3 = ~-3") = "false");
  assert((test_sub "3 = 3") = "true");
  assert((test_sub "true = true") = "true");
  assert((test_sub "true = false") = "false");
  assert((test_sub "3 < ~-3") = "false");
  assert((test_sub "~-3 < 3") = "true");
  assert((test_sub "true < true") = "false");
  assert((test_sub "true < false") = "false");
  assert((test_sub "if true then 3 else 2") = "3");
  assert((test_sub "if false then 3 else 2") = "2");
  assert((test_sub "fun f -> f + 9") = "fun f -> f + 9");
  assert((test_sub "let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4") =
         "24");

  (* dynamical evaluation *)
  let test_dyn (str : string) : string =
    Env.value_to_string (eval_d (str_to_exp (str ^ ";;")) (Env.create ())) in
  assert((test_dyn "3") = "3");
  assert((test_dyn "true") = "true");
  assert((test_dyn "3 - 3") = "0");
  assert((test_dyn "3 * ~-3") = "-9");
  assert((test_dyn "3 + 3") = "6");
  assert((test_dyn "3 = ~-3") = "false");
  assert((test_dyn "3 = 3") = "true");
  assert((test_dyn "true = true") = "true");
  assert((test_dyn "true = false") = "false");
  assert((test_dyn "3 < ~-3") = "false");
  assert((test_dyn "~-3 < 3") = "true");
  assert((test_dyn "true < true") = "false");
  assert((test_dyn "true < false") = "false");
  assert((test_dyn "if true then 3 else 2") = "3");
  assert((test_dyn "if false then 3 else 2") = "2");
  assert((test_dyn "fun f -> f + 9") = "fun f -> f + 9");
  assert((test_dyn "let x = 0 in let f = fun y -> x + y in let x = 10 in f 5") =
         "15");
  assert((test_dyn "let x = 0 in let f = fun y -> x + y in let x = 10 in f x") =
         "20");
  assert((test_dyn "let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 9") =
         "362880");

  ;;
let _ =
  exp2str ();
  evaluations ();
  () ;;

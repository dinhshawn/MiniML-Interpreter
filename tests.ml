open Expr ;;
open Evaluation ;;
open Miniml ;;

let exp () =
  let v1 = Var("x") in
  let v2 = Var("y") in
  let n1 = Num(3) in
  let n2 = Num(~-3) in
  let n3 = Num(4) in
  let n4 = Num(2) in
  let n5 = Num(7) in
  let b1 = Bool(true) in
  let fun1 = Fun("f",Binop(Plus,Var("f"),Num(9))) in
  let reclet =
    Letrec("f",Fun("x",Conditional(Binop(Equals,v1,Num(0)),Num(1),
           Binop(Times,v1,App(Var("f"),Binop(Minus,v1,Num(1)))))),
           App(Var("f"),n3)) in
  let free_reclet =
    Letrec("f",Fun("x",Conditional(Binop(Equals,v1,Num(0)),Num(1),
           Binop(Times,v1,App(Var("f"),Binop(Minus,v1,Var("z")))))),
           App(Var("f"),Var("a"))) in

  (* exp_to_abstract_string function *)
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

  (* exp_to_concrete_string function *)
  assert(exp_to_concrete_string v1 = "x");
  assert(exp_to_concrete_string n1 = "3");
  assert(exp_to_concrete_string n2 = "-3");
  assert(exp_to_concrete_string b1 = "true");
  assert(exp_to_concrete_string (Unop(Negate,n1)) = "~-(3)");
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

  (* free_vars function *)
  assert(same_vars (free_vars v1) (vars_of_list ["x"]));
  assert(same_vars (free_vars n1) (vars_of_list []));
  assert(same_vars (free_vars (Fun("f", Binop(Plus, Var("x"), Var("f")))))
                   (vars_of_list ["x"]));
  assert(same_vars (free_vars (Binop(Plus, v1, v2))) (vars_of_list ["x";"y"]));
  assert(same_vars (free_vars (App(fun1,v2))) (vars_of_list ["y"]));
  assert(same_vars (free_vars (Let("x",v2,Binop(Times,v1,Var("z")))))
                   (vars_of_list ["y";"z"]));
  assert(same_vars (free_vars free_reclet) (vars_of_list ["z";"a"]));

  (* subst function *)
  assert((subst "x" b1 v1) = b1);
  assert((subst "x" n1 (Binop(Plus, v1, v2))) = Binop(Plus, n1, v2));
  assert((subst "x" n1 (Binop(Plus, v1, v1))) = Binop(Plus, n1, n1));
  assert((subst "y" b1 (App(Fun("x",Conditional(Var("x"),n1,n2)),v2))) =
          App(Fun("x",Conditional(Var("x"),n1,n2)),b1));
  assert((subst "y" (Bool(false)) (App(Fun("x",Conditional(Var("x"),b1,v2)),v2))) =
          App(Fun("x",Conditional(Var("x"),b1,(Bool(false)))),Bool(false)));
  assert((subst "x" b1 v2) = v2) ;;

let evaluations () =
  (* Environment functions tests *)
  let make_loc (s : string) =
    (ref (Env.Val (str_to_exp (s ^ ";;")))) in
  let empt = Env.create () in
  let e1 = Env.extend empt "x" (make_loc "3") in
  assert (Env.lookup e1 "x" = !(make_loc "3"));
  assert (Env.value_to_string !(make_loc "3") = "3");
  assert (Env.value_to_string !(make_loc "false") = "false");
  assert (Env.value_to_string !(make_loc "if true then 1 else 2") =
         "if true then 1 else 2");
  assert(
    try
      Env.lookup e1 "y" = !(make_loc "3")
    with
    | EvalError _ -> true);
  let e2 = Env.extend (Env.extend e1 "x" (make_loc "23")) "y" (make_loc "19") in
  assert (Env.lookup e2 "x" = !(make_loc "23"));
  assert (Env.value_to_string !(make_loc "23") = "23");
  assert (Env.lookup e2 "y" = !(make_loc "19"));
  assert (Env.value_to_string !(make_loc "19") = "19");
  assert (Env.env_to_string e1 = "{x⊢3}");
  let c1 = Env.close (str_to_exp ("fun f -> f + 3" ^ ";;")) empt in
  assert (Env.value_to_string c1 = "fun f -> f + 3, [{}]");
  let c2 = Env.close (str_to_exp ("fun f -> f + 3" ^ ";;")) e1 in
  assert (Env.value_to_string c2 = "fun f -> f + 3, [{x⊢3}]");
  let c2 = Env.close (str_to_exp ("fun f -> f + 3" ^ ";;")) e2 in
  assert (Env.value_to_string c2 = "fun f -> f + 3, [{y⊢19, x⊢23, x⊢3}]");

  (* substitution evaluation *)
  let test_sub (str : string) : string =
    Env.value_to_string (eval_s (str_to_exp (str ^ ";;")) (Env.create ())) in
  let run_tests f =
    assert((f "3") = "3");
    assert((f "true") = "true");
    assert((f "3 - 3") = "0");
    assert((f "3 * ~-3") = "-9");
    assert((f "3 + 3") = "6");
    assert((f "3 = ~-3") = "false");
    assert((f "3 = 3") = "true");
    assert((f "3.5 +. 2.6") = "6.1");
    assert((f "3.5 -. 2.6") = "0.9");
    assert((f "3.5 *. 3.") = "10.5");
    assert((f "~=3.7") = "4");
    assert((f "~=3.3") = "3");
    assert((f "~=(~-2.3)") = "-2");
    assert((f "~=(~-2.5)") = "-3");
    assert((f "3.3 < 3.4") = "true");
    assert((f "~-3.3 < ~-3.4") = "false");
    assert((f "true = true") = "true");
    assert((f "true = false") = "false");
    assert((f "(4<8) && true") = "true");
    assert((f "true && (2<1)") = "false");
    assert((f "(3<2) || (4=7)") = "false");
    assert((f "(3=3) || false") = "true");
    assert((f "3 < ~-3") = "false");
    assert((f "~-3 < 3") = "true");
    assert((f "true < true") = "false");
    assert((f "true < false") = "false");
    assert((f "'a'") = "'a'");
    assert((f "'a' = 'a'") = "true");
    assert((f "'a' < 'b'") = "true");
    assert((f "'c' < 'b'") = "false");
    assert((f "\"abba\"") = "\"abba\"");
    assert((f "\"abba\" = \"abba\"") = "true");
    assert((f "\"abba\" = \"bbba\"") = "false");
    assert((f "\"abba\" < \"babaloo\"") = "true");
    assert((f "\"abba\" < \"abba\"") = "false");
    assert((f "\"abba\" + \"cddc\"") = "\"abbacddc\"");
    assert((f "()") = "()");
    assert((f "if true then 3 else 2") = "3");
    assert((f "if true then 3 else 2") = "3");
    assert((f "if false then raise else ()") = "()");
    assert((f "fun f -> f + 9") = "fun f -> f + 9");
    assert(
      try
        f "raise" = "raise"
      with
      | EvalError _ -> true)
  in
  run_tests test_sub;
  assert((test_sub "let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 4") =
         "24");
  assert((test_sub "let x = 1 in let f = fun y -> x + y in let x = 2 in f 3") =
         "4");

  (* dynamical evaluation *)
  let test_dyn (str : string) : string =
    Env.value_to_string (eval_d (str_to_exp (str ^ ";;")) (Env.create ())) in
  run_tests test_dyn;
  assert((test_dyn "let x = 0 in let f = fun y -> x + y in let x = 10 in f 5") =
         "15");
  assert((test_dyn "let x = 0 in let f = fun y -> x + y in let x = 10 in f x") =
         "20");
  assert((test_dyn "let rec f = fun x -> if x = 0 then 1 else x * f (x - 1) in f 9") =
         "362880");
  assert((test_dyn "let x = 1 in let f = fun y -> x + y in let x = 2 in f 3") =
         "5");;

let _ =
  exp ();
  evaluations ();
  () ;;

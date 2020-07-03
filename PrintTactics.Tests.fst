module PrintTactics.Tests

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul
open PrintTactics


(*** Tests *)
(**** Miscelleanous functions *)
let test_fun1 (n : nat) :
  Pure nat
  (requires (n >= 4))
  (ensures (fun n' -> n' >= 8)) =
  2 * n

let test_fun2 (n : nat) :
  ST.Stack nat
  (requires (fun h1 -> n >= 4))
  (ensures (fun h1 n' h2 -> n' >= 8)) =
  2 * n

let test_fun3 (n : nat) :
  ST.ST nat
  (requires (fun h1 -> n >= 4))
  (ensures (fun h1 n' h2 -> n' >= 8)) =
  2 * n

let test_fun4 (n : nat{n >= 2}) :
  Tot (n':nat{n' >= 8}) =
  4 * n

let test_fun5 (n : nat{n >= 2}) :
  Tot (p:(nat & int){let n1, n2 = p in n1 >= 8 /\ n2 >= 2}) =
  4 * n, 2

let test_fun6 (n1 : nat{n1 >= 4}) (n2 : nat{n2 >= 8}) (n3 : nat{n3 >= 10}) :
  Tot (n:int{n >= 80}) =
  (n1 + n2) * n3

let test_stack1 (n : nat) :
  ST.Stack (n':int{n' >= 0})
  (requires (fun h0 -> n >= 1 /\ B.live h0 (B.null #nat)))
  (ensures (fun h0 n' h1 -> B.modifies B.loc_none h0 h1 /\ n' >= n)) =
  n + 1

let test_lemma1 (n : nat) :
  Lemma (n * n >= 0) = ()

let test_lemma2 (n : nat) :
  Lemma
  (requires (n >= 4 /\ True))
  (ensures (2 * n >= 8)) = ()

let predicate_with_a_very_long_name_to_ensure_break_line (n : nat) : Type0 =
  n >= 4

let test_lemma3 (n : int{n >= 0}) :
  Lemma
  (requires (
    n >= 4 /\ n * n >= 0 /\ n >= 0 /\ n * n + n + 3 >= 0 /\
    predicate_with_a_very_long_name_to_ensure_break_line n))
  (ensures (2 * n >= 8)) = ()

let test_lemma4 (n1 : nat{n1 >= 3}) (n2 : int{n2 >= 5}) (n3 n4 n5 : nat):
  Lemma
  (requires (n3 + n4 + n5 >= 1))
  (ensures (n1 * n2 * (n3 + n4 + n5) >= 15)) = ()

(**** Post-processing *)
//#push-options "--admit_smt_queries true"
[@(postprocess_with (pp_focused_term false))]
let pp_test0 () : Tot nat =
  let x = 1 in
  let y = 2 in
  let _ = focus_on_term in
  test_fun1 (3 * x + y)

[@(postprocess_with (pp_focused_term false))]
let pp_test1 () : Tot nat =
  let x = 1 in
  let y = 2 in
  if x >= y then
    let _ = focus_on_term in
    test_fun1 (3 * x + y)
  else 0

[@(postprocess_with (pp_focused_term false))]
let pp_test2 () : Tot int =
  let x = 4 in
  let y = 9 in
  let z = 11 in
  if x <= y then
    let _ = focus_on_term in
    test_fun6 x y z
  else 0

[@(postprocess_with (pp_focused_term false))]
let pp_test3 () : Tot nat =
  let x = 4 in
  let y = 9 in
  let z = 11 in
  if x <= y then
    let _ = focus_on_term in
    let w = test_fun6 x y z in
    w
  else 0

[@(postprocess_with (pp_focused_term false))]
let pp_test4 (y : nat) :
  ST.Stack nat
  (requires (fun _ -> y >= 2))
  (ensures (fun _ _ _ -> 3 >= 2)) =
  let x = 2 in
  let _ = focus_on_term in
  let w = test_stack1 x in
  w

[@(postprocess_with (pp_focused_term false))]
let pp_test4_1 (y : nat) :
  ST.Stack nat
  (requires (fun _ -> y >= 2))
  (ensures (fun _ _ _ -> 3 >= 2)) =
  let y = 3 in
  let x = 2 in
  let _ = focus_on_term in
  let w = test_stack1 x in
  w

[@(postprocess_with (pp_focused_term false))]
let pp_test5 () :
  ST.Stack nat
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> 3 >= 2)) =
  let x = 2 in
  let _ = focus_on_term in
  test_stack1 x

[@(postprocess_with (pp_focused_term true))]
let pp_test6 () :
  ST.Stack (n:nat{n % 2 = 0})
  (requires (fun _ -> True))
  (ensures (fun _ n _ -> n >= 2)) =
  let x : int = 2 in
  let _ = focus_on_term in
  x

/// Tests with shadowed dependent types
type ty1 (a : Type) : Type0 = list a
type ty2 (a b : Type0) = list a & option b
let pred1 (#a : Type) (x : ty1 a) : Tot bool = Cons? x

/// x is shadowed, so the global precondition should be dropped. However the
/// global post-condition should be displayed.
[@(postprocess_with (pp_focused_term true))]
let pp_test7 (a : Type) (x : ty1 a) :
  Pure (ty1 a)
  (requires x == x /\ a == a)
  (ensures fun x' -> x == x') =
  let y = x in
  let a = nat in
  let x = 3 in
  let _ = focus_on_term in
  y

/// The global precondition should be displayed.
[@(postprocess_with (pp_focused_term true))]
let pp_test8 (a : Type) (x : ty1 a) :
  Pure (ty1 a)
  (requires x == x /\ a == a /\ pred1 x)
  (ensures fun x' -> x == x') =
  let _ = focus_on_term in
  let y = x in
  let a = nat in
  let x = 3 in
  let _ = focus_on_term in
  y

[@(postprocess_with (pp_focused_term true))]
let pp_test9 (y : int{y >= 10}) :
  Tot nat =
  let _ = focus_on_term in
  test_lemma3 y;
  0

[@(postprocess_with (pp_focused_term true))]
let pp_test10 (n : nat{n % 4 = 0}) :
  Tot (n:nat{n % 2 = 0}) =
  let _ = focus_on_term in
  2 * n

(* Shadowing a parameter with a function's return value *)
[@(postprocess_with (pp_focused_term true))]
let pp_test11 (n : nat{n >= 4}) :
  Tot (n:nat{n % 2 = 0}) =
  let _ = focus_on_term in
  let n = test_fun1 n in
  n

(**** Wrapping with tactics *)

// Rk.: problems with naming: use synth: let x = _ by (...)
  
#push-options "--admit_smt_queries true"
[@(postprocess_with pp_tac)]
let test1 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Pure (n:nat{n >= 17})
  (requires (x % 3 = 0))
  (ensures (fun n -> n % 2 = 0)) =
  test_lemma1 x; (**)
  run_tactic (fun _ -> print_binders_info true (top_env()));
  17

let test2 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Lemma(x + y + z >= 26) =
  (* Look for the binder after the one with type "Prims.pure_post".
   * Or: count how many parameters the function has... *)
  run_tactic (fun _ -> print_binders_info true (top_env ()))

let test3 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Lemma (requires x % 2 = 0) (ensures x + y + z >= 26) =
  (* The pre and the post are put together in a conjunction *)
  run_tactic (fun _ -> print_binders_info true (top_env()))

let test4 (x : nat{x >= 4}) :
  ST.Stack nat
  (requires (fun h -> x % 2 = 0))
  (ensures (fun h1 y h2 -> y % 3 = 0)) =
  (* Look after FStar.Pervasives.st_post_h FStar.Monotonic.HyperStack.mem Prims.nat
   * and FStar.Monotonic.HyperStack.mem *)
  run_tactic (fun _ -> print_binders_info true (top_env()));
  3

let test5 (x : nat{x >= 4}) :
  ST.Stack nat
  (requires (fun h -> x % 2 = 0))
  (ensures (fun h1 y h2 -> y % 3 = 0)) =
  (* Shadowing: we can't use the pre anymore... *)
  let x = 5 in
  test_lemma1 x;
  run_tactic (fun _ -> print_binders_info false (top_env()));
  3

let test5_1 (x : nat{x >= 4}) :
  ST.Stack nat
  (requires (fun h -> x % 2 = 0))
  (ensures (fun h1 y h2 -> y % 3 = 0)) =
  (* When using ``synth``, we don't see the same thing *)
  let x = 5 in
  test_lemma1 x;
  let _ : unit = _ by (print_binders_info false (top_env()); exact (`())) in
  3

(* Playing with module definitions *)
let test5_2 (x : nat{x >= 4}) :
  ST.Stack nat
  (requires (fun h -> x % 2 = 0))
  (ensures (fun h1 y h2 -> y % 3 = 0)) =
  let x = 5 in
  test_lemma1 x;
  run_tactic (
    fun () ->
    let opt_sig = lookup_typ (top_env ()) ["PrintTactics"; "Unknown"] in
    begin match opt_sig with
    | Some sig -> print "Found signature"
    | _ -> print "No signature"
    end;
    iter (fun fv -> print (fv_to_string fv)) (defs_in_module (top_env()) ["PrintTactics"])
    );
  3

(* Trying to use different names between the declaration and the definition *)
val test6 (x : nat{x >= 4}) :
  ST.Stack nat
  (requires (fun h -> x % 2 = 0))
  (ensures (fun h1 y h2 -> y % 3 = 0))

(* It's ok: the pre references y *)
let test6 y =
  run_tactic (fun _ -> print_binders_info false (top_env()));
  3

(* TODO: what is ``lookup_attr`` used for? *)
let test7 (x : nat) : nat =
  [@inline_let] let y = x + 1 in
  run_tactic (fun _ ->
    let e = top_env () in
    print "> lookup_attr";
    iter (fun a -> print (flatten_name (inspect_fv a))) (lookup_attr (quote y) e);
    (* Warning: takes some time! *)
//    print "> all_defs_in_env";
//    iter (fun a -> print (flatten_name (inspect_fv a))) (all_defs_in_env e);
    ()
  );
  0

let test8 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Tot (n:nat{n % 2 = 0}) =
  let a = 3 in
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  let w = 3 in
  test_lemma1 w;
  test_lemma3 x;
  (**) test_lemma3 x; (**)
  (**) test_lemma3 y; (**)
  test_lemma4 x y x 1 2;
  2

//[@(postprocess_with pp_tac)]
let test9 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Tot (n:nat{n % 2 = 0}) =
  let a = 3 in
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  let w = 3 in
  test_lemma1 w;
  test_lemma3 x;
  (**) test_lemma3 x; (**)
  (**) test_lemma3 y; (**)
  test_lemma4 x y x 1 2;
  let w = test_fun4 x in
  _ by (
    let s = term_to_string (cur_goal ()) in
    iteri (fun i g -> print ("goal " ^ (string_of_int i) ^ ": " ^
                          (term_to_string (goal_type g)))) (goals());
    iteri (fun i g -> print ("smt goal " ^ (string_of_int i) ^ ": " ^
                          (term_to_string (goal_type g)))) (smt_goals());
    tadmit_no_warning())


let test10 () : Lemma(3 >= 2) =
  _ by (
    let s = term_to_string (cur_goal ()) in
    iteri (fun i g -> print ("goal " ^ (string_of_int i) ^ ":" ^
                          "\n- type: " ^ (term_to_string (goal_type g)) ^
                          "\n- witness: " ^ (term_to_string (goal_witness g))))
                          (goals());
    iteri (fun i g -> print ("smt goal " ^ (string_of_int i) ^ ": " ^
                          (term_to_string (goal_type g)))) (smt_goals());
    print ("- qualif: " ^ term_construct (cur_goal ()));
    tadmit_no_warning())

module PrintTactics

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.List
open FStar.Tactics
open FStar.Mul

/// TODO: precondition, postcondition, current goal, unfold

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"

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

let test_lemma1 (n : nat) :
  Lemma (n * n >= 0) = ()

let test_lemma2 (n : nat) :
  Lemma
  (requires (n >= 4))
  (ensures (2 * n >= 8)) = ()

let predicate_with_a_very_long_name_to_ensure_break_line (n : nat) : Type0 =
  n >= 4

let test_lemma3 (n : nat) :
  Lemma
  (requires (
    n >= 4 /\ n * n >= 0 /\ n >= 0 /\ n * n + n + 3 >= 0 /\
    predicate_with_a_very_long_name_to_ensure_break_line n))
  (ensures (2 * n >= 8)) = ()

(* Return the qualifier of a term as a string *)
val term_qualifier (t : term) : Tac string

let term_qualifier (t : term) : Tac string =
  match inspect t with
  | Tv_Var _ -> "Tv_Var"
  | Tv_BVar _ -> "Tv_BVar"
  | Tv_FVar _ -> "Tv_FVar"
  | Tv_App _ _ -> "Tv_App"
  | Tv_Abs _ _ -> "Tv_Abs"
  | Tv_Arrow _ _ -> "Tv_Arrow"
  | Tv_Type _ -> "Tv_Type"
  | Tv_Refine _ _ -> "Tv_Refine"
  | Tv_Const _ -> "Tv_Const"
  | Tv_Uvar _ _ -> "Tv_Uvar"
  | Tv_Let _ _ _ _ _ -> "Tv_Let"
  | Tv_Match _ _ -> "Tv_Match"
  | Tv_AscribedT _ _ _ -> "Tv_AscribedT"
  | Tv_AscribedC _ _ _ -> "Tv_AScribedC"
  | _ -> "Tv_Unknown"

(* Return the qualifier of a comp as a string *)
val comp_qualifier (c : comp) : Tac string

#push-options "--ifuel 1"
let comp_qualifier (c : comp) : Tac string =
  match inspect_comp c with
  | C_Total _ _ -> "C_Total"
  | C_GTotal _ _ -> "C_GTotal"
  | C_Lemma _ _ _ -> "C_Lemma"
  | C_Eff _ _ _ _ -> "C_Eff"
#pop-options

/// Effect information: we list the current supported effects
type effect_type =
| E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure | E_Stack | E_ST

val effect_type_to_string : effect_type -> string

#push-options "--ifuel 1"
let effect_type_to_string ety =
  match ety with
  | E_Total -> "E_Total"
  | E_GTotal -> "E_GTotal"
  | E_Lemma -> "E_Lemma"
  | E_PURE -> "E_PURE"
  | E_Pure -> "E_Pure"
  | E_Stack -> "E_Stack"
  | E_ST -> "E_ST"
#pop-options

let pure_effect_name = "Prims.PURE"
let pure_hoare_effect_name = "Prims.Pure"
let stack_effect_name = "FStar.HyperStack.ST.Stack"
let st_effect_name = "FStar.HyperStack.ST.ST"

val effect_name_to_type (ename : name) : Tot (option effect_type)

let effect_name_to_type (ename : name) : Tot (option effect_type) =
  let ename = implode_qn ename in
  if ename = pure_effect_name then Some E_PURE
  else if ename = pure_hoare_effect_name then Some E_Pure
  else if ename = stack_effect_name then Some E_Stack
  else if ename = st_effect_name then Some E_ST
  else None

/// Effectful term information
noeq type eterm_info = {
  etype : effect_type;
  pre : option term;
  post : option term;
  ret : option typ;
  ret_refin : option term;
  (* ``goal`` is used when the term is the return result of a function:
   * it contains the proof obligation (which is generally a function of
   * the result) *)
  goal : option term;
}

let mk_eterm_info etype pre post ret ret_refin goal : eterm_info =
  Mketerm_info etype pre post ret ret_refin goal

/// Returns the effectful information about a term
val get_eterm_info : term -> Tac (option eterm_info)

#push-options "--ifuel 1"
let get_eterm_info (t : term) =
  (* Retrieve the type of the function *)
  let e = top_env () in
  (* Note that the call to ``tcc`` might fail *)
  try
    begin
    let c : comp = tcc e t in
    let cv : comp_view = inspect_comp c in
    match cv with
    | C_Total ret_type decr ->
      print ("C_Total: " ^ (term_to_string ret_type));
      Some (mk_eterm_info E_Total None None (Some ret_type) None None)
    | C_GTotal ret_type decr ->
      print ("C_GTotal: " ^ (term_to_string ret_type));
      Some (mk_eterm_info E_GTotal None None (Some ret_type) None None)
    | C_Lemma pre post patterns ->
      print "C_Lemma:";
      print ("- pre:\n" ^ (term_to_string pre));
      print ("- post:\n" ^ (term_to_string post));
      print ("- patterns:\n" ^ (term_to_string patterns));
      Some (mk_eterm_info E_Lemma (Some pre) (Some post) None None None)
    | C_Eff univs eff_name result eff_args ->
      print "C_Eff:";
      print ("eff_name: " ^ (implode_qn eff_name));
      print ("result: " ^ (term_to_string result));
      print "eff_args";
      iter (fun (a, _) -> print ("arg: " ^ (term_to_string a))) eff_args;
      (* Handle the common effects *)
      begin match effect_name_to_type eff_name, eff_args with
      | Some E_PURE, [(pre, _)] ->
        Some (mk_eterm_info E_PURE (Some pre) None (Some result) None None)
      | Some E_Pure, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Pure (Some pre) (Some post) (Some result) None None)
      | Some E_Stack, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Stack (Some pre) (Some post) (Some result) None None)
      | Some E_ST, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_ST (Some pre) (Some post) (Some result) None None)
      | _, _ ->
        print ("Unknown or inconsistant effect: " ^ (implode_qn eff_name));
        None
      end
    end
  with | _ ->
    print ("get_eterm_info: error: could not compute the type of '" ^
           (term_to_string t) ^ "'");
    None
#pop-options
  
val simplify_eterm_info : list norm_step -> eterm_info -> Tac eterm_info

#push-options "--ifuel 1"
let simplify_eterm_info steps info =
  let e = top_env () in
  let opt_norm (x : option term) : Tac (option term) =
    match x with | Some x' -> Some (norm_term_env e steps x') | None -> None
  in
  {
    info with
    pre = opt_norm info.pre;
    post = opt_norm info.post;
    ret_refin = opt_norm info.ret_refin;
  }
#pop-options

val get_type_refin : typ -> Tac (option term)

let get_type_refin t =
  match inspect t with
  | Tv_Refine bv refin ->
    let b : binder = pack_binder bv Q_Explicit in
    Some (pack (Tv_Abs b refin))
  | _ -> None

/// Print the effectful information about a term in a format convenient to
/// use for the emacs commands
val print_eterm_info : eterm_info -> term -> list term -> Tac unit

#push-options "--ifuel 1"
let print_eterm_info info ret_arg post_args =
    (* Instanciate the post-condition and simplify the info *)
    let spost =
      match info.post with
      | Some post -> Some (mk_e_app post post_args)
      | None -> None
    in
    (* Retrieve the return type refinement, instanciate it and simplify it *)
    let sret_refin =
      match info.ret with
      | Some ret ->
        begin match get_type_refin ret with
        | Some refin -> Some (mk_e_app ret [ret_arg])
        | None -> None
        end
      | _ -> None
    in
    let info' = { info with post = spost; ret_refin = sret_refin } in
    let sinfo = simplify_eterm_info [] info' in
    (* Print the information *)
    let print_opt_term name t : Tac unit =
      match t with
      | Some t' ->
        print ("eterm_info:" ^ name ^ ":\n" ^ (term_to_string t'))
      | None -> print ("eterm_info:" ^ name ^ ":'NONE'")
    in
    print ("eterm_info:BEGIN");
    print ("eterm_info:etype:" ^ (effect_type_to_string info.etype));
    print_opt_term "pre" sinfo.pre;
    print_opt_term "post" sinfo.post;
    print_opt_term "result" sinfo.ret;
    print_opt_term "ret" sinfo.ret;
    print_opt_term "ret_refin" sinfo.ret_refin;
    print_opt_term "goal" sinfo.goal;
    print ("eterm_info:END")
#pop-options

//val get_eterm_info : term -> Tac (option eterm_info)
(* Substitutions:
Prims.l_True
Prims.l_False
*)

/// The tactic to be called by the emacs commands
val dprint_eterm : term -> term -> list term -> Tac unit

#push-options "--ifuel 1"
let dprint_eterm t ret_arg post_args =
  match get_eterm_info t with
  | None ->
    print ("dprint_eterm: could not retrieve effect information from: '" ^
           (term_to_string t) ^ "'")
  | Some info ->
    print_eterm_info info ret_arg post_args

let test (x : nat{x >= 4}) : nat =
  test_lemma1 x; (**)
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  let y = 3 in
  test_lemma1 y;
  test_lemma3 x;
  admit()

(*
(setq debug-on-error t)

assert(2 * x >= 8);

  //
  (**) let y = test_fun1 x in (**)  
  (**) let z = 3 in (**)  (**)  
  run_tactic (fun _ -> dprint_eterm (quote (test_lemma1 x)) (`()) [(`())]);
//  run_tactic (fun _ -> dprint_eterm (quote x) (`()) []);
  admit()
  x


(*


(global-set-key (kbd "C-M-x") 'eval-region)

(setq debug-on-error t)

*)

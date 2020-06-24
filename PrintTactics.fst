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

let test_fun4 (n : nat{n >= 2}) :
  Tot (n':nat{n' >= 8}) =
  4 * n

let test_fun5 (n : nat{n >= 2}) :
  Tot (p:(nat & int){let n1, n2 = p in n1 >= 8 /\ n2 >= 2}) =
  4 * n, 2

let test_lemma1 (n : nat) :
  Lemma (n * n >= 0) = ()

let test_lemma2 (n : nat) :
  Lemma
  (requires (n >= 4 /\ True))
  (ensures (2 * n >= 8)) = ()

let predicate_with_a_very_long_name_to_ensure_break_line (n : nat) : Type0 =
  n >= 4

let test_lemma3 (n : nat) :
  Lemma
  (requires (
    n >= 4 /\ n * n >= 0 /\ n >= 0 /\ n * n + n + 3 >= 0 /\
    predicate_with_a_very_long_name_to_ensure_break_line n))
  (ensures (2 * n >= 8)) = ()

/// Some constants
let prims_true_name = "Prims.l_True"

let pure_effect_name = "Prims.PURE"
let pure_hoare_effect_name = "Prims.Pure"
let stack_effect_name = "FStar.HyperStack.ST.Stack"
let st_effect_name = "FStar.HyperStack.ST.ST"

/// Return the qualifier of a term as a string
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

/// Return the qualifier of a comp as a string
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

val effect_name_to_type (ename : name) : Tot (option effect_type)

let effect_name_to_type (ename : name) : Tot (option effect_type) =
  let ename = implode_qn ename in
  if ename = pure_effect_name then Some E_PURE
  else if ename = pure_hoare_effect_name then Some E_Pure
  else if ename = stack_effect_name then Some E_Stack
  else if ename = st_effect_name then Some E_ST
  else None

/// Refinement type information
noeq type rtype_info = {
  raw : typ; // Raw type
  refin : term; // Refinement predicate
}

let mk_rtype_info raw refin : rtype_info =
  Mkrtype_info raw refin

/// Type information
noeq type type_info = {
  ty : typ;
  rty : option rtype_info;
}

let mk_type_info ty rty : type_info =
  Mktype_info ty rty

val safe_tc (e:env) (t:term) : Tac (option term)

let safe_tc e t =
  try Some (tc e t) with | _ -> None

val safe_tcc (e:env) (t:term) : Tac (option comp)

let safe_tcc e t =
  try Some (tcc e t) with | _ -> None

val get_refin_from_type : typ -> Tac (option term)

let get_refin_from_type t =
  print ("get_refin_from_type: " ^ term_to_string t);
  match inspect t with
  | Tv_Refine bv refin ->
    print ("Tv_Refine " ^ term_to_string refin);
    let b : binder = pack_binder bv Q_Explicit in
    Some (pack (Tv_Abs b refin))
  | _ -> None

(*let compute_type_refinement

let compute_type_info (e:env) (t:term) : Tac (option type_info) =
  match safe_tc e t with
  | None -> None
  | Some ty ->
    match inspect ty with
    | Tv_Refine bv ref ->
      let b : binder = pack_binder bv Q_Explicit in
      Some (pack (Tv_Abs b refin))
  | Tv_Refine : bv:bv -> ref:term -> term_view *)

/// Parameter information
noeq type param_info = {
  t : term;
  qualif : aqualv;
  ty : option type_info; // The type of the term
  pty : option type_info; // The type of the expected parameter
}

let mk_param_info t qualif ty pty : param_info =
  Mkparam_info t qualif ty pty

/// Effectful term information
noeq type eterm_info = {
  etype : effect_type;
  pre : option term;
  post : option term;
  ret : option typ;
  ret_refin : option term;
  (* If the term is a function: its head and parameters *)
  head : term;
  parameters : list param_info;
  (* ``goal`` is used when the term is the return result of a function:
   * it contains the proof obligation (which is generally a function of
   * the result) *)
  goal : option term;
}

let mk_eterm_info etype pre post ret ret_refin head parameters goal : eterm_info =
  Mketerm_info etype pre post ret ret_refin head parameters goal

/// Decompose a function application between its body and parameters
val decompose_application : env -> term -> Tac (term & list param_info)

(* let rec decompose_application_aux (e : env) (t : term) :
  Tac (term & list param_info) =
  match inspect t with
  | Tv_App hd (a, qualif) ->
    let hd0, params = decompose_application_aux e hd in
    (* Parameter type *)
    let ty = safe_tc e a in
    (* Type expected by the function *)
    let hd_ty = safe_tc e hd in
  | _ -> t, []
Tv_App    : hd:term -> a:argv -> term_view*)

/// Returns the effectful information about a term
val get_eterm_info : term -> Tac (option eterm_info)

#push-options "--ifuel 1"
let get_eterm_info (t : term) =
  let e = top_env () in
  (* Decompose the term if it is a function application *)
  let hd, parameters = t, [] in // TODO
  (* Note that the call to ``tcc`` might fail *)
  try
    begin
    let c : comp = tcc e t in
    let cv : comp_view = inspect_comp c in
    match cv with
    | C_Total ret_type decr ->
      print ("C_Total: " ^ (term_to_string ret_type));
      Some (mk_eterm_info E_Total None None (Some ret_type) None hd parameters None)
    | C_GTotal ret_type decr ->
      print ("C_GTotal: " ^ (term_to_string ret_type));
      Some (mk_eterm_info E_GTotal None None (Some ret_type) None hd parameters None)
    | C_Lemma pre post patterns ->
      print "C_Lemma:";
      print ("- pre:\n" ^ (term_to_string pre));
      print ("- post:\n" ^ (term_to_string post));
      print ("- patterns:\n" ^ (term_to_string patterns));
      Some (mk_eterm_info E_Lemma (Some pre) (Some post) None None hd parameters None)
    | C_Eff univs eff_name result eff_args ->
      print "C_Eff:";
      print ("- eff_name: " ^ (implode_qn eff_name));
      print ("- result: " ^ (term_to_string result));
      print "- eff_args:";
      iter (fun (a, _) -> print ("arg: " ^ (term_to_string a))) eff_args;
      (* Handle the common effects *)
      begin match effect_name_to_type eff_name, eff_args with
      | Some E_PURE, [(pre, _)] ->
        Some (mk_eterm_info E_PURE (Some pre) None (Some result) None hd parameters None)
      | Some E_Pure, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Pure (Some pre) (Some post) (Some result) None hd parameters None)
      | Some E_Stack, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Stack (Some pre) (Some post) (Some result) None hd parameters None)
      | Some E_ST, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_ST (Some pre) (Some post) (Some result) None hd parameters None)
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

/// Check if a proposition is trivial (i.e.: is True)
val is_trivial_proposition : term -> Tac bool

let is_trivial_proposition t =
  match inspect t with
  | Tv_FVar fv ->
    if implode_qn (inspect_fv fv) = prims_true_name then true else false
  | _ -> false

/// Simplify the fields of a term and remove the useless ones (i.e.: trivial conditions)
val simplify_eterm_info : env -> list norm_step -> eterm_info -> Tac eterm_info

#push-options "--ifuel 1"
let simplify_eterm_info e steps info =
  let opt_norm (x : option term) : Tac (option term) =
    match x with
    | Some x' -> Some (norm_term_env e steps x')
    | None -> None
  in
  let opt_norm_simplify (x : option term) : Tac (option term) =
    match opt_norm x with
    | Some x' -> if is_trivial_proposition x' then None else Some x'
    | None -> None
  in
  {
    info with
    pre = opt_norm_simplify info.pre;
    post = opt_norm_simplify info.post;
    ret_refin = opt_norm_simplify info.ret_refin;
    goal = opt_norm_simplify info.ret_refin;
  }
#pop-options

/// Print the effectful information about a term in a format convenient to
/// use for the emacs commands
val print_eterm_info : env -> eterm_info -> option string -> term -> list term -> Tac unit

(* TODO: ret_arg: the introduced variables get replaced... *)
#push-options "--ifuel 1"
let print_eterm_info e info ret_arg_name ret_arg post_args =
    print ("ret_arg: " ^ term_to_string ret_arg);
    (* Instanciate the post-condition and simplify the information *)
    let spost =
      match info.post with
      | Some post -> Some (mk_e_app post post_args)
      | None -> None
    in
    (* Retrieve the return type refinement, instanciate it and simplify it *)
    let sret_refin, e =
      match info.ret with
      | Some ret_ty ->
        (* TODO: get_refin_from_type should have been called before *)
        begin match get_refin_from_type ret_ty with
        | Some refin ->
          let ret_arg, e =
            match ret_arg_name with
            | Some name ->
              let fbv : bv = fresh_bv_named name ret_ty in
              let b : binder = pack_binder fbv Q_Explicit in
              pack (Tv_Var fbv), push_binder e b
            | None -> ret_arg, e
          in
          Some (mk_e_app refin [ret_arg]), e
        | None -> None, e
        end
      | _ -> None, e
    in
    let info' = { info with post = spost; ret_refin = sret_refin } in
    let sinfo = simplify_eterm_info e [primops; simplify] info' in
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
val dprint_eterm : term -> option string -> term -> list term -> Tac unit

#push-options "--ifuel 1"
let dprint_eterm t ret_arg_name ret_arg post_args =
  match get_eterm_info t with
  | None ->
    print ("dprint_eterm: could not retrieve effect information from: '" ^
           (term_to_string t) ^ "'")
  | Some info ->
    print_eterm_info (top_env ()) info ret_arg_name ret_arg post_args
#pop-options

let _debug_print_var (name : string) (t : term) : Tac unit =
  print ("_debug_print_var: " ^ name ^ ": " ^ term_to_string t);
  begin match safe_tc (top_env ()) t with
  | Some ty -> print ("type: " ^ term_to_string ty)
  | _ -> ()
  end;
  print ("qualifier: " ^ term_qualifier t);
  begin match inspect t with
  | Tv_Var bv ->
    let b : bv_view = inspect_bv bv in
    print ("Tv_Var: ppname: " ^ b.bv_ppname ^
           "; index: " ^ (string_of_int b.bv_index) ^
           "; sort: " ^ term_to_string b.bv_sort)
  | _ -> ()
  end;
  print "end of _debug_print_var"

let test1 (x : nat{x >= 4}) : nat =
  test_lemma1 x; (**)
//  run_tactic (fun _ -> dprint_eterm (quote (test_lemma1 x)) (`()) [(`())]);
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  let y = 3 in
  test_lemma1 y;
  test_lemma3 x;
  let y = test_fun4 x in
  run_tactic (fun _ -> dprint_eterm (quote (test_fun4 x)) (Some "y") (quote y) [(`())]);
  admit()
  let n1, n2 = test_fun5 x in
//  run_tactic (fun _ -> print ("n1: " ^ term_to_string (quote n1)));
  run_tactic (fun _ -> _debug_print_var "n1" (quote n1));
  run_tactic (fun _ -> _debug_print_var "n2" (quote n2));
  run_tactic (fun _ -> dprint_eterm (quote (test_fun5 x)) None (`(`#(quote n1), `#(quote n2))) [(`())]);
  x


let test2 (x : nat{x >= 4}) : nat =
  test_lemma1 x; (**)
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  test_lemma2 x;
  test_lemma2 6;
  let y = 3 in
  test_lemma1 y;
  test_lemma3 x;
  admit()

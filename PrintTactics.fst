module PrintTactics

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.List
open FStar.Tactics
open FStar.Mul

/// TODO: precondition, postcondition, current goal, unfold

#push-options "--z3rlimit 15 --fuel 0 --ifuel 0"

(* TODO: move to FStar.Tactics.Util.fst *)
#push-options "--ifuel 1"
val iteri_aux: int -> (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

val iteri: (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let iteri f x = iteri_aux 0 f x
#pop-options


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

val get_rtype_info_from_type : typ -> Tac (option rtype_info)

let get_rtype_info_from_type t =
  print ("get_rtype_info_from_type: " ^ term_to_string t);
  match inspect t with
  | Tv_Refine bv refin ->
    print ("Tv_Refine " ^ term_to_string refin);
    let bview : bv_view = inspect_bv bv in
    let raw_type : typ = bview.bv_sort in
    let b : binder = pack_binder bv Q_Explicit in
    let refin = pack (Tv_Abs b refin) in
    Some (mk_rtype_info raw_type refin)
  | _ -> None

#push-options "--ifuel 1"
let get_type_info (e:env) (t:term) : Tac (option type_info) =
  match safe_tc e t with
  | None -> None
  | Some ty ->
    let refin = get_rtype_info_from_type ty in
    Some (mk_type_info ty refin)
#pop-options

let get_type_info_from_type (e:env) (ty:term) : Tac type_info =
  let refin = get_rtype_info_from_type ty in
  mk_type_info ty refin

/// Parameter information
noeq type param_info = {
  t : term;
  qualif : aqualv;
  p_ty : option type_info; // The type of the term
  exp_ty : option type_info; // The type of the expected parameter
}

let mk_param_info t qualif p_ty exp_ty : param_info =
  Mkparam_info t qualif p_ty exp_ty

/// Effectful term information
noeq type eterm_info = {
  etype : effect_type;
  pre : option term;
  post : option term;
  ret_type : option type_info;
  (* If the term is a function: its head and parameters *)
  head : term;
  parameters : list param_info;
  (* ``goal`` is used when the term is the return result of a function:
   * it contains the proof obligation (which is generally a function of
   * the result) *)
  goal : option term;
}

let mk_eterm_info etype pre post ret_type head parameters goal : eterm_info =
  Mketerm_info etype pre post ret_type head parameters goal

/// Decompose a function application between its body and parameters
val decompose_application : env -> term -> Tac (term & list param_info)

#push-options "--ifuel 1"
let rec decompose_application_aux (e : env) (t : term) :
  Tac (term & list param_info) =
  match inspect t with
  | Tv_App hd (a, qualif) ->
    let hd0, params = decompose_application_aux e hd in
    (* Parameter type *)
    let a_type = get_type_info e a in
    (* Type expected by the function *)
    let hd_ty = safe_tc e hd in
    let param_type =
      match hd_ty with
      | None -> None
      | Some hd_ty' ->
        match inspect hd_ty' with
        | Tv_Arrow b c ->
          let bv, _ = inspect_binder b in
          let bview = inspect_bv bv in
          let ty = bview.bv_sort in
          let rty = get_rtype_info_from_type ty in
          Some (mk_type_info ty rty)
        | _ -> None
    in
    let param_info = mk_param_info a qualif a_type param_type in
    hd0, param_info :: params
  | _ -> t, []
#pop-options

let decompose_application e t =
  let hd, params = decompose_application_aux e t in
  hd, List.Tot.rev params

/// Returns the effectful information about a term
val get_eterm_info : env -> term -> Tac (option eterm_info)

#push-options "--ifuel 1"
let get_eterm_info (e:env) (t : term) =
  (* Decompose the term if it is a function application *)
  let hd, parameters = decompose_application e t in
  (* Note that the call to ``tcc`` might fail *)
  try
    begin
    let c : comp = tcc e t in
    let cv : comp_view = inspect_comp c in
    match cv with
    | C_Total ret_ty decr ->
      print ("C_Total: " ^ (term_to_string ret_ty));
      let ret_type_info = Some (get_type_info_from_type e ret_ty) in
      Some (mk_eterm_info E_Total None None ret_type_info hd parameters None)
    | C_GTotal ret_ty decr ->
      print ("C_GTotal: " ^ (term_to_string ret_ty));
      let ret_type_info = Some (get_type_info_from_type e ret_ty) in
      Some (mk_eterm_info E_GTotal None None ret_type_info hd parameters None)
    | C_Lemma pre post patterns ->
      print "C_Lemma:";
      print ("- pre:\n" ^ (term_to_string pre));
      print ("- post:\n" ^ (term_to_string post));
      print ("- patterns:\n" ^ (term_to_string patterns));
      (* No return type information - we might put unit *)
      Some (mk_eterm_info E_Lemma (Some pre) (Some post) None hd parameters None)
    | C_Eff univs eff_name ret_ty eff_args ->
      print "C_Eff:";
      print ("- eff_name: " ^ (implode_qn eff_name));
      print ("- result: " ^ (term_to_string ret_ty));
      print "- eff_args:";
      iter (fun (a, _) -> print ("arg: " ^ (term_to_string a))) eff_args;
      let ret_type_info = Some (get_type_info_from_type e ret_ty) in
      (* Handle the common effects *)
      begin match effect_name_to_type eff_name, eff_args with
      | Some E_PURE, [(pre, _)] ->
        Some (mk_eterm_info E_PURE (Some pre) None ret_type_info hd parameters None)
      | Some E_Pure, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Pure (Some pre) (Some post) ret_type_info hd parameters None)
      | Some E_Stack, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_Stack (Some pre) (Some post) ret_type_info hd parameters None)
      | Some E_ST, [(pre, _); (post, _)] ->
        Some (mk_eterm_info E_ST (Some pre) (Some post) ret_type_info hd parameters None)
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

/// Applies normalization steps to an optional proposition (term of type Type).
/// If the proposition gets reduced to True, returns None.
let simplify_opt_proposition (e:env) (steps:list norm_step) (p:option term) :
  Tac (option term) =
  match p with
  | Some x ->
    let x' = norm_term_env e steps x in
    if is_trivial_proposition x' then None else Some x'
  | _ -> None

/// Simplify a type, and remove the refinement if it is trivial
let simplify_type_info (e:env) (steps:list norm_step) (info:type_info) : Tac type_info =
  match info.rty with
  | Some rinfo ->
    let refin' = norm_term_env e steps rinfo.refin in
    if is_trivial_proposition refin' then mk_type_info rinfo.raw None
    else ({ info with rty = Some ({ rinfo with refin = refin' })})
  | _ -> info

let simplify_opt_type_info e steps info : Tac (option type_info) =
  match info with
  | Some info' -> Some (simplify_type_info e steps info')
  | _ -> None

/// Simplify the fields of a term and remove the useless ones (i.e.: trivial conditions)
val simplify_eterm_info : env -> list norm_step -> eterm_info -> Tac eterm_info

#push-options "--ifuel 1"
let simplify_eterm_info e steps info =
  let simpl_prop = simplify_opt_proposition e steps in
  let simpl_type = simplify_opt_type_info e steps in
  let simpl_param (p:param_info) : Tac param_info =
    { p with p_ty = simpl_type p.p_ty; exp_ty = simpl_type p.exp_ty; }
  in
  {
    info with
    pre = simpl_prop info.pre;
    post = simpl_prop info.post;
    ret_type = simpl_type info.ret_type;
    parameters = map simpl_param info.parameters;
    goal = simpl_prop info.goal;
  }
#pop-options

let printout_string (prefix data:string) : Tac unit =
  print (prefix ^ ":\n" ^ data)

let printout_term (prefix:string) (t:term) : Tac unit =
  printout_string prefix (term_to_string t)

let printout_opt_term (prefix:string) (t:option term) : Tac unit =
  match t with
  | Some t' -> printout_term prefix t'
  | None -> print (prefix ^ ":NONE")

let printout_opt_type (prefix:string) (ty:option type_info) : Tac unit =
  let ty, rty_raw, rty_refin =
    match ty with
    | Some ty' ->
      begin match ty'.rty with
      | Some rty' -> Some ty'.ty, Some rty'.raw, Some rty'.refin
      | _ -> Some ty'.ty, None, None
      end
    | _ -> None, None, None
  in
  printout_opt_term (prefix ^ ":ty") ty;
  printout_opt_term (prefix ^ ":rty_raw") rty_raw;
  printout_opt_term (prefix ^ ":rty_refin") rty_refin

(*/// Compare the type of a parameter and its expected tyep
let parameter_has_expected_type (p:param_info) : Tac bool =
  match p.p_ty, exp_ty with
  | Some info1, Some info2 ->
    if term_eq info1.ty info2.ty then true
    else begin match 
      
    end
    match term_eq *)

let printout_parameter (prefix:string) (index:int) (p:param_info) : Tac unit =
  let p_prefix = prefix ^ ":param" ^ string_of_int index in
  printout_term p_prefix p.t;
  printout_opt_type (p_prefix ^ ":p_ty") p.p_ty;
  printout_opt_type (p_prefix ^ ":e_ty") p.exp_ty

let printout_parameters (prefix:string) (parameters:list param_info) : Tac unit =
  printout_string (prefix ^ ":num") (string_of_int (List.length parameters));
  iteri (printout_parameter prefix) parameters

/// The type refinement in a ``type_info`` is initially lambda functions.
/// Instantiate it with the appropriate term so as to generate a predicate.
val instantiate_type_info_refin : term -> type_info -> Tac type_info

let instantiate_type_info_refin t info =
  match info.rty with
  | Some rinfo ->
    let refin' = mk_e_app rinfo.refin [t] in
    let opt_rinfo' = Some ({rinfo with refin = refin'}) in
    { info with rty = opt_rinfo' }
  | _ -> info

val instantiate_opt_type_info_refin : term -> option type_info -> Tac (option type_info)

let instantiate_opt_type_info_refin t info =
  match info with
  | Some info' -> Some (instantiate_type_info_refin t info')
  | _ -> None

/// The type refinements in a ``eterm_info`` are initially lambda functions.
/// Instantiate them with the appropriate terms so as to generate predicates.
val instantiate_refinements : env -> eterm_info -> option string -> term -> list term ->
  Tac (env & eterm_info)

let instantiate_refinements e info ret_arg_name ret_arg post_args =
  (* Instanciate the post-condition and simplify the information *)
  let ipost =
    match info.post with
    | Some post -> Some (mk_e_app post post_args)
    | None -> None
  in
  (* Retrieve the return type refinement and instanciate it*)
  let (iret_type : option type_info), (e' : env) =
    match info.ret_type with
    | Some ret_type_info ->
      begin match ret_type_info.rty with
      | Some ret_type_rinfo ->
        let ret_arg, e' =
          match ret_arg_name with
          | Some name ->
            let fbv : bv = fresh_bv_named name ret_type_rinfo.raw in
            let b : binder = pack_binder fbv Q_Explicit in
            pack (Tv_Var fbv), push_binder e b
          | None -> ret_arg, e
        in
        let refin' = mk_e_app ret_type_rinfo.refin [ret_arg] in
        let ret_type_rinfo : rtype_info = { ret_type_rinfo with refin = refin' } in
        let ret_type_info' = { ret_type_info with rty = Some ret_type_rinfo } in
        Some ret_type_info', e'
      | None -> None, e
      end
    | _ -> None, e
  in
  (* Instantiate the refinements in the parameters *)
  let inst_param (p:param_info) : Tac param_info =
    let p_ty' = instantiate_opt_type_info_refin p.t p.p_ty in
    let exp_ty' = instantiate_opt_type_info_refin p.t p.exp_ty in
    { p with p_ty = p_ty'; exp_ty = exp_ty' }
  in
  let iparameters = map inst_param info.parameters in
  (* Return *)
  e',
  ({ info with
    post = ipost;
    ret_type = iret_type;
    parameters = iparameters })

/// Print the effectful information about a term in a format convenient to
/// use for the emacs commands
val print_eterm_info : env -> eterm_info -> option string -> term -> list term -> Tac unit

(* TODO: ret_arg: the introduced variables get replaced... *)
(* TODO: correct naming for variables derived from tuples *)
#push-options "--ifuel 1"
let print_eterm_info e info ret_arg_name ret_arg post_args =
    print ("ret_arg: " ^ term_to_string ret_arg);
    let sinfo = simplify_eterm_info e [primops; simplify] info in
    (* Print the information *)
    print ("eterm_info:BEGIN");
    print ("eterm_info:etype:" ^ (effect_type_to_string info.etype));
    printout_opt_term "eterm_info:pre" sinfo.pre;
    printout_opt_term "eterm_info:post" sinfo.post;
    printout_opt_type "eterm_info:ret_type" sinfo.ret_type;
    printout_parameters "eterm_info:parameters" sinfo.parameters;
    printout_opt_term "eterm_info:goal" sinfo.goal;
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
  let e = top_env () in
  match get_eterm_info e t with
  | None ->
    print ("dprint_eterm: could not retrieve effect information from: '" ^
           (term_to_string t) ^ "'")
  | Some info ->
    let e = top_env () in
    let e', info' = instantiate_refinements e info ret_arg_name ret_arg post_args in
    print_eterm_info e' info' ret_arg_name ret_arg post_args
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

let test1 (x : nat{x >= 4}) (y : nat{y >= 8}) (z : nat{z >= 10}) : nat =
  test_lemma1 x; (**)
//  run_tactic (fun _ -> dprint_eterm (quote (test_lemma1 x)) (`()) [(`())]);
  (**) test_lemma1 x; (**)
  test_lemma1 (let y = x in y); (**)
  let w = 3 in
  test_lemma1 w;
  test_lemma3 x;
  let w = test_fun4 x in
//  run_tactic (fun _ -> dprint_eterm (quote (test_fun4 x)) (Some "w") (quote w) [(`())]);
//  run_tactic (fun _ -> dprint_eterm (quote (test_fun6 x (2 * x) (3 * x))) (Some "a") (quote y) [(`())]);
  run_tactic (fun _ -> dprint_eterm (quote (test_fun6 x y z)) (Some "a") (quote y) [(`())]);
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

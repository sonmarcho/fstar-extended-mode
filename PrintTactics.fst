module PrintTactics

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul

/// TODO: precondition, postcondition, current goal, unfold

#push-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(* TODO: move to FStar.Tactics.Util.fst *)
#push-options "--ifuel 1"
val iteri_aux: int -> (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

val iteri: (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let iteri f x = iteri_aux 0 f x
#pop-options

(* TODO: move to FStar.Reflection.Derived.fst *)
let rec mk_abs (t : term) (args : list binder) : Tot term (decreases args) =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = mk_abs t args' in
    pack_ln (Tv_Abs a t')


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

exception MetaAnalysis of string
let mfail str =
  raise (MetaAnalysis str)

/// Some constants
let prims_true_qn = "Prims.l_True"
let prims_true_term = `Prims.l_True

let pure_effect_qn = "Prims.PURE"
let pure_hoare_effect_qn = "Prims.Pure"
let stack_effect_qn = "FStar.HyperStack.ST.Stack"
let st_effect_qn = "FStar.HyperStack.ST.ST"


/// Return the qualifier of a term as a string
val term_view_construct (t : term_view) : Tac string

let term_view_construct (t : term_view) : Tac string =
  match t with
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

val term_construct (t : term) : Tac string

let term_construct (t : term) : Tac string =
  term_view_construct (inspect t)

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
| E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure | E_Stack | E_ST | E_Unknown

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
  | E_Unknown -> "E_Unknown"
#pop-options

val effect_name_to_type (ename : name) : Tot effect_type

let effect_name_to_type (ename : name) : Tot effect_type =
  let ename = flatten_name ename in
  if ename = pure_effect_qn then E_PURE
  else if ename = pure_hoare_effect_qn then E_Pure
  else if ename = stack_effect_qn then E_Stack
  else if ename = st_effect_qn then E_ST
  else E_Unknown

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

let unit_type_info = mk_type_info (`unit) None

val safe_tc (e:env) (t:term) : Tac (option term)

let safe_tc e t =
  try Some (tc e t) with | _ -> None

val safe_tcc (e:env) (t:term) : Tac (option comp)

let safe_tcc e t =
  try Some (tcc e t) with | _ -> None

val get_rtype_info_from_type : typ -> Tac (option rtype_info)

let get_rtype_info_from_type t =
  match inspect t with
  | Tv_Refine bv refin ->
    let bview : bv_view = inspect_bv bv in
    let raw_type : typ = bview.bv_sort in
    let b : binder = mk_binder bv in
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

/// Cast information
noeq type cast_info = {
  term : term;
  p_ty : option type_info; // The type of the term
  exp_ty : option type_info; // The type of the expected parameter
}

let mk_cast_info t p_ty exp_ty : cast_info =
  Mkcast_info t p_ty exp_ty

/// Effectful term information
noeq type eterm_info = {
  eterm : term;
  etype : effect_type;
  pre : option term;
  post : option term;
  ret_type : type_info;
  (* Head and parameters of the decomposition of the term into a function application *)
  head : term;
  parameters : list cast_info;
  (* The following fields are used when the term is the return value of a
   * function:
   * - ``ret_cast``: contains the cast to the function return type
   * - ``goal``: contains the postcondition of the function *)
  ret_cast : option cast_info;
  goal : option term;
}

let mk_eterm_info eterm etype pre post ret_type head parameters ret_cast goal : eterm_info =
  Mketerm_info eterm etype pre post ret_type head parameters ret_cast goal

(*** Effectful term analysis *)
/// Analyze a term to retrieve its effectful information

(**** Step 1 *)
/// Decompose a function application between its body and parameters
val decompose_application : env -> term -> Tac (term & list cast_info)

#push-options "--ifuel 1"
let rec decompose_application_aux (e : env) (t : term) :
  Tac (term & list cast_info) =
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
    let cast_info = mk_cast_info a a_type param_type in
    hd0, cast_info :: params
  | _ -> t, []
#pop-options

let decompose_application e t =
  let hd, params = decompose_application_aux e t in
  hd, List.Tot.rev params

(*type valid_eterm_info =
  info:eterm_info{
    match info.etype with
    | E_Total | E_GTotal | E_Lemma -> True
    | E_PURE | E_Pure | E_Stack | E_ST | E_Unknown ->
      Some? info.ret_type
  }*)

/// Returns the effectful information about a term
val get_eterm_info : env -> term -> Tac eterm_info

#push-options "--ifuel 2"
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
      let ret_type_info = get_type_info_from_type e ret_ty in
      mk_eterm_info t E_Total None None ret_type_info hd parameters None None
    | C_GTotal ret_ty decr ->
      print ("C_GTotal: " ^ (term_to_string ret_ty));
      let ret_type_info = get_type_info_from_type e ret_ty in
      mk_eterm_info t E_GTotal None None ret_type_info hd parameters None None
    | C_Lemma pre post patterns ->
      print "C_Lemma:";
      print ("- pre:\n" ^ (term_to_string pre));
      print ("- post:\n" ^ (term_to_string post));
      print ("- patterns:\n" ^ (term_to_string patterns));
      (* We use unit as the return type information *)
      mk_eterm_info t E_Lemma (Some pre) (Some post) unit_type_info hd parameters None None
    | C_Eff univs eff_name ret_ty eff_args ->
      print "C_Eff:";
      print ("- eff_name: " ^ (flatten_name eff_name));
      print ("- result: " ^ (term_to_string ret_ty));
      print "- eff_args:";
      iter (fun (a, _) -> print ("arg: " ^ (term_to_string a))) eff_args;
      let ret_type_info = get_type_info_from_type e ret_ty in
      (* Handle the common effects *)
      begin match effect_name_to_type eff_name, eff_args with
      | E_PURE, [(pre, _)] ->
        mk_eterm_info t E_PURE (Some pre) None ret_type_info hd parameters None None
      | E_Pure, [(pre, _); (post, _)] ->
        mk_eterm_info t E_Pure (Some pre) (Some post) ret_type_info hd parameters None None
      | E_Stack, [(pre, _); (post, _)] ->
        mk_eterm_info t E_Stack (Some pre) (Some post) ret_type_info hd parameters None None
      | E_ST, [(pre, _); (post, _)] ->
        mk_eterm_info t E_ST (Some pre) (Some post) ret_type_info hd parameters None None
      (* If the effect is unknown and there are two parameters or less, we make the
       * guess that the first one is a pre-condition and the second one is a
       * post-condition *)
      | E_Unknown, [] ->
        mk_eterm_info t E_Unknown None None ret_type_info hd parameters None None
      | E_Unknown, [(pre, _)] ->
        mk_eterm_info t E_Unknown (Some pre) None ret_type_info hd parameters None None
      | E_Unknown, [(pre, _); (post, _)] ->
        mk_eterm_info t E_Unknown (Some pre) (Some post) ret_type_info hd parameters None None
      | _ ->
        mfail ("Unknown or inconsistant effect: " ^ (flatten_name eff_name))
      end
    end
  with
  | TacticFailure msg ->
    mfail ("get_eterm_info: failure: '" ^ msg ^ "'")
  | e -> raise e
#pop-options

/// Adds the current goal information to an ``eterm_info`` (if the term is a returned value)
val get_goal_info : eterm_info -> Tac eterm_info

/// TODO:
let get_goal_info info =
  let env = cur_env () in
  let goal = cur_goal () in
  info

(**** Step 2 *)
/// The retrieved type refinements and post-conditions are not instantiated (they
/// are lambda functions): instantiate them to get propositions.

/// The type to model a proposition
noeq type proposition = {
  (* The proposition body *)
  prop : term;
  (* The parameters which must be abstracted. It happens that we need to
   * introduce variables that don't appear in the user code (for example,
   * stack memories for the pre and post-condition of stateful functions).
   * In this case, we introduce the appropriate assertions for the pre and
   * the post but written as asbtractions applied to those missing parameters
   * (i.e.: [> assert((fun h1 h2 -> post) h1 h2); ).
   * The user can then replace those parameters (h1 and h2 above) by the proper
   * ones then normalize the assertion by using the appropriate command, to get
   * what he needs. *)
  abs : list binder;
}

/// Propositions split between pre and post assertions
noeq type assertions = {
  pres : list proposition;
  posts : list proposition;
}

let mk_assertions pres posts : assertions =
  Mkassertions pres posts

(***** Types, casts and refinements *)

let has_refinement (ty:type_info) : Tot bool =
  Some? ty.rty

let get_refinement (ty:type_info{Some? ty.rty}) : Tot term =
  (Some?.v ty.rty).refin

let get_opt_refinment (ty:type_info) : Tot (option term) =
  match ty.rty with
  | Some rty -> Some rty.refin
  | None -> None

let get_rawest_type (ty:type_info) : Tot typ =
  match ty.rty with
  | Some rty -> rty.raw
  | _ -> ty.ty

/// Compare the type of a parameter and its expected type
type type_comparison = | Refines | Same_raw_type | Unknown

#push-options "--ifuel 1"
let type_comparison_to_string c =
  match c with
  | Refines -> "Refines"
  | Same_raw_type -> "Same_raw_type"
  | Unknown -> "Unknown"
#pop-options

let compare_types (info1 info2 : type_info) :
  Tot (c:type_comparison{c = Same_raw_type ==> has_refinement info2}) =
  if term_eq info1.ty info2.ty
  then Refines // The types are the same
  else
    let ty1 = get_rawest_type info1 in
    let ty2 = get_rawest_type info2 in
    if term_eq ty1 ty2 then
      if has_refinement info2
      then Same_raw_type // Same raw type but can't say anything about the expected refinement
      else Refines // The first type is more precise than the second type
    else
      Unknown

let compare_cast_types (p:cast_info) :
  Tot (c:type_comparison{
    ((c = Refines \/ c = Same_raw_type) ==> (Some? p.p_ty /\ Some? p.exp_ty)) /\
    (c = Same_raw_type ==> has_refinement (Some?.v p.exp_ty))}) =
  match p.p_ty, p.exp_ty with
  | Some info1, Some info2 -> compare_types info1 info2
  | _ -> Unknown

let opt_cons (#a : Type) (opt_x : option a) (ls : list a) : Tot (list a) =
  match opt_x with
  | Some x -> x :: ls
  | None -> ls

/// Instantiate a proposition.
val term_to_proposition : term -> list term -> list binder -> Tot proposition
let term_to_proposition t params abs_params =
  let p = mk_e_app t params in
  { prop = p; abs = abs_params; }

val opt_term_to_opt_proposition : option term -> list term -> list binder -> Tot (option proposition)
let opt_term_to_opt_proposition opt_t params abs_params =
  match opt_t with
  | Some t -> Some (term_to_proposition t params abs_params)
  | None -> None  

/// Generate the propositions equivalent to a correct type cast.
/// Note that the type refinements need to be instantiated.
val cast_info_to_propositions : cast_info -> Tac (list proposition)
let cast_info_to_propositions ci =
  match compare_cast_types ci with
  | Refines -> []
  | Same_raw_type ->
    let refin = get_refinement (Some?.v ci.exp_ty) in
    let inst_refin = term_to_proposition refin [ci.term] [] in
    [inst_refin]
  | Unknown ->
    match ci.p_ty, ci.exp_ty with
    | Some p_ty, Some e_ty ->
      let p_rty = get_rawest_type p_ty in
      let e_rty = get_rawest_type e_ty in
      (* For the type cast, we generate an assertion of the form:
       * [> has_type (p <: type_of_p) expected_type
       * The reason is that we want the user to know which parameter is
       * concerned (hence the ``has_type``), and which types should be
       * related (hence the ascription).
       *)
      let ascr_term = pack (Tv_AscribedT ci.term p_rty None) in
      let has_type_params = [(p_rty, Q_Implicit); (ascr_term, Q_Explicit); (e_rty, Q_Explicit)] in
      let type_cast = mk_app (`has_type) has_type_params in
      (* Expected type's refinement *)
      let opt_refin = get_opt_refinment e_ty in
      let inst_opt_refin = opt_term_to_opt_proposition opt_refin [ci.term] [] in
      opt_cons inst_opt_refin [{ prop = type_cast; abs = []; }]
    | _ -> []

/// Generates a list of propositions from a list of ``cast_info``. Note that
/// the user should revert the list before printing the propositions.
val cast_info_list_to_propositions : list cast_info -> Tac (list proposition)
let cast_info_list_to_propositions ls =
  let lsl = map cast_info_to_propositions ls in
  flatten lsl

/// Versions of ``fresh_bv`` and ``fresh_binder`` inspired by the standard library
/// We make sure the name is fresh because we need to be able to generate valid code
/// (it is thus not enough to have a fresh integer).
let rec _fresh_bv binder_names basename i ty : Tac bv =
  let name = basename ^ string_of_int i in
  (* In worst case the performance is quadratic in the number of binders,
   * but it is very unlikely that we get the worst case  *)
  if List.mem name binder_names then _fresh_bv binder_names basename (i+1) ty
  else fresh_bv_named name ty

let fresh_bv (e : env) (basename : string) (ty : typ) : Tac bv =
  let binders = binders_of_env e in
  let binder_names = List.Tot.map name_of_binder binders in
  _fresh_bv binder_names basename 0 ty

let fresh_binder (e : env) (basename : string) (ty : typ) : Tac binder =
  let bv = fresh_bv e basename ty in
  mk_binder bv

let push_fresh_binder (e : env) (basename : string) (ty : typ) : Tac (binder & env) =
  let b = fresh_binder e basename ty in
  let e' = push_binder e b in
  b, e'

/// When dealing with unknown effects, we try to guess what the pre and post-conditions
/// are. The effects are indeed very likely to have a pre and a post-condition,
/// and to be parameterized with an internal effect state, so that the pre and posts
/// have the following shapes:
/// - pre  : STATE -> Type0
/// - post : STATE -> RET -> STATE -> Type0
/// Or (no state/pure):
/// - pre  : Type0
/// - post : RET -> Type0
/// We try to detect that with the following functions:
noeq type pre_post_type =
  | PP_Unknown | PP_Pure
  | PP_State : (state_type:term) -> pre_post_type

val get_total_or_gtotal_ret_type : comp -> Tot (option typ)
let get_total_or_gtotal_ret_type c =
  match inspect_comp c with
  | C_Total ret_ty _ | C_GTotal ret_ty _ -> Some ret_ty
  | _ -> None

val check_pre_type : env -> term -> Tac pre_post_type
let check_pre_type e pre =
  match safe_tc e pre with
  | None -> PP_Unknown
  | Some ty ->
    match inspect ty with
    | Tv_Arrow b c ->
      (* Not sure if the comp check is necessary *)
      if Some? (get_total_or_gtotal_ret_type c) then PP_State (type_of_binder b)
      else PP_Unknown
    | _ -> PP_Pure

val check_post_type : env -> term -> term -> Tac pre_post_type
let check_post_type e ret_type post =
  let get_tot_ret_type c : Tac (option term_view) =
    match get_total_or_gtotal_ret_type c with
    | Some ret_ty -> Some (inspect ret_ty)
    | None -> None
  in
  match safe_tc e post with
  | None -> PP_Unknown
  | Some ty ->
    (* The initial state or the return value *)
    match inspect ty with
    | Tv_Arrow b0 c0 ->
      begin match get_tot_ret_type c0 with
      | None -> PP_Unknown
      (* If arrow: the post-condition is for a stateful effect, and the binder
       * we get here gives us the type of the return value *)
      | Some (Tv_Arrow b1 c1) ->
        (* Check that there is a third arrow for the new state *)
        begin match get_tot_ret_type c1 with
        | None -> PP_Unknown
        | Some (Tv_Arrow b2 c2) ->
          (* Just check that the types are coherent: return type, but also states *)
          if term_eq ret_type (type_of_binder b1) &&
             term_eq (type_of_binder b0) (type_of_binder b2)
          then PP_Pure else PP_Unknown
        | _ -> PP_Unknown
        end
      (* Otherwise, it is the post-condition of a pure effect *)
      | Some _ ->
        (* Check that the return value type is consistent *)
        if term_eq ret_type (type_of_binder b0) then PP_Pure else PP_Unknown
      end
    | _ -> PP_Unknown

val check_pre_post_type : env -> term -> term -> term -> Tac pre_post_type
let check_pre_post_type e pre ret_type post =
  match check_pre_type e pre, check_post_type e ret_type post with
  | PP_Pure, PP_Pure -> PP_Pure
  | PP_State ty1, PP_State ty2 ->
    if term_eq ty1 ty2 then PP_State ty1 else PP_Unknown
  | _ -> PP_Unknown

val check_opt_pre_post_type : env -> option term -> term -> option term -> Tac (option pre_post_type)
let check_opt_pre_post_type e opt_pre ret_type opt_post =
  match opt_pre, opt_post with
  | Some pre, Some post -> Some (check_pre_post_type e pre ret_type post)
  | Some pre, None -> Some (check_pre_type e pre)
  | None, Some post -> Some (check_post_type e ret_type post)
  | None, None -> None

val push_two_fresh_vars : env -> string -> typ -> Tac (term & binder & term & binder & env)
let push_two_fresh_vars e0 basename ty =
  let b1, e1 = push_fresh_binder e0 basename ty in
  let b2, e2 = push_fresh_binder e1 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  let v2 = pack (Tv_Var (bv_of_binder b2)) in
  v1, b1, v2, b2,  e2

val _introduce_variables_for_abs : env -> typ -> Tac (list term & list binder & env)
let rec _introduce_variables_for_abs e ty =
  match inspect ty with
  | Tv_Arrow b c ->
    let b1, e1 = push_fresh_binder e (name_of_binder b) (type_of_binder b) in
    let bv1 = bv_of_binder b1 in
    let v1 = pack (Tv_Var bv1) in
    begin match get_total_or_gtotal_ret_type c with
    | Some ty1 ->
      let vl, bl, e2 = _introduce_variables_for_abs e1 ty1 in
      v1 :: vl, b1 :: bl, e2
    | None -> [v1], [b1], e1
    end
 | _ -> [], [], e

val introduce_variables_for_abs : env -> term -> Tac (list term & list binder & env)
let introduce_variables_for_abs e tm =
  match safe_tc e tm with
  | Some ty -> _introduce_variables_for_abs e ty
  | None -> [], [], e

val introduce_variables_for_opt_abs : env -> option term -> Tac (list term & list binder & env)
let introduce_variables_for_opt_abs e opt_tm =
  match opt_tm with
  | Some tm -> introduce_variables_for_abs e tm
  | None -> [], [], e

val effect_type_is_stateful : effect_type -> Tot bool
let effect_type_is_stateful etype =
  match etype with
  | E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure -> false
  | E_Stack | E_ST | E_Unknown -> true

(* val term_to_prop : term -> list term -> list binder -> Tot proposition
let term_to_prop t params abs_params =
  let t = mk_e_app t params in
  { prop = t; abs = abs_params; }

val opt_term_to_prop : option term -> list term -> -> Tot (option proposition)
let opt_term_to_prop opt_t params_info =
  match opt_t with
  | Some t -> Some (term_to_prop t params_info)
  | None -> None *)

/// Convert effectful type information to a list of propositions. May have to
/// introduce additional binders for the preconditions/postconditions/goal (hence
/// the environment in the return type).
/// The ``bind_var`` parameter is a variable if the studied term was bound in a let
/// expression.
val eterm_info_to_assertions : env -> eterm_info -> option term -> Tac (env & assertions)
let eterm_info_to_assertions e info bind_var =
  (* Introduce additional variables to instantiate the return type refinement,
   * the precondition, the postcondition and the goal *)
  (* First, the return value: returns an updated env, the value to use for
   * the return type and a list of abstract binders *)
  let gen_ret_value e : Tac (env & term & list binder) =
    match bind_var with
    | Some v -> e, v, []
    | None ->
      (* If the studied term is not stateless, we can use it directly in the
       * propositions, otherwise we need to introduced a variable *)
      if effect_type_is_stateful info.etype then
        let b = fresh_binder e "__ret" info.ret_type.ty in
        let bv = bv_of_binder b in
        let tm = pack (Tv_Var bv) in
        push_binder e b, tm, [b]
      else e, info.eterm, []
  in
  (* Then, the variables for the pre/postconditions *)
  let e', (ret_values, ret_binders), (pre_values, pre_binders), (post_values, post_binders) =
    match info.etype with
    | E_Lemma ->
      (* Nothing to introduce *)
      e, ([], []), ([], []), ([], [])
    | E_Total | E_GTotal ->
      (* Optionally introduce a variable for the return value *)
      let e', v, brs = gen_ret_value e in
      e', ([v], brs), ([], []), ([], [])
    | E_PURE | E_Pure ->
      (* Optionally introduce a variable for the return value *)
      let e', v, brs = gen_ret_value e in
      e', ([v], brs), ([], []), ([v], brs)
    | E_Stack | E_ST ->
      (* Optionally introduce a variable for the return value *)
      let e0, v, brs = gen_ret_value e in
      (* Introduce variables for the memories *)
      let h1, b1, h2, b2, e2 = push_two_fresh_vars e0 "__h" (`HS.mem) in
      e2, ([v], brs), ([h1], [b1]), ([h1; v; h2], [b1; b2])
    | E_Unknown ->
      (* We don't know what the effect is and the current pre and post-conditions
       * are currently guesses. Introduce any necessary variable abstracted by
       * those parameters *)
      (* Optionally introduce a variable for the return value *)
      let e0, v, brs = gen_ret_value e in
       (* The pre and post-conditions are likely to have the same shape as
        * one of Pure or Stack (depending on whether we use or not an internal
        * state). We try to check that and to instantiate them accordingly *)
      let pp_type = check_opt_pre_post_type e0 info.pre info.ret_type.ty info.post in
      begin match pp_type with
      | Some PP_Pure ->
        (* We only need the return value *)
        e0, ([v], brs), ([], []), ([v], brs)
      | Some (PP_State state_type) ->
        (* Introduces variables for the states *)
        let s1, b1, s2, b2, e2 = push_two_fresh_vars e0 "__s" state_type in
        e2, ([v], brs), ([s1], [b1]), ([s1; v; s2], [b1; b2])
      | Some PP_Unknown ->
        (* Introduce variables for all the values, for the pre and the post *)
        let pre_values, pre_binders, e1 = introduce_variables_for_opt_abs e0 info.pre in
        let post_values, post_binders, e2 = introduce_variables_for_opt_abs e1 info.post in
        e2, ([v], brs), (pre_values, pre_binders), (post_values, post_binders)
      | _ ->
        (* No pre and no post *)
        e0, ([v], brs), ([], []), ([], [])
      end
  in
  (* Generate the propositions: *)
  (* - from the parameters' cast info *)
  let params_props = cast_info_list_to_propositions info.parameters in
  (* - from the precondition *)
  let pre_prop = opt_term_to_opt_proposition info.pre pre_values pre_binders in
  (* - from the return type *)
  let ret_refin_prop = opt_term_to_opt_proposition (get_opt_refinment info.ret_type) ret_values ret_binders in
  (* - from the postcondition *)
  let post_prop = opt_term_to_opt_proposition info.post post_values post_binders in
  (* Concatenate, revert and return *)
  let pres = List.Tot.rev (opt_cons pre_prop params_props) in
  let posts = opt_cons ret_refin_prop (opt_cons post_prop []) in
  e', { pres = pres; posts = posts }

(**** Step 3 *)
/// Simplify the propositions and filter the trivial ones.

/// Check if a proposition is trivial (i.e.: is True)
val is_trivial_proposition : proposition -> Tac bool

let is_trivial_proposition p =
  term_eq (`Prims.l_True) p.prop

let simp_filter_proposition (e:env) (steps:list norm_step) (p:proposition) :
  Tac (list proposition) =
  let prop1 = norm_term_env e steps p.prop in
  (* If trivial, filter *)
  if term_eq (`Prims.l_True) prop1 then []
  else
    (* Otherwise reinsert the abstracted parameters *)
    let prop2 = mk_abs prop1 p.abs in
    let prop3 = mk_e_app prop2 ((map (fun b -> pack (Tv_Var (bv_of_binder b)))) p.abs) in
    [{ p with prop = prop3 }]

let simp_filter_propositions (e:env) (steps:list norm_step) (pl:list proposition) :
  Tac (list proposition) =
  List.flatten (map (simp_filter_proposition e steps) pl)

let simp_filter_assertions (e:env) (steps:list norm_step) (a:assertions) :
  Tac assertions =
  let pres = simp_filter_propositions e steps a.pres in
  let posts = simp_filter_propositions e steps a.posts in
  mk_assertions pres posts

(**** Step 4 *)
/// Output the resulting information
/// Originally: we output the ``eterm_info`` and let the emacs commands do some
/// filtering and formatting. Now, we convert ``eterm_info`` to a ``assertions``.

let printout_string (prefix data:string) : Tac unit =
  (* Export all at once - actually I'm not sure it is not possible for external
   * output to be mixed here *)
  print (prefix ^ ":\n" ^ data ^ "\n")

let printout_term (prefix:string) (t:term) : Tac unit =
  printout_string prefix (term_to_string t)

let printout_opt_term (prefix:string) (t:option term) : Tac unit =
  match t with
  | Some t' -> printout_term prefix t'
  | None -> printout_string prefix ""

let printout_proposition (prefix:string) (p:proposition) : Tac unit =
  printout_term prefix p.prop

let printout_propositions (prefix:string) (pl:list proposition) : Tac unit =
  let print_prop i p =
    let prefix' = prefix ^ ":prop" ^ string_of_int i in
    printout_proposition prefix' p
  in
  printout_string (prefix ^ ":num") (string_of_int (List.Tot.length pl));
  iteri print_prop pl

let printout_assertions (prefix:string) (a:assertions) : Tac unit =
  print (prefix ^ ":BEGIN");
  printout_propositions (prefix ^ ":pres") a.pres;
  printout_propositions (prefix ^ ":posts") a.posts;
  print (prefix ^ ":END")

let _debug_print_var (name : string) (t : term) : Tac unit =
  print ("_debug_print_var: " ^ name ^ ": " ^ term_to_string t);
  begin match safe_tc (top_env ()) t with
  | Some ty -> print ("type: " ^ term_to_string ty)
  | _ -> ()
  end;
  print ("qualifier: " ^ term_construct t);
  begin match inspect t with
  | Tv_Var bv ->
    let b : bv_view = inspect_bv bv in
    print ("Tv_Var: ppname: " ^ b.bv_ppname ^
           "; index: " ^ (string_of_int b.bv_index) ^
           "; sort: " ^ term_to_string b.bv_sort)
  | _ -> ()
  end;
  print "end of _debug_print_var"

/// We use the following to solve goals requiring a unification variable (for
/// which we might not have a candidate, or for which the candidate may not
/// typecheck correctly). We can't use the tactic ``tadmit`` for the simple
/// reason that it generates a warning which may mess up with the subsequent
/// parsing of the data generated by the tactics.
assume val magic_witness (#a : Type) : a

let tadmit_no_warning () : Tac unit =
  apply (`magic_witness)

let pp_tac () : Tac unit =
  print ("post-processing: " ^ (term_to_string (cur_goal ())));
  dump "";
  trefl()

let test0 () : Lemma(3 >= 2) =
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

#push-options "--ifuel 1"
let print_binder_info (full : bool) (b : binder) : Tac unit =
  let bv, a = inspect_binder b in
  let a_str = match a with
    | Q_Implicit -> "Implicit"
    | Q_Explicit -> "Explicit"
    | Q_Meta t -> "Meta: " ^ term_to_string t
  in
  let bview = inspect_bv bv in
  if full then
    print (
      "> print_binder_info:" ^
      "\n- name: " ^ (name_of_binder b) ^
      "\n- as string: " ^ (binder_to_string b) ^
      "\n- aqual: " ^ a_str ^
      "\n- ppname: " ^ bview.bv_ppname ^
      "\n- index: " ^ string_of_int bview.bv_index ^
      "\n- sort: " ^ term_to_string bview.bv_sort
    )
  else print (binder_to_string b)

let print_binders_info (full : bool) (e:env) : Tac unit =
  iter (print_binder_info full) (binders_of_env e)

(*** Alternative: post-processing *)

/// We declare some identifiers that we will use to guide the meta processing
assume type meta_info
assume val focus_on_term : meta_info

/// A map linking variables to terms. For now we use a list to define it, because
/// there shouldn't be too many bindings.
type bind_map = list (bv & term)

let bind_map_push (b:bv) (t:term) (m:bind_map) = (b,t)::m

let rec bind_map_get (b:bv) (m:bind_map) : Tot (option term) =
  match m with
  | [] -> None
  | (b',t)::m' ->
    if compare_bv b b' = Order.Eq then Some t else bind_map_get b m'

let rec bind_map_get_from_name (b:string) (m:bind_map) : Tot (option (bv & term)) =
  match m with
  | [] -> None
  | (b',t)::m' ->
    let b'v = inspect_bv b' in
    if b'v.bv_ppname = b then Some (b',t) else bind_map_get_from_name b m'

noeq type genv =
  {
    env : env;
    bmap : bind_map;
  }
let get_env (e:genv) : env = e.env
let get_bind_map (e:genv) : bind_map = e.bmap
let mk_genv env bmap : genv =
  Mkgenv env bmap

/// Push a binder to a ``genv``. Optionally takes a ``term`` which provides the
/// term the binder is bound to (in a `let _ = _ in` construct for example).
let genv_push_bv (b:bv) (t:option term) (e:genv) : Tac genv =
  match t with
  | Some t' ->
    let br = mk_binder b in
    let e' = push_binder e.env br in
    let bmap' = bind_map_push b t' e.bmap in
    mk_genv e' bmap'
  | None ->
    let br = mk_binder b in
    let e' = push_binder e.env br in
    let bmap' = bind_map_push b (pack (Tv_Var b)) e.bmap in
    mk_genv e' bmap'

let genv_push_binder (b:binder) (t:option term) (e:genv) : Tac genv =
  match t with
  | Some t' ->
    let e' = push_binder e.env b in
    let bmap' = bind_map_push (bv_of_binder b) t' e.bmap in
    mk_genv e' bmap'
  | None ->
    let e' = push_binder e.env b in
    let bv = bv_of_binder b in
    let bmap' = bind_map_push bv (pack (Tv_Var bv)) e.bmap in
    mk_genv e' bmap'

let convert_ctrl_flag (flag : ctrl_flag) =
  match flag with
  | Continue -> Continue
  | Skip -> Continue
  | Abort -> Abort

/// TODO: for now I need to use universe 0 for type a because otherwise it doesn't
/// type check
/// ctrl_flag:
/// - Continue: continue exploring the term
/// - Skip: don't explore the sub-terms of this term
/// - Abort: stop exploration
val explore_term (dbg : bool)
                 (#a : Type0) (f : a -> genv -> term_view -> Tac (a & ctrl_flag))
                 (x : a) (ge:genv) (t:term) :
  Tac (a & ctrl_flag)

val explore_pattern (dbg : bool)
                    (#a : Type0) (f : a -> genv -> term_view -> Tac (a & ctrl_flag))
                    (x : a) (ge:genv) (pat:pattern) :
  Tac (genv & a & ctrl_flag)

(* TODO: carry around the list of encompassing terms *)
let rec explore_term dbg #a f x ge t =
  if dbg then
    begin
    print ("[> explore_term: " ^ term_construct t ^ ":\n" ^ term_to_string t)
    end;
  let tv = inspect t in
  let x', flag = f x ge tv in
  if flag = Continue then
    begin match tv with
    | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> x', Continue
    | Tv_App hd (a,qual) ->
      let x', flag' = explore_term dbg f x ge a in
      if flag' = Continue then
        explore_term dbg f x' ge hd
      else x', convert_ctrl_flag flag'
    | Tv_Abs br body ->
      (* We first explore the type of the binder - the user might want to
       * check information inside the binder definition *)
      let bv = bv_of_binder br in
      let bvv = inspect_bv bv in
      let x', flag' = explore_term dbg f x ge bvv.bv_sort in
      if flag' = Continue then
        let ge' = genv_push_binder br None ge in
        explore_term dbg f x' ge' body
      else x', convert_ctrl_flag flag'
    | Tv_Arrow br c -> x, Continue (* TODO: we might want to explore that *)
    | Tv_Type () -> x, Continue
    | Tv_Refine bv ref ->
      let bvv = inspect_bv bv in
      let x', flag' = explore_term dbg f x ge bvv.bv_sort in
      if flag' = Continue then
        let ge' = genv_push_bv bv None ge in
        explore_term dbg f x' ge' ref
      else x', convert_ctrl_flag flag'
    | Tv_Const _ -> x, Continue
    | Tv_Uvar _ _ -> x, Continue
    | Tv_Let recf attrs bv def body ->
      let bvv = inspect_bv bv in
      (* Explore the binding type *)
      let x', flag' = explore_term dbg f x ge bvv.bv_sort in
      if flag' = Continue then
        (* Explore the binding definition *)
        let x'', flag'' = explore_term dbg f x' ge def in
        if flag'' = Continue then
          (* Explore the next subterm *)
          let ge' = genv_push_bv bv (Some def) ge in
          explore_term dbg f x ge' body
        else x'', convert_ctrl_flag flag''
      else x', convert_ctrl_flag flag'
    | Tv_Match scrutinee branches ->
      let explore_branch (x_flag : a & ctrl_flag) (br : branch) : Tac (a & ctrl_flag)=
        let x, flag = x_flag in
        if flag = Continue then
          let pat, branch_body = br in
          (* Explore the pattern *)
          let ge', x', flag' = explore_pattern dbg #a f x ge pat in
          if flag' = Continue then
            (* Explore the branch body *)
            explore_term dbg #a f x' ge' branch_body
          else x', convert_ctrl_flag flag'
        (* Don't convert the flag *)
        else x, flag
      in
      let x' = explore_term dbg #a f x ge scrutinee in
      fold_left explore_branch x' branches
    | Tv_AscribedT e ty tac ->
      let x', flag = explore_term dbg #a f x ge e in
      if flag = Continue then
        explore_term dbg #a f x' ge ty
      else x', convert_ctrl_flag flag
    | Tv_AscribedC e c tac ->
      (* TODO: explore the comp *)
      explore_term dbg #a f x ge e
    | _ ->
      (* Unknown *)
      x, Continue
    end
  else x', convert_ctrl_flag flag

and explore_pattern dbg #a f x ge pat =
  match pat with
  | Pat_Constant _ -> ge, x, Continue
  | Pat_Cons fv patterns ->
    let explore_pat ge_x_flag pat =
      let ge, x, flag = ge_x_flag in
      let pat', _ = pat in
      if flag = Continue then
        explore_pattern dbg #a f x ge pat'
      else
        (* Don't convert the flag *)
        ge, x, flag
    in
    fold_left explore_pat (ge, x, Continue) patterns
  | Pat_Var bv | Pat_Wild bv ->
    let ge' = genv_push_bv bv None ge in
    ge', x, Continue
  | Pat_Dot_Term bv t ->
    (* TODO: I'm not sure what this is *)
    let ge' = genv_push_bv bv None ge in
    ge', x, Continue

let print_dbg (debug : bool) (s : string) : Tac unit =
  if debug then print s

let pp_explore (dbg : bool)
               (#a : Type0) (f : a -> genv -> term_view -> Tac (a & ctrl_flag))
               (x : a) :
  Tac unit =
  print "[> pp_explore";
  let g = cur_goal () in
  let e = cur_env () in
  begin match term_as_formula g with
  | Comp (Eq _) l r ->
    let ge = mk_genv e [] in
    let x = explore_term dbg #a f x ge l in
    trefl()
  | _ -> mfail "pp_explore: not a squashed equality"
  end

/// Effectful term analysis: analyze a term in order to print propertly instantiated
/// pre/postconditions and type conditions.

/// Check for meta-identifiers. Note that we can't simply use ``term_eq`` which
/// sometimes unexpectedly fails (maybe because of information hidden to Meta-F*).
val is_focus_on_term : term -> Tac bool
let is_focus_on_term t =
  match inspect t with
  | Tv_FVar fv ->
    if flatten_name (inspect_fv fv) = `%PrintTactics.focus_on_term then true else false
  | _ -> false

val analyze_effectful_term : bool -> unit -> genv -> term_view -> Tac (unit & ctrl_flag)

let analyze_effectful_term dbg () ge t =
  if dbg then
    begin
    print ("[> analyze_effectful_term: " ^ term_view_construct t ^ ":\n" ^ term_to_string t)
    end;
  match t with
  | Tv_Let recf attrs bv def body ->
    (* We need to check if the let definition is a meta identifier *)
       if is_focus_on_term def then
       begin
       print ("[> Focus on term: " ^ term_to_string body);
       print ("[> Environment information: ");
       print_binders_info false ge.env;
       (* Start by analyzing the effectful term and checking whether it is
        * a 'let' or not *)
       let ge1, info, ret_arg, is_let =
         begin match inspect body with
         | Tv_Let _ _ fbv fterm _ ->
           let ret_arg = pack (Tv_Var fbv) in
           genv_push_bv fbv None ge, get_eterm_info ge.env fterm, Some ret_arg, true
         | _ -> ge, get_eterm_info ge.env body, None, true
         end
       in
       (* Instantiate the refinements *)
       let e2, asserts = eterm_info_to_assertions ge1.env info ret_arg in
       (* Simplify and filter *)
       let sasserts = simp_filter_assertions e2 [primops; simplify] asserts in
       (* Print *)
       printout_assertions "ainfo" sasserts;
       (), Abort
       end
     else (), Continue
  | _ -> (), Continue

val pp_focused_term : bool -> unit -> Tac unit
let pp_focused_term dbg () =
  pp_explore dbg (analyze_effectful_term dbg) ()

(*** Tests *)
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
let pp_test2 () : Tot nat =
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
let pp_test4 () :
  ST.Stack nat
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> 3 >= 2)) =
  let x = 2 in
  let _ = focus_on_term in
  let w = test_stack1 x in
  w



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
  run_tactic (fun _ -> print_binders_info true)

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

//binders_of_env
//lookup_typ
//lookup_attr
//all_defs_in_env  


//[@(postprocess_with pp_tac)]
let test8 (x : nat{x >= 4}) (y : int{y >= 10}) (z : nat{z >= 12}) :
  Tot (n:nat{n % 2 = 0}) =
//  run_tactic (fun _ -> print (term_to_string (quote ((**) x))));
  let a = 3 in
//  FStar.Tactics.Derived.run_tactic (fun _ -> PrintTactics.dprint_eterm (quote (test_lemma1 x)) None (`()) [(`())]);
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

//  run_tactic (fun _ -> dprint_eterm (quote (test_fun4 x)) (Some "w") (quote w) [(`())]);
//  run_tactic (fun _ -> dprint_eterm (quote (test_fun6 x (2 * x) (3 * x))) (Some "a") (quote y) [(`())]);
//  run_tactic (fun _ -> dprint_eterm (quote (test_fun6 x y z)) (Some "a") (quote y) [(`())]);

(*
   (setq debug-on-error t)

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

  x = 3;

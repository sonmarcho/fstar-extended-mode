module FEM.Process

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul

/// TODO: when an F* meta function fails for a known reason, it is better to fail
/// silently but output a message which will be displayed by the user, so that he
/// knows what's going on (for example: "can't unfold (x + y)")

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

val tryPick: ('a -> Tac (option 'b)) -> list 'a -> Tac (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(* TODO: move to FStar.Tactics.Derived.fst *)
let rec mk_abs (t : term) (args : list binder) : Tac term (decreases args) =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = mk_abs t args' in
    pack (Tv_Abs a t')

val bv_eq : bv -> bv -> Tot bool
let bv_eq (bv1 bv2 : bv) =
  let bvv1 = inspect_bv bv1 in
  let bvv2 = inspect_bv bv2 in
  (* We don't check for type equality: the fact that no two different binders
   * have the same name and index is an invariant which must be enforced *)
  bvv1.bv_ppname = bvv2.bv_ppname && bvv1.bv_index = bvv2.bv_index

val name_eq : name -> name -> Tot bool
let rec name_eq n1 n2 =
  match n1, n2 with
  | [], [] -> true
  | x1::n1', x2::n2' ->
    x1 = x2 && name_eq n1' n2'
  | _ -> false

val fv_eq : fv -> fv -> Tot bool
let fv_eq fv1 fv2 =
  let n1 = inspect_fv fv1 in
  let n2 = inspect_fv fv2 in
  name_eq n1 n2

// TODO: use everywhere
val fv_eq_name : fv -> name -> Tot bool
let fv_eq_name fv n =
  let fvn = inspect_fv fv in
  name_eq fvn n

(*** General utilities *)
// TODO: use more
val opt_apply (#a #b : Type) (f : a -> Tot b) (x : option a) : Tot (option b)
let opt_apply #a #b f x =
  match x with
  | None -> None
  | Some x' -> Some (f x')

val opt_tapply (#a #b : Type) (f : a -> Tac b) (x : option a) : Tac (option b)
let opt_tapply #a #b f x =
  match x with
  | None -> None
  | Some x' -> Some (f x')

/// Some debugging facilities
val print_dbg : bool -> string -> Tac unit
let print_dbg debug s =
  if debug then print s

val option_to_string : (#a : Type) -> (a -> Tot string) -> option a -> Tot string
let option_to_string #a f x =
  match x with
  | None -> "None"
  | Some x' -> "Some (" ^ f x' ^ ")"

val list_to_string : #a : Type -> (a -> Tot string) -> list a -> Tot string
let list_to_string #a f ls =
  (List.Tot.fold_left (fun s x -> s ^ " (" ^ f x ^ ");") "[" ls) ^ "]"

/// Alternative ``bv_to_string`` function where we print the index of the bv.
/// It can be very useful for debugging.
let abv_to_string bv : Tot string =
  let bvv = inspect_bv bv in
  bvv.bv_ppname ^ " (%" ^ string_of_int (bvv.bv_index) ^ ") : " ^
  term_to_string bvv.bv_sort

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

let acomp_to_string (c:comp) : Tot string =
  match inspect_comp c with
  | C_Total ret decr ->
    "C_Total (" ^ term_to_string ret
  | C_GTotal ret decr ->
    "C_GTotal (" ^ term_to_string ret
  | C_Lemma pre post patterns ->
    "C_Lemma (" ^ term_to_string pre ^ ") (" ^ term_to_string post ^ ")"
  | C_Eff us eff_name result eff_args ->
    let eff_arg_to_string (a : term) : Tot string =
      " (" ^ term_to_string a ^ ")"
    in
    let args_str = List.Tot.map (fun (x, y) -> eff_arg_to_string x) eff_args in
    let args_str = List.Tot.fold_left (fun x y -> x ^ y) "" args_str in
    "C_Eff (" ^ flatten_name eff_name ^ ") (" ^ term_to_string result ^ ")" ^ args_str

exception MetaAnalysis of string
let mfail str =
  raise (MetaAnalysis str)

/// A map linking variables to terms. For now we use a list to define it, because
/// there shouldn't be too many bindings.
type bind_map (a : Type) = list (bv & a)

let bind_map_push (#a:Type) (m:bind_map a) (b:bv) (x:a) = (b,x)::m

let rec bind_map_get (#a:Type) (m:bind_map a) (b:bv) : Tot (option a) =
  match m with
  | [] -> None
  | (b', x)::m' ->
    if compare_bv b b' = Order.Eq then Some x else bind_map_get m' b

let rec bind_map_get_from_name (#a:Type) (m:bind_map a) (name:string) :
  Tot (option (bv & a)) =
  match m with
  | [] -> None
  | (b', x)::m' ->
    let b'v = inspect_bv b' in
    if b'v.bv_ppname = name then Some (b', x) else bind_map_get_from_name m' name

noeq type genv =
{
  env : env;
  (* Whenever we evaluate a let binding, we keep track of the relation between
   * the binder and its definition.
   * The boolean indicates whether or not the variable is considered abstract. We
   * often need to introduce variables which don't appear in the user context, for
   * example when we need to deal with a postcondition for Stack or ST, which handles
   * the previous and new memory states, and which may not be available in the user
   * context, or where we don't always know which variable to use.
   * In this case, whenever we output the term, we write its content as an
   * asbtraction applied to those missing parameters. For instance, in the
   * case of the assertion introduced for a post-condition:
   * [> assert((fun h1 h2 -> post) h1 h2);
   * Besides the informative goal, the user can replace those parameters (h1
   * and h2 above) by the proper ones then normalize the assertion by using
   * the appropriate command to get a valid assertion. *)
  bmap : bind_map (bool & term);
  (* Whenever we introduce a new variable, we check whether it shadows another
   * variable because it has the same name, and put it in the below
   * list. Of course, for the F* internals such shadowing is not an issue, because
   * the index of every variable should be different, but this is very important
   * when generating code for the user *)
  svars : list bv;
}

let get_env (e:genv) : env = e.env
let get_bind_map (e:genv) : bind_map (bool & term) = e.bmap
let mk_genv env bmap svars : genv = Mkgenv env bmap svars
let mk_init_genv env : genv = mk_genv env [] []

val genv_to_string : genv -> Tot string
let genv_to_string ge =
  let binder_to_string (b : binder) : Tot string =
    abv_to_string (bv_of_binder b) ^ "\n"
  in
  let binders_str = List.Tot.map binder_to_string (binders_of_env ge.env) in
  let bmap_elem_to_string (e : bv & (bool & term)) : Tot string =
    let bv, (abs, t) = e in
    "(" ^ abv_to_string bv ^" -> (" ^
    string_of_bool abs ^ ", " ^ term_to_string t ^ "))\n"
  in
  let bmap_str = List.Tot.map bmap_elem_to_string ge.bmap in
  let svars_str = List.Tot.map (fun bv -> abv_to_string bv ^ "\n") ge.svars in
  let flatten = List.Tot.fold_left (fun x y -> x ^ y) "" in
  "> env:\n" ^ flatten binders_str ^
  "> bmap:\n" ^ flatten bmap_str ^
  "> svars:\n" ^ flatten svars_str

let genv_get (ge:genv) (b:bv) : Tot (option (bool & term)) =
  bind_map_get ge.bmap b

let genv_get_from_name (ge:genv) (name:string) : Tot (option (bv & (bool & term))) =
  bind_map_get_from_name ge.bmap name

/// Push a binder to a ``genv``. Optionally takes a ``term`` which provides the
/// term the binder is bound to (in a `let _ = _ in` construct for example).
let genv_push_bv (ge:genv) (b:bv) (abs:bool) (t:option term) : Tac genv =
  let br = mk_binder b in
  let sv = genv_get_from_name ge (name_of_bv b) in
  let svars' = if Some? sv then fst (Some?.v sv) :: ge.svars else ge.svars in
  let e' = push_binder ge.env br in
  let tm = if Some? t then Some?.v t else pack (Tv_Var b) in
  let bmap' = bind_map_push ge.bmap b (abs, tm) in
  mk_genv e' bmap' svars'

let genv_push_binder (ge:genv) (b:binder) (abs:bool) (t:option term) : Tac genv =
  genv_push_bv ge (bv_of_binder b) abs t

/// Check if a binder is shadowed by another more recent binder
let bv_is_shadowed (ge : genv) (bv : bv) : Tot bool =
  List.Tot.existsb (bv_eq bv) ge.svars

let binder_is_shadowed (ge : genv) (b : binder) : Tot bool =
  bv_is_shadowed ge (bv_of_binder b)

let find_shadowed_bvs (ge : genv) (bl : list bv) : Tot (list (bv & bool)) =
  List.Tot.map (fun b -> b, bv_is_shadowed ge b) bl

let find_shadowed_binders (ge : genv) (bl : list binder) : Tot (list (binder & bool)) =
  List.Tot.map (fun b -> b, binder_is_shadowed ge b) bl

val bv_is_abstract : genv -> bv -> Tot bool
let bv_is_abstract ge bv =
  match genv_get ge bv with
  | None -> false
  | Some (abs, _) -> abs

val binder_is_abstract : genv -> binder -> Tot bool
let binder_is_abstract ge b =
  bv_is_abstract ge (bv_of_binder b)

val genv_abstract_bvs : genv -> Tot (list bv)
let genv_abstract_bvs ge =
  let abs = List.Tot.filter (fun (_, (abs, _)) -> abs) ge.bmap in
  List.Tot.map (fun (bv, _) -> bv) abs

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

let genv_push_fresh_binder (ge : genv) (basename : string) (ty : typ) : Tac (genv & binder) =
  let b = fresh_binder ge.env basename ty in
  (* TODO: we can have a shortcircuit push (which performs less checks) *)
  let ge' = genv_push_binder ge b true None in
  ge', b

// TODO: actually we should use push_fresh_bv more
let push_fresh_binder (e : env) (basename : string) (ty : typ) : Tac (env & binder) =
  let b = fresh_binder e basename ty in
  let e' = push_binder e b in
  e', b

let genv_push_fresh_bv (ge : genv) (basename : string) (ty : typ) : Tac (genv & bv) =
  let ge', b = genv_push_fresh_binder ge basename ty in
  ge', bv_of_binder b

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

val effect_type_is_pure : effect_type -> Tot bool
let effect_type_is_pure etype =
  match etype with
  | E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure -> true
  | E_Stack | E_ST | E_Unknown -> false

/// Type information
noeq type type_info = {
  ty : typ; (* the type without refinement *)
  refin : option term;
}

let mk_type_info = Mktype_info

val type_info_to_string : type_info -> Tot string
let type_info_to_string info =
  "Mktype_info (" ^
  term_to_string info.ty ^ ") (" ^
  option_to_string term_to_string info.refin ^ ")"

let unit_type_info = mk_type_info (`unit) None

val safe_tc (e:env) (t:term) : Tac (option term)
let safe_tc e t =
  try Some (tc e t) with | _ -> None

val safe_tcc (e:env) (t:term) : Tac (option comp)
let safe_tcc e t =
  try Some (tcc e t) with | _ -> None

let get_type_info_from_type (ty:typ) : Tac type_info =
  match inspect ty with
  | Tv_Refine bv refin ->
    let bview : bv_view = inspect_bv bv in
    let raw_type : typ = bview.bv_sort in
    let b : binder = mk_binder bv in
    let refin = pack (Tv_Abs b refin) in
    mk_type_info raw_type (Some refin)
  | _ -> mk_type_info ty None

#push-options "--ifuel 1"
let get_type_info (e:env) (t:term) : Tac (option type_info) =
  match safe_tc e t with
  | None -> None
  | Some ty -> Some (get_type_info_from_type ty)
#pop-options

val get_total_or_gtotal_ret_type : comp -> Tot (option typ)
let get_total_or_gtotal_ret_type c =
  match inspect_comp c with
  | C_Total ret_ty _ | C_GTotal ret_ty _ -> Some ret_ty
  | _ -> None

val get_comp_ret_type : comp -> Tot typ
let get_comp_ret_type c =
  match inspect_comp c with
  | C_Total ret_ty _ | C_GTotal ret_ty _
  | C_Eff _ _ ret_ty _ -> ret_ty
  | C_Lemma _ _ _ -> (`unit)

val is_total_or_gtotal : comp -> Tot bool
let is_total_or_gtotal c =
  Some? (get_total_or_gtotal_ret_type c)


/// This type is used to store typing information.
/// We use it mostly to track what the target type/computation type is for
/// a term being explored. It is especially useful to generate post-conditions,
/// for example.
/// Whenever we go inside an abstraction, we store how  we instantiated the outer
/// lambda (in an order reverse to the instantiation order), so that we can correctly
/// instantiate the pre/post-conditions and type refinements.
// TODO: actually we only need to carry a comp (if typ: consider it total)
noeq type typ_or_comp =
| TC_Typ : v:typ -> m:list (bv & bv) -> typ_or_comp
| TC_Comp : v:comp -> m:list (bv & bv) -> typ_or_comp

/// Compute a ``typ_or_comp`` from the type of a term
val safe_typ_or_comp : bool -> env -> term ->
                       Tac (opt:option typ_or_comp{Some? opt ==> TC_Comp? (Some?.v opt)})
let safe_typ_or_comp dbg e t =
  match safe_tcc e t with
  | None ->
    print_dbg dbg ("[> safe_typ_or_comp:" ^
                   "\n-term: " ^ term_to_string t ^
                   "\n-comp: None");
    None
  | Some c ->
    print_dbg dbg ("[> safe_typ_or_comp:" ^
                   "\n-term: " ^ term_to_string t ^
                   "\n-comp: " ^ acomp_to_string c);
    Some (TC_Comp c [])

/// Update the current ``typ_or_comp`` before going into the body of an abstraction
/// Any new binder needs to be added to the current environment (otherwise we can't,
/// for example, normalize the terms containing the binding), hence the ``env``
/// parameter, which otherwise is useless (consider like as a monadic state). Note
/// that we don't add this binder to a more general environment, because we don't
/// need it besides that.
val abs_update_typ_or_comp : binder -> typ_or_comp -> env -> Tac (env & typ_or_comp)
let _abs_update_typ (b:binder) (ty:typ) (m:list (bv & bv)) (e:env) :
  Tac (env & typ_or_comp) =
  begin match inspect ty with
  | Tv_Arrow b1 c1 ->
    push_binder e b1, TC_Comp c1 ((bv_of_binder b1, bv_of_binder b) :: m)
  | _ -> mfail ("abs_update_typ_or_comp: not an arrow: " ^ term_to_string ty)
  end

let abs_update_typ_or_comp (b:binder) (c : typ_or_comp) (e:env) : Tac (env & typ_or_comp) =
  match c with
  | TC_Typ v m -> _abs_update_typ b v m e
  | TC_Comp v m ->
    (* Note that the computation is not necessarily pure, in which case we might
     * want to do something with the effect arguments (pre, post...) - for
     * now we just ignore them *)
    let ty = get_comp_ret_type v in
    _abs_update_typ b ty m e

val abs_update_opt_typ_or_comp : binder -> option typ_or_comp -> env ->
                                 Tac (env & option typ_or_comp)
let abs_update_opt_typ_or_comp b opt_c e =
  match opt_c with
  | None -> e, None
  | Some c ->
    let e, c = abs_update_typ_or_comp b c e in
    e, Some c

/// Exploring a term

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
/// TODO: we might want a more precise control (like: don't explore the type of the
/// ascription but explore its body)
/// Note that ``explore_term`` doesn't use the environment parameter besides pushing
/// binders and passing it to ``f``, which means that you can give it arbitrary
/// environments, ``explore_term`` itself won't fail (but the passed function might).

let explorer (a : Type) =
  a -> genv -> list (genv & term_view) -> option typ_or_comp -> term_view ->
  Tac (a & ctrl_flag)

// TODO: use more
let bind_expl (#a : Type) (x : a) (f1 f2 : a -> Tac (a & ctrl_flag)) : Tac (a & ctrl_flag) =
  let x1, flag1 = f1 x in
  if flag1 = Continue then
    f2 x1
  else x1, convert_ctrl_flag flag1  

// TODO: change the signature to move the dbg flag
val explore_term :
     dbg : bool
  -> dfs : bool (* depth-first search *)
  -> #a : Type0
  -> f : explorer a
  -> x : a
  -> ge : genv
  (* the list of terms traversed so far (first is most recent) with the environment
   * at the time they were traversed *)
  -> parents : list (genv & term_view)
  -> c : option typ_or_comp
  -> t:term ->
  Tac (a & ctrl_flag)

val explore_pattern :
     dbg : bool
  -> dfs : bool (* depth-first search *)
  -> #a : Type0
  -> f : explorer a
  -> x : a
  -> ge:genv
  -> pat:pattern ->
  Tac (genv & a & ctrl_flag)

(* TODO: carry around the list of encompassing terms *)
let rec explore_term dbg dfs #a f x ge0 pl0 c0 t0 =
  if dbg then
    begin
    print ("[> explore_term: " ^ term_construct t0 ^ ":\n" ^ term_to_string t0)
    end;
  let tv0 = inspect t0 in
  let x0, flag = f x ge0 pl0 c0 tv0 in
  let pl1 = (ge0, tv0) :: pl0 in
  if flag = Continue then
    begin match tv0 with
    | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> x0, Continue
    | Tv_App hd (a,qual) ->
      (* Explore the argument - we update the target typ_or_comp when doing so *)
      let a_c = safe_typ_or_comp dbg ge0.env a in
      let x1, flag1 = explore_term dbg dfs f x0 ge0 pl1 a_c a in
      (* Explore the head - no type information here: we can compute it,
       * but it seems useless (or maybe use it only if it is not Total) *)
      if flag1 = Continue then
        explore_term dbg dfs f x1 ge0 pl1 None hd
      else x1, convert_ctrl_flag flag1
    | Tv_Abs br body ->
      let ge1 = genv_push_binder ge0 br false None in
      let e2, c1 = abs_update_opt_typ_or_comp br c0 ge1.env in
      let ge2 = { ge1 with env = e2 } in
      explore_term dbg dfs f x0 ge2 pl1 c1 body
    | Tv_Arrow br c0 -> x0, Continue (* TODO: we might want to explore that *)
    | Tv_Type () -> x0, Continue
    | Tv_Refine bv ref ->
      let bvv = inspect_bv bv in
      let x1, flag1 = explore_term dbg dfs f x0 ge0 pl1 None bvv.bv_sort in
      if flag1 = Continue then
        let ge1 = genv_push_bv ge0 bv false None in
        explore_term dbg dfs f x1 ge1 pl1 None ref
      else x1, convert_ctrl_flag flag1
    | Tv_Const _ -> x0, Continue
    | Tv_Uvar _ _ -> x0, Continue
    | Tv_Let recf attrs bv def body ->
      (* Binding definition exploration - for the target computation: initially we
       * used the type of the definition, however it is often unnecessarily complex.
       * Now, we use the type of the binder used for the binding. *)
      let def_c = Some (TC_Typ (type_of_bv bv) []) in
      let explore_def x = explore_term dbg dfs f x ge0 pl1 def_c def in
      (* Exploration of the following instructions *)
      let ge1 = genv_push_bv ge0 bv false (Some def) in
      let explore_next x = explore_term dbg dfs f x ge1 pl1 c0 body in
      (* Perform the exploration in the proper order *)
      let expl1, expl2 = if dfs then explore_next, explore_def else explore_def, explore_next in
      bind_expl x0 expl1 expl2
    | Tv_Match scrutinee branches ->
      (* Auxiliary function to explore the branches *)
      let explore_branch (x_flag : a & ctrl_flag) (br : branch) : Tac (a & ctrl_flag)=
        let x0, flag = x_flag in
        if flag = Continue then
          let pat, branch_body = br in
          (* Explore the pattern *)
          let ge1, x1, flag1 = explore_pattern dbg dfs #a f x0 ge0 pat in
          if flag1 = Continue then
            (* Explore the branch body *)
            explore_term dbg dfs #a f x1 ge1 pl1 c0 branch_body
          else x1, convert_ctrl_flag flag1
        (* Don't convert the flag *)
        else x0, flag
      in
      (* Explore the scrutinee *)
      let scrut_c = safe_typ_or_comp dbg ge0.env scrutinee in
      let x1 = explore_term dbg dfs #a f x0 ge0 pl1 scrut_c scrutinee in
      (* Explore the branches *)
      fold_left explore_branch x1 branches
    | Tv_AscribedT e ty tac ->
      let c1 = Some (TC_Typ ty []) in
      let x1, flag = explore_term dbg dfs #a f x0 ge0 pl1 None ty in
      if flag = Continue then
        explore_term dbg dfs #a f x1 ge0 pl1 c1 e
      else x1, convert_ctrl_flag flag
    | Tv_AscribedC e c1 tac ->
      (* TODO: explore the comp *)
      explore_term dbg dfs #a f x0 ge0 pl1 (Some (TC_Comp c1 [])) e
    | _ ->
      (* Unknown *)
      x0, Continue
    end
  else x0, convert_ctrl_flag flag

and explore_pattern dbg dfs #a f x ge0 pat =
  match pat with
  | Pat_Constant _ -> ge0, x, Continue
  | Pat_Cons fv patterns ->
    let explore_pat ge_x_flag pat =
      let ge0, x, flag = ge_x_flag in
      let pat1, _ = pat in
      if flag = Continue then
        explore_pattern dbg dfs #a f x ge0 pat1
      else
        (* Don't convert the flag *)
        ge0, x, flag
    in
    fold_left explore_pat (ge0, x, Continue) patterns
  | Pat_Var bv | Pat_Wild bv ->
    let ge1 = genv_push_bv ge0 bv false None in
    ge1, x, Continue
  | Pat_Dot_Term bv t ->
    (* TODO: I'm not sure what this is *)
    let ge1 = genv_push_bv ge0 bv false None in
    ge1, x, Continue

/// Returns the list of variables free in a term
val free_in : term -> Tac (list bv)
let free_in t =
  let same_name (bv1 bv2 : bv) : Tot bool =
    name_of_bv bv1 = name_of_bv bv2
  in
  let update_free (fl:list bv) (ge:genv) (pl:list (genv & term_view))
                  (c:option typ_or_comp) (tv:term_view) :
    Tac (list bv & ctrl_flag) =
    match tv with
    | Tv_Var bv | Tv_BVar bv ->
      let bvv = inspect_bv bv in
      (* Check if the binding was not introduced during the traversal *)
      begin match genv_get_from_name ge bvv.bv_ppname with
      | None ->
        (* Check if we didn't already count the binding *)
        let fl' = if Some? (List.Tot.tryFind (same_name bv) fl) then fl else bv :: fl in
        fl', Continue
      | Some _ -> fl, Continue
      end
    | _ -> fl, Continue
  in
  let e = top_env () in (* we actually don't care about the environment *)
  let ge = mk_genv e [] [] in
  List.Tot.rev (fst (explore_term false false update_free [] ge [] None t))

/// Returns the list of abstract variables appearing in a term, in the order in
/// which they were introduced in the context.
val abs_free_in : genv -> term -> Tac (list bv)
let abs_free_in ge t =
  let fvl = free_in t in
  let absl = List.rev (genv_abstract_bvs ge) in
  let is_free_in_term bv =
    Some? (List.Tot.find (bv_eq bv) fvl)
  in
  let absfree = List.Tot.filter is_free_in_term absl in
  absfree

(*** Simplification *)
/// Whenever we generate assertions, we simplify them to make them cleaner,
/// prettier and remove the trivial ones. The normalization steps we apply
/// are listed below.
let simpl_norm_steps = [primops; simplify]

(*** Effectful term analysis *)
/// Analyze a term to retrieve its effectful information

type proposition = term

val proposition_to_string : proposition -> Tot string
let proposition_to_string p = term_to_string p

/// Cast information
noeq type cast_info = {
  term : term;
  p_ty : option type_info; // The type of the term
  exp_ty : option type_info; // The type of the expected parameter
}

let mk_cast_info t p_ty exp_ty : cast_info =
  Mkcast_info t p_ty exp_ty

val cast_info_to_string : cast_info -> Tot string
let cast_info_to_string info =
  "Mkcast_info (" ^ term_to_string info.term ^ ") (" ^
  option_to_string type_info_to_string info.p_ty ^ ") (" ^
  option_to_string type_info_to_string info.exp_ty ^ ")"

/// Extracts the effectful information from a computation
noeq type effect_info = {
  ei_type : effect_type;
  ei_ret_type : type_info;
  ei_pre : option term;
  ei_post : option term;
}

let mk_effect_info = Mkeffect_info

/// Convert a ``typ_or_comp`` to cast information
val effect_info_to_string : effect_info -> Tot string
let effect_info_to_string c =
  "Mkeffect_info " ^
  effect_type_to_string c.ei_type ^ " (" ^
  option_to_string term_to_string c.ei_pre ^ ") (" ^
  type_info_to_string c.ei_ret_type ^ ") (" ^
  option_to_string term_to_string c.ei_post ^ ")"

/// Effectful term information
noeq type eterm_info = {
  einfo : effect_info;
  (* Head and parameters of the decomposition of the term into a function application *)
  head : term;
  parameters : list cast_info;
}

val eterm_info_to_string : eterm_info -> Tot string
let eterm_info_to_string info =
  let params = List.Tot.map (fun x -> "(" ^ cast_info_to_string x ^ ");  \n") info.parameters in
  let params_str = List.Tot.fold_left (fun x y -> x ^ y) "" params in
  "Mketerm_info (" ^
  effect_info_to_string info.einfo ^ ") (" ^
  term_to_string info.head ^ ")\n[" ^
  params_str ^ "]"

let mk_eterm_info = Mketerm_info


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
          Some (get_type_info_from_type ty)
        | _ -> None
    in
    let cast_info = mk_cast_info a a_type param_type in
    hd0, cast_info :: params
  | _ -> t, []
#pop-options

let decompose_application e t =
  let hd, params = decompose_application_aux e t in
  hd, List.Tot.rev params

/// Computes an effect type, its return type and its (optional) pre and post
val comp_view_to_effect_info : comp_view -> Tac (option effect_info)

let comp_view_to_effect_info cv =
  match cv with
  | C_Total ret_ty decr ->
    let ret_type_info = get_type_info_from_type ret_ty in
    Some (mk_effect_info E_Total ret_type_info None None)
  | C_GTotal ret_ty decr ->
    let ret_type_info = get_type_info_from_type ret_ty in
    Some (mk_effect_info E_Total ret_type_info None None)
  | C_Lemma pre post patterns ->
    (* We use unit as the return type information *)
    Some (mk_effect_info E_Lemma unit_type_info (Some pre) (Some post))
  | C_Eff univs eff_name ret_ty eff_args ->
    let ret_type_info = get_type_info_from_type ret_ty in
    let etype = effect_name_to_type eff_name in
    let mk_res = mk_effect_info etype ret_type_info in
    begin match etype, eff_args with
    | E_PURE, [(pre, _)] -> Some (mk_res (Some pre) None)
    | E_Pure, [(pre, _); (post, _)]
    | E_Stack, [(pre, _); (post, _)]
    | E_ST, [(pre, _); (post, _)] -> Some (mk_res (Some pre) (Some post))
    (* If the effect is unknown and there are two parameters or less, we make the
     * guess that the first one is a pre-condition and the second one is a
     * post-condition *)
    | E_Unknown, [] -> Some (mk_res None None)
    | E_Unknown, [(pre, _)] -> Some (mk_res (Some pre) None)
    | E_Unknown, [(pre, _); (post, _)] -> Some (mk_res (Some pre) (Some post))
    | _ -> None
    end

val comp_to_effect_info : comp -> Tac (option effect_info)

let comp_to_effect_info c =
  let cv : comp_view = inspect_comp c in
  comp_view_to_effect_info cv

val compute_effect_info : env -> term -> Tac (option effect_info)

let compute_effect_info e tm =
  match safe_tcc e tm with
  | Some c -> comp_to_effect_info c
  | None -> None

/// Returns the effectful information about a term
val compute_eterm_info : env -> term -> Tac eterm_info

#push-options "--ifuel 2"
let compute_eterm_info (e:env) (t : term) =
  (* Decompose the term if it is a function application *)
  let hd, parameters = decompose_application e t in
  try
    begin
    let c : comp = tcc e t in
    let opt_einfo = comp_to_effect_info c in
    match opt_einfo with
    | None -> mfail ("compute_eterm_info: failed on: " ^ term_to_string t)
    | Some einfo ->
      mk_eterm_info einfo hd parameters
    end
  with
  | TacticFailure msg ->
    mfail ("compute_eterm_info: failure: '" ^ msg ^ "'")
  | e -> raise e
#pop-options

(***** Types, casts and refinements *)

(* TODO: those are not needed anymore *)
let has_refinement (ty:type_info) : Tot bool =
  Some? ty.refin

let get_refinement (ty:type_info{Some? ty.refin}) : Tot term =
  Some?.v ty.refin

let get_opt_refinment (ty:type_info) : Tot (option term) =
  ty.refin

let get_rawest_type (ty:type_info) : Tot typ =
  ty.ty

/// Compare the type of a parameter and its expected type
type type_comparison = | Refines | Same_raw_type | Unknown

#push-options "--ifuel 1"
let type_comparison_to_string c =
  match c with
  | Refines -> "Refines"
  | Same_raw_type -> "Same_raw_type"
  | Unknown -> "Unknown"
#pop-options

// TODO: without debugging information generation, is Tot
let compare_types (dbg : bool) (info1 info2 : type_info) :
  Tac (c:type_comparison{c = Same_raw_type ==> has_refinement info2}) =
  print_dbg dbg "[> compare_types";
  if term_eq info1.ty info2.ty then
      let _ = print_dbg dbg "-> types are equal" in
      if has_refinement info2 then
        let _ = print_dbg dbg "-> 2nd type has refinement" in
        // This doesn't work like in C: we need to check if info1 has a
        // refinement, then we can compare the refinements inside ANOTHER if
        if has_refinement info1 then
          let _ = print_dbg dbg "-> 1st type has refinement" in
          if term_eq (get_refinement info1) (get_refinement info2) then
            let _ = print_dbg dbg "-> Refines" in
            Refines
          else
          let _ = print_dbg dbg "-> Same_raw_type" in
          Same_raw_type // Same raw type but can't say anything about the expected refinement
        else
          let _ = print_dbg dbg "-> 1st type has no refinement" in
          let _ = print_dbg dbg "-> Same_raw_type" in
          Same_raw_type // Same raw type but can't say anything about the expected refinement
      else
        let _ = print_dbg dbg "-> 2nd type has no refinement: Refines" in
        Refines // The first type is more precise than the second type
    else
      let _ = print_dbg dbg "types are not equal" in
      Unknown

let compare_cast_types (dbg : bool) (p:cast_info) :
  Tac (c:type_comparison{
    ((c = Refines \/ c = Same_raw_type) ==> (Some? p.p_ty /\ Some? p.exp_ty)) /\
    (c = Same_raw_type ==> has_refinement (Some?.v p.exp_ty))}) =
  print_dbg dbg "[> compare_cast_types";
  match p.p_ty, p.exp_ty with
  | Some info1, Some info2 ->
    compare_types dbg info1 info2
  | _ -> Unknown

let opt_cons (#a : Type) (opt_x : option a) (ls : list a) : Tot (list a) =
  match opt_x with
  | Some x -> x :: ls
  | None -> ls

/// Apply a term to a list of parameters, normalize the result to make sure
/// any abstractions are evaluated
val mk_app_norm : genv -> term -> list term -> Tac term
let mk_app_norm ge t params =
  let t1 = mk_e_app t params in
  let t2 = norm_term_env ge.env [] t1 in
  t2

val opt_mk_app_norm : genv -> option term -> list term -> Tac (option term)
let opt_mk_app_norm ge opt_t params =
  opt_tapply (fun t -> mk_app_norm ge t params) opt_t

// TODO: remove
let rec unzip #a #b (l : list (a & b)) : Tot (list a & list b) =
  match l with
  | [] -> ([],[])
  | (hd1,hd2)::tl ->
       let (tl1,tl2) = unzip tl in
       (hd1::tl1,hd2::tl2)

/// Perform a variable substitution in a term
val apply_subst : env -> term -> list (bv & term) -> Tac term
let apply_subst e t subst =
  let bl, vl = unzip subst in
  let bl = List.Tot.map mk_binder bl in
  let t1 = mk_abs t bl in
  let t2 = mk_e_app t1 vl in
  norm_term_env e [] t2

/// Introduce fresh variables to generate a substitution for the variables shadowed
/// in the current environment.
val generate_shadowed_subst : genv -> Tac (genv & list (bv & bv))

/// In order to introduce variables with coherent types (the variables' types
/// may be dependent) and make things simpler, we build one big term:
/// [> (fun x1 x2 ... xn -> ())
/// Then, for each variable, we introduce a fresh variable with the same type as
/// the outermost abstraction, apply the above term to this new variable and
/// normalize to "apply" the substitution and reveal the next binding.

let rec _generate_shadowed_subst (ge:genv) (t:term) (bvl : list bv) :
  Tac (genv & list (bv & bv)) =
  match bvl with
  | [] -> ge, []
  | old_bv :: bvl' ->
    match inspect t with
    | Tv_Abs b _ ->
      (* Introduce the new binder *)
      let bv, _ = inspect_binder b in
      let bvv = inspect_bv bv in
      let ty = bvv.bv_sort in
      let name = bvv.bv_ppname in
      let ge1, fresh = genv_push_fresh_bv ge ("__" ^ name) ty in
      let t1 = mk_e_app t [pack (Tv_Var fresh)] in
      let t2 = norm_term_env ge1.env [] t1 in
      (* Recursion *)
      let ge2, nbvl = _generate_shadowed_subst ge1 t2 bvl' in
      (* Return *)
      ge2, (old_bv, fresh) :: nbvl
    | _ -> mfail "_subst_with_fresh_vars: not a Tv_Abs"

let generate_shadowed_subst ge =
  (* We need to replace the variables starting with the oldest *)
  let bvl = List.Tot.rev ge.svars in
  let bl = List.Tot.map mk_binder bvl in
  let dummy = mk_abs (`()) bl in
  _generate_shadowed_subst ge dummy bvl

/// Converts a ``typ_or_comp`` to an ``effect_info``, applies the instantiation
/// stored in the ``typ_or_comp``.
let typ_or_comp_to_effect_info (ge : genv) (c : typ_or_comp) :
  Tac effect_info =
  (* Prepare the substitution of the variables from m *)
  let m = match c with | TC_Typ ty m -> m | TC_Comp cv m -> m in
  let subst_src, subst_tgt = unzip m in
  let subst_tgt = map (fun x -> pack (Tv_Var x)) subst_tgt in
  let subst = zip subst_src subst_tgt in
  let asubst x = apply_subst ge.env x subst in
  let opt_asubst (opt : option term) : Tac (option term) =
    match opt with
    | None -> None
    | Some x -> Some (asubst x)
  in
  let asubst_in_type_info tinfo =
    let ty' = asubst tinfo.ty in
    let refin' = opt_asubst tinfo.refin in
    mk_type_info ty' refin'
  in
  match c with
  | TC_Typ ty m ->
    let tinfo = get_type_info_from_type ty in
    let tinfo = asubst_in_type_info tinfo in
    mk_effect_info E_Total tinfo None None
  | TC_Comp cv m ->
    let opt_einfo = comp_to_effect_info cv in
    match opt_einfo with
    | None -> mfail ("typ_or_comp_to_effect_info failed on: " ^ acomp_to_string cv)
    | Some einfo ->
      let ret_type_info = asubst_in_type_info einfo.ei_ret_type in
      let pre = opt_asubst einfo.ei_pre in
      let post = opt_asubst einfo.ei_post in
      mk_effect_info einfo.ei_type ret_type_info pre post

(**** Step 2 *)
/// The retrieved type refinements and post-conditions are not instantiated (they
/// are lambda functions): instantiate them to get propositions.

/// Propositions split between pre and post assertions
noeq type assertions = {
  pres : list proposition;
  posts : list proposition;
}

let mk_assertions pres posts : assertions =
  Mkassertions pres posts

// TODO: I don't understand why I need ifuel 2 here
#push-options "--ifuel 2"
/// Generate the propositions equivalent to a correct type cast.
/// Note that the type refinements need to be instantiated.
val cast_info_to_propositions : bool -> genv -> cast_info -> Tac (list proposition)
let cast_info_to_propositions dbg ge ci =
  print_dbg dbg ("[> cast_info_to_propositions:\n" ^ cast_info_to_string ci);
  match compare_cast_types dbg ci with
  | Refines -> 
    print_dbg dbg ("-> Comparison result: Refines");
    []
  | Same_raw_type ->
    print_dbg dbg ("-> Comparison result: Same_raw_type");
    let refin = get_refinement (Some?.v ci.exp_ty) in
    let inst_refin = mk_app_norm ge refin [ci.term] in
    [inst_refin]
  | Unknown ->
    print_dbg dbg ("-> Comparison result: Unknown");
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
      let inst_opt_refin = opt_mk_app_norm ge e_ty.refin [ci.term] in
      opt_cons inst_opt_refin [type_cast]
    | _ -> []
#pop-options

/// Generates a list of propositions from a list of ``cast_info``. Note that
/// the user should revert the list before printing the propositions.
val cast_info_list_to_propositions : bool -> genv -> list cast_info -> Tac (list proposition)
let cast_info_list_to_propositions dbg ge ls =
  let lsl = map (cast_info_to_propositions dbg ge) ls in
  flatten lsl

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

val compute_pre_type : bool -> env -> term -> Tac pre_post_type
let compute_pre_type dbg e pre =
  print_dbg dbg "[> compute_pre_type";
  match safe_tc e pre with
  | None ->
    print_dbg dbg "safe_tc failed";
    PP_Unknown
  | Some ty ->
    print_dbg dbg "safe_tc succeeded";
    let brs, c = collect_arr_bs ty in
    print_dbg dbg ("num binders: " ^ string_of_int (List.Tot.length brs));
    match brs, is_total_or_gtotal c with
    | [], true ->
      print_dbg dbg "PP_Pure";
      PP_Pure
    | [b], true ->
      print_dbg dbg ("PP_State " ^ (term_to_string (type_of_binder b)));
      PP_State (type_of_binder b)
    | _ ->
      print_dbg dbg "PP_Unknown";
      PP_Unknown

val opt_remove_refin : typ -> Tac typ
let opt_remove_refin ty =
  match inspect ty with
  | Tv_Refine bv _ -> (inspect_bv bv).bv_sort
  | _ -> ty

val compute_post_type : bool -> env -> term -> term -> Tac pre_post_type
let compute_post_type dbg e ret_type post =
  print_dbg dbg "[> compute_post_type";
  let get_tot_ret_type c : Tac (option term_view) =
    match get_total_or_gtotal_ret_type c with
    | Some ret_ty -> Some (inspect ret_ty)
    | None -> None
  in
  match safe_tc e post with
  | None ->
    print_dbg dbg "safe_tc failed";
    PP_Unknown
  | Some ty ->
    print_dbg dbg "safe_tc succeeded";
    let brs, c = collect_arr_bs ty in
    print_dbg dbg ("num binders: " ^ string_of_int (List.Tot.length brs));
    match brs, is_total_or_gtotal c with
    | [r], true ->
      (* Pure *)
      print_dbg dbg "PP_Pure";
      PP_Pure
    | [s1; r; s2], true ->
      (* Stateful: check that the state types are coherent *)
      let r_ty = type_of_binder r in
      let s1_ty = type_of_binder s1 in
      (* After testing with Stack: the final state seems to have a refinement
       * (which gives the postcondition) so we need to remove it to match
       * it against the initial state *)
      let s2_ty = opt_remove_refin (type_of_binder s2) in
      let ret_type_eq = term_eq ret_type r_ty in
      let state_type_eq = term_eq s1_ty s2_ty in
      print_dbg dbg ("- ret type:\n-- target: " ^ term_to_string ret_type ^
                     "\n-- binder: " ^ term_to_string r_ty);
      print_dbg dbg ("- state types:\n-- binder1: " ^ term_to_string s1_ty ^
                     "\n-- binder2: " ^ term_to_string s2_ty);
      print_dbg dbg ("- ret type equality: " ^ string_of_bool ret_type_eq);
      print_dbg dbg ("- state types equality: " ^ string_of_bool state_type_eq);
      if ret_type_eq && state_type_eq
      then
        begin
        print_dbg dbg ("PP_State" ^ term_to_string (type_of_binder s1));
        PP_State (type_of_binder s1)
        end
      else
        begin
        print_dbg dbg "PP_Unknown";
        PP_Unknown
        end
    | _ ->
      print_dbg dbg "PP_Unknown";
      PP_Unknown

val check_pre_post_type : bool -> env -> term -> term -> term -> Tac pre_post_type
let check_pre_post_type dbg e pre ret_type post =
  print_dbg dbg "[> check_pre_post_type";
  match compute_pre_type dbg e pre, compute_post_type dbg e ret_type post with
  | PP_Pure, PP_Pure ->
    print_dbg dbg "PP_Pure, PP_Pure";
    PP_Pure
  | PP_State ty1, PP_State ty2 ->
    print_dbg dbg "PP_State, PP_State";
    if term_eq ty1 ty2 then PP_State ty1 else PP_Unknown
  | _ ->
    print_dbg dbg "_, _";
    PP_Unknown

val check_opt_pre_post_type : bool -> env -> option term -> term -> option term -> Tac (option pre_post_type)
let check_opt_pre_post_type dbg e opt_pre ret_type opt_post =
  print_dbg dbg "[> check_opt_pre_post_type";
  match opt_pre, opt_post with
  | Some pre, Some post ->
    print_dbg dbg "Some pre, Some post";
    Some (check_pre_post_type dbg e pre ret_type post)
  | Some pre, None ->
    print_dbg dbg "Some pre, None";
    Some (compute_pre_type dbg e pre)
  | None, Some post ->
    print_dbg dbg "None, Some post";
    Some (compute_post_type dbg e ret_type post)
  | None, None ->
    print_dbg dbg "None, None";
    None

val push_fresh_var : env -> string -> typ -> Tac (term & binder & env)
let push_fresh_var e0 basename ty =
  let e1, b1 = push_fresh_binder e0 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  v1, b1, e1

val genv_push_fresh_var : genv -> string -> typ -> Tac (term & binder & genv)
let genv_push_fresh_var ge0 basename ty =
  let ge1, b1 = genv_push_fresh_binder ge0 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  v1, b1, ge1

val push_two_fresh_vars : env -> string -> typ -> Tac (term & binder & term & binder & env)
let push_two_fresh_vars e0 basename ty =
  let e1, b1 = push_fresh_binder e0 basename ty in
  let e2, b2 = push_fresh_binder e1 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  let v2 = pack (Tv_Var (bv_of_binder b2)) in
  v1, b1, v2, b2, e2

val genv_push_two_fresh_vars : genv -> string -> typ -> Tac (term & binder & term & binder & genv)
let genv_push_two_fresh_vars ge0 basename ty =
  let ge1, b1 = genv_push_fresh_binder ge0 basename ty in
  let ge2, b2 = genv_push_fresh_binder ge1 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  let v2 = pack (Tv_Var (bv_of_binder b2)) in
  v1, b1, v2, b2, ge2

val _introduce_variables_for_abs : genv -> typ -> Tac (list term & list binder & genv)
let rec _introduce_variables_for_abs ge ty =
  match inspect ty with
  | Tv_Arrow b c ->
    let ge1, b1 = genv_push_fresh_binder ge ("__" ^ name_of_binder b) (type_of_binder b) in
    let bv1 = bv_of_binder b1 in
    let v1 = pack (Tv_Var bv1) in
    begin match get_total_or_gtotal_ret_type c with
    | Some ty1 ->
      let vl, bl, ge2 = _introduce_variables_for_abs ge1 ty1 in
      v1 :: vl, b1 :: bl, ge2
    | None -> [v1], [b1], ge1
    end
 | _ -> [], [], ge

val introduce_variables_for_abs : genv -> term -> Tac (list term & list binder & genv)
let introduce_variables_for_abs ge tm =
  match safe_tc ge.env tm with
  | Some ty -> _introduce_variables_for_abs ge ty
  | None -> [], [], ge

val introduce_variables_for_opt_abs : genv -> option term -> Tac (list term & list binder & genv)
let introduce_variables_for_opt_abs ge opt_tm =
  match opt_tm with
  | Some tm -> introduce_variables_for_abs ge tm
  | None -> [], [], ge

val effect_type_is_stateful : effect_type -> Tot bool
let effect_type_is_stateful etype =
  match etype with
  | E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure -> false
  | E_Stack | E_ST | E_Unknown -> true

/// When manipulating pre/postconditions for an effect using the ``HS.mem`` type,
/// look for expressions of the form ``let h = ST.get ()`` in the context to find
/// a way to instantiate the pre/postconditions.
val find_mem_in_context :
     dbg:bool
  -> ge:genv
  -> parents:list term_view
  -> next:term
  -> Tac (option (bv & bv))

let is_st_get dbg t : Tac bool =
  print_dbg dbg ("[> is_st_get:\n" ^ term_to_string t);
  match inspect t with
  | Tv_App  hd (a, qual) ->
    print_dbg dbg "-> Is Tv_App";
    begin match inspect hd with
    | Tv_FVar fv ->
      print_dbg dbg ("-> Head is Tv_FVar: " ^ fv_to_string fv);
      fv_eq_name fv ["FStar"; "HyperStack"; "ST"; "get"]
    | _ ->
      print_dbg dbg "-> Head is not Tv_FVar";
      false
    end
  | _ ->
    print_dbg dbg "-> Is not Tv_App";
    false

let is_let_st_get dbg (t : term_view) =
  print_dbg dbg ("[> is_let_st_get:\n" ^ term_to_string t);
  match t with
  | Tv_Let recf attrs bv def body ->
    print_dbg dbg "The term is a let expression";
    if is_st_get dbg def then Some bv else None
  | _ ->
    print_dbg dbg "The term is not a let expression";
    None

// TODO: Define relation between parents and children in and use it in explore_term
// app: head or arg
// let : bv or def or child
// match: scrutinee or branch
// ascribed: e or ty

/// Check if the computation of a term is effectful. The return type is option
/// because we may not be able to retrieve the term computation.
val term_has_effectful_comp : env -> term -> Tac (option bool)
let term_has_effectful_comp e tm =
  let einfo_opt = compute_effect_info e tm in
  match einfo_opt with
  | Some einfo -> Some (effect_type_is_pure einfo.ei_type)
  | None -> None

/// Check if a related term is effectful. This is used to look for instances of ``HS.mem``
/// to use to instantiate pre/postconditions, which means that the term should
/// be a parent/child term of the term under study, as generated by ``explore_term``
/// (otherwise the way we check that a term is effectful doesn't make sense).
/// The computation is an overapproximation: it may happen that, for instance, we
/// can't compute a term computation. In this case, we consider that the term is
/// effectful. There are also situations in which we may not be sure which term to
/// consider.
let related_term_is_effectul dbg ge tv : Tac bool =
  let is_effectful tm =
    term_has_effectful_comp ge.env tm <> Some false
  in
  match tv with
  | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> false
  | Tv_App hd (a, qual) ->
    (* The term under focus should be the app itself or an argument *)
    false
  | Tv_Abs br body -> false
  | Tv_Arrow br c0 -> false
  | Tv_Type () -> false
  | Tv_Refine bv ref ->
    false
  | Tv_Const _ -> false
  | Tv_Uvar _ _ -> false
  | Tv_Let recf attrs bv def body -> is_effectful def
  | Tv_Match scrutinee branches ->
    (* TODO: we need to keep track of the relation between parents and children *)
    (* We assume the term under focus is in one the branches of the match - this
     * assumption is safe: in the worst case, we won't be able to find a mem to use.
     * Besides, in practice it is uncommon (impossible?) to use an effectful term
     * as the scrutinee of a match *)
    is_effectful scrutinee
  | Tv_AscribedT e ty tac -> false (* The focused term should be inside the ascription *)
  | Tv_AscribedC e c tac -> false (* The focused term should be inside the ascription *)
  | _ -> (* Unknown: keep things safe *) true

/// Look for a term of the form ``let h = ST.get ()`` in a list of parent/children terms
/// and return the let-bound bv. Abort the search if we find a non-effectful term.
/// The typical usages of this function are the following:
/// - look for a state variable to instantiate the precondition of the term under focus
/// - look for state variables for the pre/postconditions of a term defined before
///   the term under focus.
val find_mem_in_related:
     dbg:bool
  -> ge:genv
  -> tms:list term_view
  -> Tac (option bv)

let rec find_mem_in_related dbg ge tms =
  match tms with
  | [] -> None
  | tv :: tms' ->
    print_dbg dbg ("[> find_mem_in_related:\n" ^ term_to_string tv);
    match is_let_st_get dbg tv with
    | Some bv ->
      print_dbg dbg "Term is of the form `let x = FStar.HyperStack.ST.get ()`: success";
      Some bv
    | None ->
      print_dbg dbg "Term is not of the form `let x = FStar.HyperStack.ST.get ()`: continuing";
      if related_term_is_effectul dbg ge tv
      then
        begin
        print_dbg dbg "Term is effectful: stopping here";
        None
        end
      else
        begin
        print_dbg dbg "Term is not effectful: continuing";
        find_mem_in_related dbg ge tms'
        end

// TODO: not used for now
/// Look for a term of the form ``let h = ST.get ()`` in a child term (the
/// focused term is supposed to be a subterm of the definition of a let-construct).
val find_mem_in_children:
     dbg:bool
  -> ge:genv
  -> child:term
  -> Tac (genv & option bv)

let rec find_mem_in_children dbg ge child =
  (* We stop whenever we find an expression which is not a let-binding *)
  match inspect child with
  | Tv_Let recf attrs bv def body ->
    if is_st_get dbg def then ge, Some bv
    else if term_has_effectful_comp ge.env def <> Some false then ge, None
    else
      let ge1 = genv_push_bv ge bv false None in
      find_mem_in_children dbg ge1 body
  | _ -> ge, None

/// Instantiates optional pre and post conditions
val pre_post_to_propositions :
     dbg:bool
  -> ge:genv
  -> etype:effect_type
  -> ret_value:term
  -> ret_abs_binder:option binder
  -> ret_type:type_info
  -> opt_pre:option term
  -> opt_post:option term
  -> parents:list term_view (* to look for state variables for the pre *)
  -> children:list term_view (* to look for state variables for the pre and post *)
  -> Tac (genv & option proposition & option proposition)

let pre_post_to_propositions dbg ge0 etype v ret_abs_binder ret_type opt_pre opt_post
                             parents children =
  print_dbg dbg "[> pre_post_to_propositions: begin";
  print_dbg dbg ("- uninstantiated pre: " ^ option_to_string term_to_string opt_pre);
  print_dbg dbg ("- uninstantiated post: " ^ option_to_string term_to_string opt_post);
  let brs = match ret_abs_binder with | None -> [] | Some b -> [b] in
  (* Analyze the pre and the postcondition and introduce the necessary variables *)
  let ge3, (pre_values, pre_binders), (post_values, post_binders) =
    match etype with
    | E_Lemma ->
      print_dbg dbg "E_Lemma";
      ge0, ([], []), ([(`())], [])
    | E_Total | E_GTotal ->
      print_dbg dbg "E_Total/E_GTotal";
      ge0, ([], []), ([], [])
    | E_PURE | E_Pure ->
      print_dbg dbg "E_PURE/E_Pure";
      ge0, ([], []), ([v], brs)
    | E_Stack | E_ST ->
      print_dbg dbg "E_Stack/E_ST";
      (* Look for state variables in the context *)
      let b1_opt = find_mem_in_related dbg ge0 parents in
      let b2_opt = find_mem_in_related dbg ge0 children in
      (* Introduce state variables if necessary *)
      let opt_push_fresh_state opt_bv basename ge : Tac (term & binder & genv) =
        match opt_bv with
        | Some bv -> pack (Tv_Var bv), mk_binder bv, ge
        | None -> genv_push_fresh_var ge basename (`HS.mem)
      in
      let h1, b1, ge1 = opt_push_fresh_state b1_opt "__h0_" ge0 in
      let h2, b2, ge2 = opt_push_fresh_state b2_opt "__h1_" ge1 in
      ge2, ([h1], [b1]), ([h1; v; h2], List.Tot.flatten ([b1]::brs::[[b2]]))
    | E_Unknown ->
      (* We don't know what the effect is and the current pre and post-conditions
       * are currently guesses. Introduce any necessary variable abstracted by
       * those parameters *)
       (* The pre and post-conditions are likely to have the same shape as
        * one of Pure or Stack (depending on whether we use or not an internal
        * state). We try to check that and to instantiate them accordingly *)
      let pp_type = check_opt_pre_post_type dbg ge0.env opt_pre ret_type.ty opt_post in
      begin match pp_type with
      | Some PP_Pure ->
        print_dbg dbg "PP_Pure";
        (* We only need the return value *)
        ge0, ([], []), ([v], brs)
      | Some (PP_State state_type) ->
        print_dbg dbg "PP_State";
        (* Introduce variables for the states *)
        let s1, b1, s2, b2, ge1 = genv_push_two_fresh_vars ge0 "__s" state_type in
        ge1, ([s1], [b1]), ([s1; v; s2], List.Tot.flatten ([b1]::brs::[[b2]]))
      | Some PP_Unknown ->
        print_dbg dbg "PP_Unknown";
        (* Introduce variables for all the values, for the pre and the post *)
        let pre_values, pre_binders, ge1 = introduce_variables_for_opt_abs ge0 opt_pre in
        let post_values, post_binders, ge1 = introduce_variables_for_opt_abs ge1 opt_post in
        ge1, (pre_values, pre_binders), (post_values, post_binders)
      | _ ->
        print_dbg dbg "No pre and no post";
        (* No pre and no post *)
        ge0, ([], []), ([], [])
      end
  in
  (* Generate the propositions: *)
  (* - from the precondition *)
  let pre_prop = opt_mk_app_norm ge3 opt_pre pre_values in
  (* - from the postcondition - note that in the case of a global post-condition
   *   we might try to instantiate the return variable with a variable whose
   *   type is not correct, leading to an error. We thus catch errors below and
   *   drop the post if there is a problem *)
  let post_prop =
    try opt_mk_app_norm ge3 opt_post post_values
    with
    | _ ->
      print_dbg dbg "Dropping a postcondition because of incoherent typing";
      None
  in
  (* return *)
  print_dbg dbg "[> pre_post_to_propositions: end";
  ge3, pre_prop, post_prop

/// Convert effectful type information to a list of propositions. May have to
/// introduce additional binders for the preconditions/postconditions/goal (hence
/// the environment in the return type).
/// The ``bind_var`` parameter is a variable if the studied term was bound in a let
/// expression.
val eterm_info_to_assertions :
     dbg:bool
  -> with_goal:bool
  -> ge:genv
  -> t:term
  -> is_let:bool (* the term is the bound expression in a let binding *)
  -> is_assert:bool (* the term is an assert - in which case we only output the precondition *)
  -> info:eterm_info
  -> opt_bind_var:option term (* if let binding: the bound var *)
  -> opt_c:option typ_or_comp
  -> parents:list term_view
  -> children:list term_view ->
  Tac (genv & assertions)

let eterm_info_to_assertions dbg with_goal ge t is_let is_assert info bind_var opt_c
                             parents children =
  print_dbg dbg "[> eterm_info_to_assertions";
  (* Introduce additional variables to instantiate the return type refinement,
   * the precondition, the postcondition and the goal *)
  (* First, the return value: returns an updated env, the value to use for
   * the return type and a list of abstract binders *)
  let einfo = info.einfo in
  let ge0, (v : term), (opt_b : option binder) =
    match bind_var with
    | Some v -> ge, v, None
    | None ->
      (* If the studied term is stateless, we can use it directly in the
       * propositions, otherwise we need to introduced a variable for the return
       * type *)
      if effect_type_is_stateful info.einfo.ei_type then
        let b = fresh_binder ge.env "__ret" einfo.ei_ret_type.ty in
        let bv = bv_of_binder b in
        let tm = pack (Tv_Var bv) in
        genv_push_binder ge b true None, tm, Some b
      else ge, t, None
  in
  (* Generate propositions from the pre and the post-conditions *)
  (**) print_dbg dbg "> Instantiating local pre/post";
  let ge1, pre_prop, post_prop =
    pre_post_to_propositions dbg ge0 einfo.ei_type v opt_b einfo.ei_ret_type
                             einfo.ei_pre einfo.ei_post parents children in
  print_dbg dbg ("- pre prop: " ^ option_to_string term_to_string pre_prop);
  print_dbg dbg ("- post prop: " ^ option_to_string term_to_string post_prop);
  (* If the term is an assert, only output the precondition *)
  if is_assert then
    begin
    print_dbg dbg "The term is an assert: only keep the precondition";
    ge1, { pres = opt_cons pre_prop []; posts = [] }
    end
  else begin
    (* Generate propositions from the target computation (pre, post, type cast) *)
    let ge2, gpre_prop, gcast_props, gpost_prop =
      begin match opt_c, with_goal with
      | Some c, true ->
        let ei = typ_or_comp_to_effect_info ge1 c in
        print_dbg dbg ("- target effect: " ^ effect_info_to_string ei);
        print_dbg dbg ("- global unfilt. pre: " ^ option_to_string term_to_string ei.ei_pre);
        print_dbg dbg ("- global unfilt. post: " ^ option_to_string term_to_string ei.ei_post);
        (* The global pre-condition is to be used only if none of its variables
         * are shadowed (which implies that we are close enough to the top of
         * the function *)
        let gpre =
          begin match ei.ei_pre with
          | None -> None
          | Some pre ->
            let abs_vars = abs_free_in ge1 pre in
            if Cons? abs_vars then
              begin
              print_dbg dbg "Dropping the global precondition because of shadowed variables";
              None
              end
            else ei.ei_pre
          end
        in
        (* The global post-condition and the type cast are relevant only if the
         * studied term is not the definition in a let binding *)
        let gpost, gcast_props =
          if is_let then
            begin
            print_dbg dbg "Dropping the global postcondition and return type because we are studying a let expression";
            None, []
            end
          else
            (* Because of the way the studied function is rewritten before being sent to F*
             * we might have a problem with the return type (we might instantiate
             * the return variable from the global post or from the return type
             * refinement with a variable whose type is not valid for that, triggering
             * an exception. In that case, we drop the post and the target type
             * refinement. Note that here only the type refinement may be instantiated,
             * we thus also need to check for the post inside ``pre_post_to_propositions`` *)
            try
              print_dbg dbg "> Generating propositions from the global type cast";
              print_dbg dbg ("- known type: " ^ type_info_to_string einfo.ei_ret_type);
              print_dbg dbg ("- exp. type : " ^ type_info_to_string ei.ei_ret_type);
              let gcast = mk_cast_info v (Some einfo.ei_ret_type) (Some ei.ei_ret_type) in
              print_dbg dbg (cast_info_to_string gcast);
              let gcast_props = cast_info_to_propositions dbg ge1 gcast in
              print_dbg dbg "> Propositions for global type cast:";
              print_dbg dbg (list_to_string term_to_string gcast_props);
              ei.ei_post, List.Tot.rev gcast_props
            with
            | _ ->
              print_dbg dbg "Dropping the global postcondition and return type because of incoherent typing";
              None, []
        in
        (* Generate the propositions from the precondition and the postcondition *)
        (* TODO: not sure about the return type parameter: maybe catch failures *)
        print_dbg dbg "> Instantiating global pre/post";
        (* Note that we need to revert the lists of parents/children terms *)
        let ge2, gpre_prop, gpost_prop =
          pre_post_to_propositions dbg ge1 ei.ei_type v opt_b einfo.ei_ret_type
                                   gpre gpost (rev parents) (children) in
        (* Some debugging output *)
        print_dbg dbg ("- global pre prop: " ^ option_to_string term_to_string gpre_prop);
        print_dbg dbg ("- global post prop: " ^ option_to_string term_to_string gpost_prop);
        (* Return type: TODO *)
        ge2, gpre_prop, gcast_props, gpost_prop
      | _, _ -> ge1, None, [], None
      end <: Tac _
    in
    (* Generate the propositions: *)
    (* - from the parameters' cast info *)
    let params_props = cast_info_list_to_propositions dbg ge2 info.parameters in
    (* - from the return type *)
    let (ret_values : list term), (ret_binders : list binder) =
      if E_Lemma? einfo.ei_type then ([] <: list term), ([] <: list binder)
      else [v], (match opt_b with | Some b -> [b] | None -> []) in
    let ret_refin_prop = opt_mk_app_norm ge2 (get_opt_refinment einfo.ei_ret_type) ret_values in
    (* Concatenate, revert and return *)
    let pres = opt_cons gpre_prop (List.Tot.rev (opt_cons pre_prop params_props)) in
    let posts = opt_cons ret_refin_prop (opt_cons post_prop
                 (List.append gcast_props (opt_cons gpost_prop []))) in
    ge2, { pres = pres; posts = posts }
    end

(**** Step 3 *)
/// Simplify the propositions and filter the trivial ones.

/// Check if a proposition is trivial (i.e.: is True)
val is_trivial_proposition : proposition -> Tac bool

let is_trivial_proposition p =
  term_eq (`Prims.l_True) p

let simp_filter_proposition (e:env) (steps:list norm_step) (p:proposition) :
  Tac (list proposition) =
  let prop1 = norm_term_env e steps p in
  (* If trivial, filter *)
  if term_eq (`Prims.l_True) prop1 then []
  else [prop1]

let simp_filter_propositions (e:env) (steps:list norm_step) (pl:list proposition) :
  Tac (list proposition) =
  List.flatten (map (simp_filter_proposition e steps) pl)

let simp_filter_assertions (e:env) (steps:list norm_step) (a:assertions) :
  Tac assertions =
  let pres = simp_filter_propositions e steps a.pres in
  let posts = simp_filter_propositions e steps a.posts in
  mk_assertions pres posts

(**** Step 4 *)
/// Introduce fresh variables for the variables shadowed in the current environment
/// and substitute them in the terms. Note that as the binding of the value returned
/// by a function application might shadow one of its parameters, we need to treat
/// differently the pre-assertions and the post-assertions. Moreover, we need to
/// keep track of which variables are shadowed for every assertion.
  
let rec _split_subst_at_bv (#a : Type) (b : bv) (subst : list (bv & a)) :
  Tot (list (bv & a) & list (bv & a))
  (decreases subst) =
  match subst with
  | [] -> [], []
  | (src, tgt) :: subst' ->
    if bv_eq b src then
      [], subst'
    else 
      let s1, s2 = _split_subst_at_bv b subst' in
      (src, tgt) :: s1, s2

val subst_shadowed_with_abs_in_assertions : bool -> genv -> option bv -> assertions -> Tac (genv & assertions)
let subst_shadowed_with_abs_in_assertions dbg ge shadowed_bv as =
  (* When generating the substitution, we need to pay attention to the fact that
   * the returned value potentially bound by a let may shadow another variable.
   * We need to take this into account for the post-assertions (but not the
   * pre-assertions). *)
  print_dbg dbg ("subst_shadowed_with_abs_in_assertions:\n" ^ genv_to_string ge);
  (* Generate the substitution *)
  let ge1, subst = generate_shadowed_subst ge in
  let post_subst = map (fun (src, tgt) -> src, pack (Tv_Var tgt)) subst in
  (* The current substitution is valid for the post-assertions: derive from it
   * a substitution valid for the pre-assertions (just cut it where the bv
   * shadowed by the return value appears). Note that because we might introduce
   * dummy variables for the return value, it is not valid just to ignore
   * the last substitution pair. *)
  let pre_subst =
    if Some? shadowed_bv then fst (_split_subst_at_bv (Some?.v shadowed_bv) post_subst)
    else post_subst
  in
  let subst_to_string subst : Tot string =
    let to_string (x, y) =
      "(" ^ abv_to_string x ^ " -> " ^ term_to_string y ^ ")\n"
    in
    let str = List.Tot.map to_string subst in
    List.Tot.fold_left (fun x y -> x ^ y) "" str
  in
  if dbg then
    begin
    print_dbg dbg ("- pre_subst:\n" ^ subst_to_string pre_subst);
    print_dbg dbg ("- post_subst:\n" ^ subst_to_string post_subst)
    end;
  (* Apply *)
  let apply = (fun s -> map (fun t -> apply_subst ge1.env t s)) in
  let pres = apply pre_subst as.pres in
  let posts = apply post_subst as.posts in
  ge1, mk_assertions pres posts

(**** Step 5 *)
/// Output the resulting information
/// Originally: we output the ``eterm_info`` and let the emacs commands do some
/// filtering and formatting. Now, we convert ``eterm_info`` to a ``assertions``.

let printout_string (prefix data:string) : Tac unit =
  (* Export all at once - actually I'm not sure it is not possible for external
   * output to be mixed here *)
  print (prefix ^ ":\n" ^ data ^ "\n")

let printout_term (ge:genv) (prefix:string) (t:term) : Tac unit =
  (* We need to look for abstract variables and abstract them away *)
  let abs = abs_free_in ge t in
  let abs_binders = List.Tot.map mk_binder abs in
  let abs_terms = map (fun bv -> pack (Tv_Var bv)) abs in
  let t = mk_abs t abs_binders in
  let t = mk_e_app t abs_terms in
  printout_string prefix (term_to_string t)

let printout_opt_term (ge:genv) (prefix:string) (t:option term) : Tac unit =
  match t with
  | Some t' -> printout_term ge prefix t'
  | None -> printout_string prefix ""

let printout_proposition (ge:genv) (prefix:string) (p:proposition) : Tac unit =
  printout_term ge prefix p

let printout_propositions (ge:genv) (prefix:string) (pl:list proposition) : Tac unit =
  let print_prop i p =
    let prefix' = prefix ^ ":prop" ^ string_of_int i in
    printout_proposition ge prefix' p
  in
  printout_string (prefix ^ ":num") (string_of_int (List.Tot.length pl));
  iteri print_prop pl

let printout_error_message (prefix : string) (message : option string) : Tac unit =
  let msg = match message with | Some msg -> msg | _ -> "" in
  printout_string (prefix ^ ":error") msg

/// Utility type and function to communicate the results to emacs.
noeq type export_result =
| ESuccess : ge:genv -> a:assertions -> export_result
| EFailure : err:string -> export_result

let printout_result (prefix:string) (res:export_result) :
  Tac unit =
  print (prefix ^ ":BEGIN");
  (* Note that the emacs commands will always look for fields for the error message
   * and the pre/post assertions, so we need to generate them, even though they
   * might be empty. *)
  let err, ge, pres, posts =
    match res with
    | ESuccess ge a -> None, ge, a.pres, a.posts
    | EFailure err ->
      let ge = mk_init_genv (top_env ()) in (* dummy environment - will not be used *)
      Some err, ge, [], []
  in
  (* Error message *)
  printout_error_message prefix err;
  (* Assertions *)
  printout_propositions ge (prefix ^ ":pres") pres;
  printout_propositions ge (prefix ^ ":posts") posts;
  print (prefix ^ ":END")

/// The function to use to export the results in case of success
let printout_success (ge:genv) (a:assertions) : Tac unit =
  printout_result "ainfo" (ESuccess ge a)

/// The function to use to communicate failure in case of error
let printout_failure (err : string) : Tac unit =
  printout_result "ainfo" (EFailure err)

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
// TODO: actually, there already exists Prims.magic
assume val magic_witness (#a : Type) : a

let tadmit_no_warning () : Tac unit =
  apply (`magic_witness)

let pp_tac () : Tac unit =
  print ("post-processing: " ^ (term_to_string (cur_goal ())));
  dump "";
  trefl()

(*** Post-processing tactics *)

/// We declare some identifiers that we will use to guide the meta processing
assume type meta_info
assume val focus_on_term : meta_info

let unsquash_equality (t:term) : Tac (option (term & term)) =
  begin match term_as_formula t with
  | Comp (Eq _) l r -> Some (l, r)
  | _ -> None
  end

#push-options "--ifuel 2"
let pp_explore (dbg dfs : bool)
               (#a : Type0)
               (f : explorer a)
               (x : a) :
  Tac unit =
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg dbg ("[> pp_explore:\n" ^ term_to_string g);
  begin match unsquash_equality g with
  | Some (l, _) ->
    let c = safe_typ_or_comp dbg e l in
    let ge = mk_genv e [] [] in
    print_dbg dbg ("[> About to explore term:\n" ^ term_to_string l);
    let x = explore_term dbg dfs #a f x ge [] c l in
    trefl()
  | _ -> mfail "pp_explore: not a squashed equality"
  end
#pop-options

/// This function goes through the goal, which is presumed to be a squashed equality,
/// and prints all the subterms of its left operand. Very useful for debugging.
val pp_explore_print_goal : unit -> Tac unit
let pp_explore_print_goal () =
  let f : explorer unit =
    fun _ _ _ _ _ -> ((), Continue)
  in
  pp_explore true false f ()

/// Check for meta-identifiers. Note that we can't simply use ``term_eq`` which
/// sometimes unexpectedly fails (maybe because of information hidden to Meta-F*)
val is_focus_on_term : term -> Tac bool
let is_focus_on_term t =
  match inspect t with
  | Tv_FVar fv ->
    flatten_name (inspect_fv fv) = `%FEM.Process.focus_on_term
  | _ -> false

/// Check if a term is an assertion or an assumption and return its content
/// if it is the case.
val term_is_assert_or_assume : term -> Tac (option term)
let term_is_assert_or_assume t =
  match inspect t with
  | Tv_App hd (a, Q_Explicit) ->
    begin match inspect hd with
    | Tv_FVar fv ->
      let fname = flatten_name (inspect_fv fv) in
      if fname = "Prims._assert"
         || fname = "FStar.Pervasives.assert_norm"
         || fname = "Prims._assume"
      then Some a
      else None
    | _ -> None
    end
  | _ -> None

/// Check if the given term view is of the form: 'let _ = focus_on_term in body'
/// Returns 'body' if it is the case.
val is_focused_term : term_view -> Tac (option term)
let is_focused_term tv =
  match tv with
  | Tv_Let recf attrs _ def body ->
    if is_focus_on_term def then Some body else None
  | _ -> None

noeq type exploration_result (a : Type)= {
  ge : genv;
  parents : list (genv & term_view);
  tgt_comp : option typ_or_comp;
  res : a;
}

let mk_exploration_result = Mkexploration_result

let pred_explorer (a:Type) = 
  genv -> list (genv & term_view) -> option typ_or_comp -> term_view ->
  Tac (option a)

val find_predicated_term_explorer : #a:Type0 -> pred_explorer a -> bool ->
                                    explorer (option (exploration_result a))
let find_predicated_term_explorer #a pred dbg acc ge pl opt_c t =
  if Some? acc then mfail "find_focused_term_explorer: non empty accumulator";
  if dbg then
    begin
    print ("[> find_focused_term_explorer: " ^ term_view_construct t ^ ":\n" ^ term_to_string t)
    end;
  match pred ge pl opt_c t with
  | Some ft -> Some (mk_exploration_result ge pl opt_c ft), Abort
  | None -> None, Continue

val find_predicated_term : #a:Type0 -> pred_explorer a -> bool -> bool ->
                           genv -> list (genv & term_view) ->
                           option typ_or_comp -> term ->
                           Tac (option (exploration_result a))
let find_predicated_term #a pred dbg dfs ge pl opt_c t =
  fst (explore_term dbg dfs #(option (exploration_result a))
                    (find_predicated_term_explorer #a pred dbg)
                    None ge pl opt_c t)

val _is_focused_term_explorer : pred_explorer term
let _is_focused_term_explorer ge pl opt_c tv =
  is_focused_term tv

val find_focused_term : bool -> bool -> genv -> list (genv & term_view) -> option typ_or_comp -> term ->
                        Tac (option (exploration_result term))
let find_focused_term dbg dfs ge pl opt_c t =
  find_predicated_term #term _is_focused_term_explorer dbg dfs ge pl opt_c t

/// This function raises a MetaAnalysis exception if it can't find a focused term
val find_focused_term_in_current_goal : bool -> Tac (exploration_result term)
let find_focused_term_in_current_goal dbg =
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg dbg ("[> find_focused_assert_in_current_goal:\n" ^ term_to_string g);
  begin match unsquash_equality g with
  | Some (l, _) ->
    let c = safe_typ_or_comp dbg e l in
    let ge = mk_genv e [] [] in
    print_dbg dbg ("[> About to explore term:\n" ^ term_to_string l);
    begin match find_focused_term dbg true ge [] c l with
    | Some res ->
      print_dbg dbg ("[> Found focused term:\n" ^ term_to_string res.res);
      res
    | None ->
      mfail ("find_focused_term_in_current_goal: could not find a focused term in the current goal: "
             ^ term_to_string g)
    end
  | _ -> mfail "find_focused_term_in_current_goal: not a squashed equality"
  end

/// This function raises a MetaAnalysis exception if it can't find a focused term
val find_focused_assert_in_current_goal : bool -> Tac (exploration_result term)
let find_focused_assert_in_current_goal dbg =
  print_dbg dbg ("[> find_focused_assert_in_current_goal");
  let res = find_focused_term_in_current_goal dbg in
  print_dbg dbg ("[> Found focused term:\n" ^ term_to_string res.res);
  (* Check that it is an assert or an assume, retrieve the assertion *)
  let res' = 
    match inspect res.res with
    | Tv_Let _ _ bv0 fterm _ ->
      let ge' = genv_push_bv res.ge bv0 false None in
      ({ res with res = fterm; ge = ge' })
    | _ -> res
  in
  begin match term_is_assert_or_assume res'.res with
  | None -> mfail ("find_focused_assert_in_current_goal: the found focused term is not an assertion or an assumption:" ^ term_to_string res.res)
  | Some tm ->  { res' with res = tm }
  end

(**** Effectful term analysis *)
/// Aanalyze a term in order to print propertly instantiated pre/postconditions
/// and type conditions.

/// with_globals states whether to analyze the target pre/post together with the
/// focused term.
val analyze_effectful_term : 
     dbg:bool
  -> with_goal:bool
  -> res:exploration_result term
  -> Tac unit

let analyze_effectful_term dbg with_goal res =
  let ge = res.ge in
  let opt_c = res.tgt_comp in
  (* Analyze the effectful term and check whether it is a 'let' or not *)
  let ge1, studied_term, info, ret_bv, shadowed_bv, is_let =
    begin match inspect res.res with
    | Tv_Let _ _ bv0 fterm _ ->
      (* Before pushing the binder, check if it shadows another variable.
       * If it is the case, we will need it to correctly output the pre
       * and post-assertions (because for the pre-assertions the variable
       * will not be shadowed yet, while it will be the case for the post-
       * assertions) *)
      print_dbg dbg ("Restraining to: " ^ term_to_string fterm);
      let shadowed_bv =
        match genv_get_from_name ge (name_of_bv bv0) with
        | None -> None
        | Some (sbv, _) -> Some sbv
      in
      let ge1 = genv_push_bv ge bv0 false None in
      (* If the bv name is "uu___", introduce a fresh variable and use it instead:
       * the underscore might have been introduced when desugaring a let using
       * tuples. If doing that is not necessary, the introduced variable will
       * not appear in the generated assertions anyway. *)
      let ge2, (bv1 : bv) =
        let bvv0 = inspect_bv bv0 in
        let _ = print_dbg dbg ("Variable bound in let: " ^ abv_to_string bv0) in
        if bvv0.bv_ppname = "uu___" (* this is a bit hacky *)
        then genv_push_fresh_bv ge1 "ret" bvv0.bv_sort
        else ge1, bv0
      in
      let info = compute_eterm_info ge2.env fterm in
      (ge2, fterm, (info <: eterm_info), Some bv1, shadowed_bv, true)
    | _ -> (ge, res.res, compute_eterm_info ge.env res.res, None, None, false)
    end
  in
  print_dbg dbg ("[> Environment information (after effect analysis):\n" ^ genv_to_string ge1);
  (* Check if the considered term is an assert, in which case we will only
   * display the precondition (otherwise we introduce too many assertions
   * in the context) *)
  let is_assert = Some? (term_is_assert_or_assume studied_term) in
  (* Instantiate the refinements *)
  (* TODO: use bv rather than term for ret_arg *)
  let ret_arg = opt_tapply (fun x -> pack (Tv_Var x)) ret_bv in
  let parents = List.Tot.map snd res.parents in
  let ge2, asserts =
    eterm_info_to_assertions dbg with_goal ge1 studied_term is_let is_assert info
                             ret_arg opt_c parents [] in
  (* Simplify and filter *)
  let asserts = simp_filter_assertions ge2.env simpl_norm_steps asserts in
  (* Introduce fresh variables for the shadowed ones and substitute *)
  let ge3, asserts = subst_shadowed_with_abs_in_assertions dbg ge2 shadowed_bv asserts in
  (* If not a let, insert all the assertions before the term *)
  let asserts =
    if is_let then asserts
    else  mk_assertions (List.Tot.append asserts.pres asserts.posts) []
  in
  (* Print *)
  printout_success ge3 asserts

[@plugin]
val pp_analyze_effectful_term : bool -> bool -> unit -> Tac unit
let pp_analyze_effectful_term dbg with_goal () =
  try
    let res = find_focused_term_in_current_goal dbg in
    analyze_effectful_term dbg with_goal res;
    trefl()
  with | MetaAnalysis msg -> printout_failure msg; trefl()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err

(**** Split conjunctions in an assert *)
/// Split an assert made of conjunctions so that there is one assert per
/// conjunction.

/// Remove ``b2t`` if it is the head of the term
val remove_b2t : term -> Tac term
let remove_b2t (t:term) : Tac term =
  match inspect t with
  | Tv_App hd (a, Q_Explicit) ->
    begin match inspect hd with
    | Tv_FVar fv ->
      if fv_eq_name fv b2t_qn then a else t
    | _ -> t
    end
  | _ -> t

// TODO: gather all the functions like split_conjunctions, is_eq...
/// Try to destruct a term of the form '_ && _' or '_ /\ _'
val is_conjunction : term -> Tac (option (term & term))
let is_conjunction t =
  let t = remove_b2t t in
  let hd, params = collect_app t in
  match params with
  | [(x,Q_Explicit);(y,Q_Explicit)] ->
    begin match inspect hd with
    | Tv_FVar fv ->
      let fvn = inspect_fv fv in
      if name_eq fvn and_qn || name_eq fvn ["Prims"; "op_AmpAmp"]
      then Some (x, y) else None
    | _ -> None
    end
  | _ -> None

val split_conjunctions : term -> Tac (list term)

let rec _split_conjunctions (ls : list term) (t : term) : Tac (list term) =
  match is_conjunction t with
  | None -> t :: ls
  | Some (l, r) ->
    let ls1 = _split_conjunctions ls r in
    let ls2 = _split_conjunctions ls1 l in
    ls2

let split_conjunctions t =
  _split_conjunctions [] t

val split_assert_conjs : bool -> exploration_result term -> Tac unit
let split_assert_conjs dbg res =
  let ge0 = res.ge in
  (* Simplify the term (it may be an abstraction applied to some parameters) *)
  let t = norm_term_env ge0.env simpl_norm_steps res.res in
  (* Split the conjunctions *)
  let conjs = split_conjunctions t in
  let asserts = mk_assertions conjs [] in
  (* Print *)
  printout_success ge0 asserts

[@plugin]
val pp_split_assert_conjs : bool -> unit -> Tac unit
let pp_split_assert_conjs dbg () =
  try
    let res = find_focused_assert_in_current_goal dbg in
    split_assert_conjs dbg res;
    trefl()
  with | MetaAnalysis msg -> printout_failure msg; trefl()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err

(**** Term unfolding in assert *)
/// Unfolds an identifier in an assert. If the assert is an equality, unfolds
/// only on the side chosen by the user.
/// Tries to be a bit smart: it the identifier is a variable local to the function,
/// looks for an equality or a pure let-binding to replace it with.

// TODO: use "kind" keyword rather than type above
/// An equality kind
noeq type eq_kind =
  | Eq_Dec    : typ -> eq_kind          (* =   *)
  | Eq_Undec  : typ -> eq_kind          (* ==  *)
  | Eq_Hetero : typ -> typ -> eq_kind   (* === *)

/// Deconstruct an equality
// We use our own construct because ``term_as_formula`` doesn't always work
// TODO: update ``term_as_formula``
val is_eq : bool -> term -> Tac (option (eq_kind & term & term))
let is_eq dbg t =
  let t = remove_b2t t in
  print_dbg dbg ("[> is_eq: " ^ term_to_string t);
  let hd, params = collect_app t in
  print_dbg dbg ("- hd:\n" ^ term_to_string hd);
  print_dbg dbg ("- parameters:\n" ^ list_to_string (fun (x, y) -> term_to_string x) params);
  match inspect hd with
  | Tv_FVar fv ->
    let name = flatten_name (inspect_fv fv) in
    begin match params with
    | [(a,Q_Implicit);(x,Q_Explicit);(y,Q_Explicit)] ->
      if name = "Prims.op_Equality" || name = "Prims.equals" || name = "Prims.op_Equals" then
        Some ((Eq_Dec a), x, y)
      else if name = "Prims.eq2" || name = "Prims.op_Equals_Equals" then
        Some ((Eq_Undec a), x, y)
      else None
    | [(a,Q_Implicit);(b,Q_Implicit);(x,Q_Explicit);(y,Q_Explicit)] ->
      if name = "Prims.eq3" || name = "Prims.op_Equals_Equals_Equals" then
        Some ((Eq_Hetero a b), x, y)
      else None
    | _ -> None
    end
  | _ -> None

/// Reconstruct an equality
val mk_eq : eq_kind -> term -> term -> Tot term
let mk_eq k t1 t2 =
  match k with
  | Eq_Dec ty ->
    mk_app (`Prims.op_Equality) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]
  | Eq_Undec ty ->
    mk_app (`Prims.eq2) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]
  | Eq_Hetero ty1 ty2 ->
    mk_app (`Prims.eq3) [(ty1, Q_Implicit); (ty2, Q_Implicit);
                            (t1, Q_Explicit); (t2, Q_Explicit)]

let formula_construct (f : formula) : Tac string =
  match f with
  | True_       -> "True_"
  | False_      -> "False_"
  | Comp _ _ _  -> "Comp"
  | And _ _     -> "And"
  | Or _ _      -> "Or"
  | Not _       -> "Not"
  | Implies _ _ -> "Implies"
  | Iff _ _     -> "Iff"
  | Forall _ _  -> "Forall"
  | Exists _ _  -> "Exists"
  | App _ _     -> "Apply"
  | Name _      -> "Name"
  | FV _        -> "FV"
  | IntLit _    -> "IntLit"
  | F_Unknown   -> "F_Unknown"

/// Check if a proposition is an equality which can be used to rewrite a term.
/// Return the operand of the equality which the term is equal to if it is the case.
val is_equality_for_term : bool -> term -> term -> Tac (option term)
let is_equality_for_term dbg tm p =
  print_dbg dbg ("[> is_equality_for_term:" ^
                 "\n- term: " ^ term_to_string tm ^
                 "\n- prop: " ^ term_to_string p);
  (* Specialize equality for bv - TODO: not sure if necessary, but I had problems
   * in the past *)
  let check_eq : term -> Tac bool =
    match inspect tm with
    | Tv_Var bv ->
      (fun tm' -> match inspect tm' with | Tv_Var bv' -> bv_eq bv bv' | _ -> false)
    | _ -> (fun tm' -> term_eq tm tm')
  in    
  match is_eq dbg p with
  | Some (ekind, l, r) ->
    (* We ignore heterogeneous equality, because it risks to cause havoc at
     * typing after substitution *)
    print_dbg dbg ("Term is eq: " ^ term_to_string l ^ " = " ^ term_to_string r);
    if Eq_Hetero? ekind then
      begin
      print_dbg dbg "Ignoring heterogeneous equality";
      None
      end
    else if check_eq l then Some r
    else if check_eq r then Some l
    else None
  | _ ->
    print_dbg dbg "Term is not eq";
    None

val find_subequality : bool -> term -> term -> Tac (option term)
let find_subequality dbg tm p =
  print_dbg dbg ("[> find_subequality:" ^ 
                 "\n- ter  : " ^ term_to_string tm ^
                 "\n- props: " ^ term_to_string p);
  let conjuncts = split_conjunctions p in
  print_dbg dbg ("Conjuncts:\n" ^ list_to_string term_to_string conjuncts);
  tryPick (is_equality_for_term dbg tm) conjuncts

/// Look for an equality in a postcondition which can be used for rewriting.
val find_equality_from_post :
  bool -> genv -> term -> bv -> term -> typ -> effect_info ->
  list term_view -> list term_view -> Tac (genv & option term)
let find_equality_from_post dbg ge0 tm let_bv ret_value ret_type einfo parents children =
  print_dbg dbg "[> find_equality_from_post";
  let tinfo = get_type_info_from_type ret_type in
  (* Compute the post-condition *)
  let ge1, _, post_prop =
    pre_post_to_propositions dbg ge0 einfo.ei_type ret_value (Some (mk_binder let_bv))
                             tinfo einfo.ei_pre einfo.ei_post parents children
  in
  print_dbg dbg ("Computed post: " ^ option_to_string term_to_string post_prop);
  (* Look for an equality in the post *)
  let res =
    match post_prop with
    | None -> None
    | Some p -> find_subequality dbg tm p
  in
  (* If we found something, we return the updated environment,
   * otherwise we can return the original one *)
  match res with
  | None -> ge0, None
  | Some tm -> ge1, Some tm

/// Given a list of parent terms (as generated by ``explore_term``), look for an
/// equality given by a post-condition which can be used to replace a term.
val find_context_equality :
     dbg:bool
  -> ge0:genv
  -> tm:term
  -> parents:list term_view
  -> children:list term_view
  -> Tac (genv & option term)

/// Auxiliary function which actually performs the search
let rec find_context_equality_aux dbg ge0 tm (opt_bv : option bv)
                                  (parents children : list term_view) :
  Tac (genv & option term) =
  match parents with
  | [] -> ge0, None
  | tv :: parents' ->
    print_dbg dbg ("[> find_context_equality:\n" ^
                   "- term  : " ^ term_to_string tm ^ "\n" ^
                   "- parent: " ^ term_to_string tv);
    (* We only consider let-bindings *)
    match tv with
    | Tv_Let _ _ bv' def _ ->
      print_dbg dbg "Is Tv_Let";
      let tm_info = compute_eterm_info ge0.env def in
      let einfo = tm_info.einfo in
      (* If the searched term is a bv and the current let is the one which
       * introduces it:
       * - if the term is effectful, use it
       * - otherwise, try to use its postcondition. If we don't find any
       *   equalities, some there *)
      let let_bv_is_tm =
        match opt_bv with
        | Some tm_bv -> bv_eq tm_bv bv'
        | None -> false
      in
      if let_bv_is_tm && effect_type_is_pure einfo.ei_type then ge0, Some def
      else
        let ret_value = pack (Tv_Var bv') in
        let ret_typ = type_of_bv bv' in
        begin match find_equality_from_post dbg ge0 tm bv' ret_value ret_typ
                                            einfo parents children with
        | ge1, Some p -> ge1, Some p
        | _, None -> find_context_equality_aux dbg ge0 tm opt_bv parents' (tv :: children)
        end
   | _ -> find_context_equality_aux dbg ge0 tm opt_bv parents' (tv :: children)

let find_context_equality dbg ge0 tm parents children =
  let opt_bv =
    match inspect tm with
    | Tv_Var bv -> Some bv
    | _ -> None
  in
  find_context_equality_aux dbg ge0 tm opt_bv parents children

/// Replace a subterm by another term
val replace_term_in : bool -> term -> term -> term -> Tac term
let rec replace_term_in dbg from_term to_term tm =
  if term_eq from_term tm then to_term else
  match inspect tm with
  | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> tm
  | Tv_App hd (a, qual) ->
    let a' = replace_term_in dbg from_term to_term a in
    let hd' = replace_term_in dbg from_term to_term hd in
    pack (Tv_App hd' (a', qual))
  | Tv_Abs br body ->
    let body' = replace_term_in dbg from_term to_term body in
    pack (Tv_Abs br body')
  | Tv_Arrow br c0 -> tm (* TODO: we might want to explore that *)
  | Tv_Type () -> tm
  | Tv_Refine bv ref ->
    let ref' = replace_term_in dbg from_term to_term ref in
    pack (Tv_Refine bv ref')
  | Tv_Const _ -> tm
  | Tv_Uvar _ _ -> tm
  | Tv_Let recf attrs bv def body ->
    let def' = replace_term_in dbg from_term to_term def in
    let body' = replace_term_in dbg from_term to_term body in
    pack (Tv_Let recf attrs bv def' body')
  | Tv_Match scrutinee branches ->
    (* Auxiliary function to explore the branches *)
    let explore_branch (br : branch) : Tac branch =
      (* Only explore the branch body *)
      let pat, body = br in
      let body' = replace_term_in dbg from_term to_term body in
      (pat, body')
    in
    let scrutinee' = replace_term_in dbg from_term to_term scrutinee in
    let branches' = map explore_branch branches in
    pack (Tv_Match scrutinee' branches')
  | Tv_AscribedT e ty tac ->
    let e' = replace_term_in dbg from_term to_term e in
    let ty' = replace_term_in dbg from_term to_term ty in
    pack (Tv_AscribedT e' ty' tac)
  | Tv_AscribedC e c tac ->
    let e' = replace_term_in dbg from_term to_term e in
    pack (Tv_AscribedC e' c tac)
  | _ ->
    (* Unknown *)
    tm

val unfold_in_assert_or_assume : bool -> exploration_result term -> Tac unit
let unfold_in_assert_or_assume dbg ares =
  print_dbg dbg ("[> unfold_in_assert_or_assume:\n" ^ term_to_string ares.res);
  (* Find the focused term inside the assert, and on which side of the
   * equality if the assert is an equality *)
  let find_focused_in_term t =
    find_focused_term dbg false ares.ge ares.parents ares.tgt_comp t
  in
  let find_in_whole_term () : Tac _ =
    match find_focused_in_term ares.res with
    | Some res ->
      ares.res, res, (fun x -> x <: Tot term), true
    | None -> mfail "unfold_in_assert_or_assume: could not find a focused term in the assert"
  in
  (* - subterm: the subterm of the assertion in which we found the focused term
   *   (if an equality, left or right operand, otherwise whole assertion)
   * - unf_res: the result of the exploration for the focused term inside the
   *   assertion, which gives the term to UNFold
   * - rebuild: a Tot function which, given a term, rebuilds the equality by
   *   replacing the above subterm with the given term
   * - insert_before: whether to insert the new assertion before or after the
   *   current assertion in the user file *)
  let subterm, unf_res, rebuild, insert_before =
    let _ = print_dbg dbg ("Assertion: " ^ term_to_string ares.res) in
    match is_eq dbg ares.res with
    | Some (kd, l, r) ->
      print_dbg dbg "The assertion is an equality";
      begin match find_focused_in_term l with
      | Some res ->
        print_dbg dbg ("Found focused term in left operand:" ^
                       "\n- left   : " ^ term_to_string l ^
                       "\n- right  : " ^ term_to_string r ^
                       "\n- focused: " ^ term_to_string res.res);
        let rebuild t = mk_eq kd t r in
        l, res, rebuild, true
      | None ->
        begin match find_focused_in_term r with
        | Some res ->
          print_dbg dbg ("Found focused term in right operand:" ^
                 "\n- left   : " ^ term_to_string l ^
                 "\n- right  : " ^ term_to_string r ^
                 "\n- focused: " ^ term_to_string res.res);
          let rebuild t = mk_eq kd l t in
          r, res, rebuild, false
        | None ->
          mfail "unfold_in_assert_or_assume: could not find a focused term in the assert"
        end
      end
    | None -> 
      print_dbg dbg "The assertion is not an equality";
      find_in_whole_term ()
  in
  print_dbg dbg ("Found subterm in assertion/assumption:\n" ^
                 "- subterm: " ^ term_to_string subterm ^ "\n" ^
                 "- focused term: " ^ term_to_string unf_res.res);
  (* Unfold the term *)
  let res_view = inspect unf_res.res in
  let ge1, unf_tm =
    match res_view with
    | Tv_FVar fv ->
      print_dbg dbg ("The focused term is a top identifier: " ^ fv_to_string fv);
      (* The easy case: just use the normalizer *)
      let fname = flatten_name (inspect_fv fv) in
      let subterm' = norm_term_env ares.ge.env [delta_only [fname]] subterm in
      print_dbg dbg ("Normalized subterm: " ^ term_to_string subterm');
      ares.ge, subterm'
    | _ ->
      (* Look for an equality given by a previous post-condition. In the case
       * the term is a bv, we can also use the let-binding which introduces it,
       * if it is pure. *)
      let parents = List.Tot.map snd ares.parents in
      let opt_bv =
        match res_view with
        | Tv_Var bv ->
          print_dbg dbg ("The focused term is a local variable: " ^ bv_to_string bv);
          (* Check that the binder was not introduced by an abstraction inside the assertion *)
          if not (Some? (genv_get ares.ge bv)) then
            mfail "unfold_in_assert_or_assume: can't unfold a variable locally introduced in an assertion";
          Some bv
        | _ ->
          print_dbg dbg ("The focused term is an arbitrary term: " ^ term_to_string unf_res.res);
          None
      in
      let ge1, eq_tm = find_context_equality dbg ares.ge unf_res.res parents [] in
      (* Check if we found an equality *)
      let eq_tm =
        match eq_tm with
        | Some eq_tm -> eq_tm
        | _ ->
          mfail ("unfold_in_assert_or_assume: " ^
                 "couldn't find equalities with which to rewrite: " ^
                 term_to_string unf_res.res)
      in
      (* Apply it *)
      let subterm' =
        match opt_bv with
        | Some bv -> apply_subst ge1.env subterm [(bv, eq_tm)]
        | None -> replace_term_in dbg unf_res.res eq_tm subterm
      in
      ge1, subterm'
  in
  (* Create the assertions to output *)
  let final_assert = rebuild unf_tm in
  print_dbg dbg ("-> Final assertion:\n" ^ term_to_string final_assert);
  let asserts =
    if insert_before then mk_assertions [final_assert] [] else mk_assertions [] [final_assert]
  in
  (* Introduce fresh variables for the shadowed ones and substitute *)
  let ge2, asserts = subst_shadowed_with_abs_in_assertions dbg ge1 None asserts in
  (* Output *)
  printout_success ge2 asserts

[@plugin]
val pp_unfold_in_assert_or_assume : bool -> unit -> Tac unit
let pp_unfold_in_assert_or_assume dbg () =
  try
    let res = find_focused_assert_in_current_goal dbg in
    unfold_in_assert_or_assume dbg res;
    trefl()
  with | MetaAnalysis msg -> printout_failure msg; trefl()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err


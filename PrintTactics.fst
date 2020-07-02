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

(* TODO: move to FStar.Tactics.Derived.fst *)
let rec mk_abs (t : term) (args : list binder) : Tac term (decreases args) =
  match args with
  | [] -> t
  | a :: args' ->
    let t' = mk_abs t args' in
    pack (Tv_Abs a t')

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
let print_dbg (debug : bool) (s : string) : Tac unit =
  if debug then print s

// TODO: remove
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
// TODO: maybe we should deal with abstract variables inside the bind_map,
// rather than carrying them around in the terms themselves.
/// The boolean indicates whether or not the variable is considered abstract. We
/// often need to introduce variables which don't appear in the user context, for
/// example when we need to deal with a postcondition for Stack or ST, which handles
/// the previous and new memory states, and which may not be available in the user
/// context, or where we don't always know which variable to use.
/// In this case, whenever we output the term, we write its content as an
/// asbtraction applied to those missing parameters. For instance, in the
/// case of the assertion introduced for a post-condition:
/// [> assert((fun h1 h2 -> post) h1 h2);
/// Besides the informative goal, the user can replace those parameters (h1
/// and h2 above) by the proper ones then normalize the assertion by using
/// the appropriate command to get a valid assertion.
type bind_map = list (bv & bool & term)

let bind_map_push (b:bv) (abs:bool) (t:term) (m:bind_map) = (b,abs,t)::m
let bind_map_push_conc (b:bv) (t:term) (m:bind_map) = (b,false,t)::m
let bind_map_push_abs (b:bv) (t:term) (m:bind_map) = (b,true,t)::m

let rec bind_map_get (b:bv) (m:bind_map) : Tot (option (bool & term)) =
  match m with
  | [] -> None
  | (b',abs,t)::m' ->
    if compare_bv b b' = Order.Eq then Some (abs, t) else bind_map_get b m'

let rec bind_map_get_from_name (b:string) (m:bind_map) : Tot (option (bv & bool & term)) =
  match m with
  | [] -> None
  | (b',abs,t)::m' ->
    let b'v = inspect_bv b' in
    if b'v.bv_ppname = b then Some (b',abs,t) else bind_map_get_from_name b m'

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
let genv_push_bv (b:bv) (abs:bool) (t:option term) (e:genv) : Tac genv =
  match t with
  | Some t' ->
    let br = mk_binder b in
    let e' = push_binder e.env br in
    let bmap' = bind_map_push b abs t' e.bmap in
    mk_genv e' bmap'
  | None ->
    let br = mk_binder b in
    let e' = push_binder e.env br in
    let bmap' = bind_map_push b abs (pack (Tv_Var b)) e.bmap in
    mk_genv e' bmap'

let genv_push_binder (b:binder) (abs:bool) (t:option term) (e:genv) : Tac genv =
  match t with
  | Some t' ->
    let e' = push_binder e.env b in
    let bmap' = bind_map_push (bv_of_binder b) abs t' e.bmap in
    mk_genv e' bmap'
  | None ->
    let e' = push_binder e.env b in
    let bv = bv_of_binder b in
    let bmap' = bind_map_push bv abs (pack (Tv_Var bv)) e.bmap in
    mk_genv e' bmap'


/// Check if a binder is shadowed by another more recent binder
let bv_is_shadowed (ge : genv) (bv : bv) : Tot bool =
  let bl = List.Tot.map (fun (x, _, _) -> x) ge.bmap in
  let bvv = inspect_bv bv in
  let opt_res = bind_map_get_from_name bvv.bv_ppname ge.bmap in
  match opt_res with
  | None -> false (* Actually shouldn't happen if the environment was correctly updated *)
  | Some (bv', _, _) ->
    let bvv' = inspect_bv bv' in
    (* Check if it is the same binder - we don't check the type *)
    if bvv'.bv_index = bvv.bv_index then false
    else true

let binder_is_shadowed (ge : genv) (b : binder) : Tot bool =
  bv_is_shadowed ge (bv_of_binder b)

let find_shadowed_bvs (ge : genv) (bl : list bv) : Tot (list (bv & bool)) =
  List.Tot.map (fun b -> b, bv_is_shadowed ge b) bl

let find_shadowed_binders (ge : genv) (bl : list binder) : Tot (list (binder & bool)) =
  List.Tot.map (fun b -> b, binder_is_shadowed ge b) bl


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

let genv_push_fresh_binder (ge : genv) (basename : string) (ty : typ) : Tac (binder & genv) =
  let b = fresh_binder ge.env basename ty in
  let ge' = genv_push_binder b true None ge in
  b, ge'

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

/// Type information
noeq type type_info = {
  ty : typ; (* the type without refinement *)
  refin : option term;
}

let mk_type_info = Mktype_info

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
noeq type typ_or_comp =
| TC_Typ : v:typ -> m:list (binder & binder) -> typ_or_comp
| TC_Comp : v:comp -> m:list (binder & binder) -> typ_or_comp

/// Update the current ``typ_or_comp`` before going into the body of an abstraction
/// Any new binder needs to be added to the current environment (otherwise we can't,
/// for example, normalize the terms containing the binding), hence the ``env``
/// parameter, which otherwise is useless (consider like as a monadic state). Note
/// that we don't add this binder to a more general environment, because we don't
/// need it besides that.
val abs_update_typ_or_comp : binder -> typ_or_comp -> env -> Tac (env & typ_or_comp)

let _abs_update_typ (b:binder) (ty:typ) (m:list (binder & binder)) (e:env) :
  Tac (env & typ_or_comp) =
  begin match inspect ty with
  | Tv_Arrow b1 c1 ->
    push_binder e b1, TC_Comp c1 ((b1, b) :: m)
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
/// TODO: we might want something more precise (like: don't explore the type of the
/// ascription but explore its body)
/// Note that ``explore_term`` doesn't use the environment parameter besides pushing
/// binders and passing it to ``f``, which means that you can give it arbitrary
/// environments, ``explore_term`` itself won't fail (but the passed function might).
val explore_term (dbg : bool)
                 (#a : Type0) (f : a -> genv -> option typ_or_comp -> term_view -> Tac (a & ctrl_flag))
                 (x : a) (ge:genv) (c:option typ_or_comp) (t:term) :
  Tac (a & ctrl_flag)

val explore_pattern (dbg : bool)
                    (#a : Type0) (f : a -> genv -> option typ_or_comp -> term_view -> Tac (a & ctrl_flag))
                    (x : a) (ge:genv) (pat:pattern) :
  Tac (genv & a & ctrl_flag)

(* TODO: carry around the list of encompassing terms *)
let rec explore_term dbg #a f x ge c t =
  if dbg then
    begin
    print ("[> explore_term: " ^ term_construct t ^ ":\n" ^ term_to_string t)
    end;
  let tv = inspect t in
  let x', flag = f x ge c tv in
  if flag = Continue then
    begin match tv with
    | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> x', Continue
    | Tv_App hd (a,qual) ->
      let x', flag' = explore_term dbg f x ge None a in
      if flag' = Continue then
        explore_term dbg f x' ge None hd
      else x', convert_ctrl_flag flag'
    | Tv_Abs br body ->
      (* We first explore the type of the binder - the user might want to
       * check information inside the binder definition *)
      let bv = bv_of_binder br in
      let bvv = inspect_bv bv in
      let x', flag' = explore_term dbg f x ge None bvv.bv_sort in
      if flag' = Continue then
        let ge' = genv_push_binder br false None ge in
        let e'', c'= abs_update_opt_typ_or_comp br c ge'.env in
        let ge'' = { ge' with env = e'' } in
        explore_term dbg f x' ge'' c' body
      else x', convert_ctrl_flag flag'
    | Tv_Arrow br c -> x, Continue (* TODO: we might want to explore that *)
    | Tv_Type () -> x, Continue
    | Tv_Refine bv ref ->
      let bvv = inspect_bv bv in
      let x', flag' = explore_term dbg f x ge None bvv.bv_sort in
      if flag' = Continue then
        let ge' = genv_push_bv bv false None ge in
        explore_term dbg f x' ge' None ref
      else x', convert_ctrl_flag flag'
    | Tv_Const _ -> x, Continue
    | Tv_Uvar _ _ -> x, Continue
    | Tv_Let recf attrs bv def body ->
      let bvv = inspect_bv bv in
      (* Explore the binding type *)
      let x', flag' = explore_term dbg f x ge None bvv.bv_sort in
      if flag' = Continue then
        (* Explore the binding definition *)
        let x'', flag'' = explore_term dbg f x' ge None def in
        if flag'' = Continue then
          (* Explore the next subterm *)
          let ge' = genv_push_bv bv false (Some def) ge in
          explore_term dbg f x ge' c body
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
            explore_term dbg #a f x' ge' c branch_body
          else x', convert_ctrl_flag flag'
        (* Don't convert the flag *)
        else x, flag
      in
      let x' = explore_term dbg #a f x ge None scrutinee in
      fold_left explore_branch x' branches
    | Tv_AscribedT e ty tac ->
      let c' = Some (TC_Typ ty []) in
      let x', flag = explore_term dbg #a f x ge None ty in
      if flag = Continue then
        explore_term dbg #a f x' ge c' e
      else x', convert_ctrl_flag flag
    | Tv_AscribedC e c' tac ->
      (* TODO: explore the comp *)
      explore_term dbg #a f x ge (Some (TC_Comp c' [])) e
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
    let ge' = genv_push_bv bv false None ge in
    ge', x, Continue
  | Pat_Dot_Term bv t ->
    (* TODO: I'm not sure what this is *)
    let ge' = genv_push_bv bv false None ge in
    ge', x, Continue

/// Returns the list of variables free in a term
val free_in : term -> Tac (list bv)
let free_in t =
  let same_name (bv1 bv2 : bv) : Tot bool =
    name_of_bv bv1 = name_of_bv bv2
  in
  let update_free (fl:list bv) (ge:genv) (c:option typ_or_comp) (tv:term_view) :
    Tac (list bv & ctrl_flag) =
    match tv with
    | Tv_Var bv | Tv_BVar bv ->
      let bvv = inspect_bv bv in
      (* Check if the binding was not introduced during the traversal *)
      begin match bind_map_get_from_name bvv.bv_ppname ge.bmap with
      | None ->
        (* Check if we didn't already count the binding *)
        let fl' = if Some? (List.Tot.tryFind (same_name bv) fl) then fl else bv :: fl in
        fl', Continue
      | Some _ -> fl, Continue
      end
    | _ -> fl, Continue
  in
  let e = top_env () in (* we actually don't care about the environment *)
  let ge = mk_genv e [] in
  List.Tot.rev (fst (explore_term false update_free [] ge None t))

// TODO: make the parameter order consistent
val bv_is_abstract : genv -> bv -> Tot bool
let bv_is_abstract ge bv =
  match bind_map_get bv ge.bmap with
  | None -> false
  | Some (abs, _) -> abs

val binder_is_abstract : genv -> binder -> Tot bool
let binder_is_abstract ge b =
  bv_is_abstract ge (bv_of_binder b)

val genv_abstract_bvs : genv -> Tot (list bv)
let genv_abstract_bvs ge =
  let abs = List.Tot.filter (fun (_, abs, _) -> abs) ge.bmap in
  List.Tot.map (fun (bv, _, _) -> bv) abs

/// We don't check for type equality
val bv_eq : bv -> bv -> Tot bool
let bv_eq (bv1 bv2 : bv) =
  let bvv1 = inspect_bv bv1 in
  let bvv2 = inspect_bv bv2 in
  bvv1.bv_ppname = bvv2.bv_ppname && bvv1.bv_index = bvv2.bv_index

/// Returns the list of abstract variables appearing in a term, in the order in
/// which they were introduced in the context.
val abs_free_in : genv -> term -> Tac (list bv)
let abs_free_in ge t =
  let fvl = free_in t in
  let absl = List.rev (genv_abstract_bvs ge) in
  let is_free_in_term bv =
    Some? (List.Tot.find (bv_eq bv) fvl)
//  let is_abs bv =
//    Some? (List.Tot.find (bv_eq bv) absl)
  in
  let absfree = List.Tot.filter is_free_in_term absl in
  absfree

(*** Effectful term analysis *)
/// Analyze a term to retrieve its effectful information

(* /// The type to model a term containing variables which may need to be abstracted.
noeq type abs_term = {
  (* The proposition body *)
  body : term;
  (* The parameters which must be abstracted. It happens that we need to
   * use variables that don't appear in the user code (for example,
   * stack memories for the pre and post-condition of stateful functions),
   * or which have been shadowed once we reach the point where we introduce
   * them.
   * In this case, whenever we output the term, we write its content as an
   * asbtraction applied to those missing parameters. For instance, in the
   * case of the assertion introduced for a post-condition:
   * [> assert((fun h1 h2 -> post) h1 h2);
   * Besides the informative goal, the user can replace those parameters (h1
   * and h2 above) by the proper ones then normalize the assertion by using
   * the appropriate command to get a valid assertion.
   *)
  abs : list binder;
} *)

type proposition = term

(* val abs_term_to_string : abs_term -> Tot string
let abs_term_to_string at =
  let brs_str = List.Tot.map binder_to_string at.abs in
  let brs_str = List.Tot.map (fun x -> " " ^ x ^ ";") brs_str in
  let brs_str = List.Tot.fold_left (fun x y -> x ^ y) "" brs_str in
  "Mkabs_term (" ^ term_to_string at.body ^ ") [" ^ brs_str ^ "])" *)

val proposition_to_string : proposition -> Tot string
let proposition_to_string p = term_to_string p

val option_to_string : (#a : Type) -> (a -> Tot string) -> option a -> Tot string
let option_to_string #a f x =
  match x with
  | None -> "None"
  | Some x' -> "Some (" ^ f x' ^ ")"

/// Cast information
noeq type cast_info = {
  term : term;
  p_ty : option type_info; // The type of the term
  exp_ty : option type_info; // The type of the expected parameter
}

let mk_cast_info t p_ty exp_ty : cast_info =
  Mkcast_info t p_ty exp_ty

/// Extracts the effectful information from a computation
// TODO: insert in eterm_info?
noeq type effect_info = {
  ei_type : effect_type;
  ei_ret_type : type_info;
  ei_pre : option term;
  ei_post : option term;
}

let mk_effect_info = Mkeffect_info

// TODO: merge with ``effect_info``
noeq type abs_effect_info = {
  cc_type : effect_type;
  cc_pre : option proposition;
  cc_ret_type : option term;
  cc_ret_refin : option proposition; (* the stored term should have type: return_type -> Type *)
  cc_post : option proposition;
}

/// Convert a ``typ_or_comp`` to cast information
val abs_effect_info_to_string : abs_effect_info -> Tot string
let abs_effect_info_to_string c =
  "mk_abs_effect_info " ^
  effect_type_to_string c.cc_type ^ " (" ^
  option_to_string term_to_string c.cc_pre ^ ") (" ^
  option_to_string term_to_string c.cc_ret_type ^ ") (" ^
  option_to_string term_to_string c.cc_ret_refin ^ ") (" ^
  option_to_string term_to_string c.cc_post ^ ")"

let mk_abs_effect_info = Mkabs_effect_info


/// Effectful term information
noeq type eterm_info = {
  etype : effect_type;
  pre : option term;
  post : option term;
  ret_type : type_info;
  (* Head and parameters of the decomposition of the term into a function application *)
  head : term;
  parameters : list cast_info;
}

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
      mk_eterm_info einfo.ei_type einfo.ei_pre einfo.ei_post einfo.ei_ret_type
                    hd parameters
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

let compare_types (info1 info2 : type_info) :
  Tot (c:type_comparison{c = Same_raw_type ==> has_refinement info2}) =
  if term_eq info1.ty info2.ty then
      if has_refinement info2 then
        if has_refinement info1 && term_eq (get_refinement info1) (get_refinement info2) then
          Refines
        else Same_raw_type // Same raw type but can't say anything about the expected refinement
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

/// Perform a variable substitution in a term
/// TODO: we might have some problems if the variables have dependent types which
/// reference each other, in which case we might have to reconstruct the whole
/// term. But I'm not sure, because we won't trypecheck them (we will just print
/// them).
/// TODO: write a function which goes through the whole term and reconstructs it.
val subst_vars : env -> term -> list (binder & term) -> Tac term
let subst_vars e t subst =
  let bl, vl = unzip subst in
  let t1 = mk_abs t bl in
  let t2 = mk_e_app t1 vl in
  norm_term_env e [] t2

/// Substitute a list of binders with fresh binders, added to the environment.
/// The tricky part comes from the fact that there may be dependent types, in
/// which we also need to do the substitution. For this reason, we start by
/// abstracting all the binders, then whenever we need to introduce a new binder,
/// we take its type from the outermost abstraction, introduce the binder, apply
/// the abstraction to the binder then normalize.
/// TODO: use this method everywhere
val subst_with_fresh_vars : genv -> term -> list binder -> Tac (genv & term & list binder)

let rec _subst_with_fresh_vars (ge:genv) (t:term) (bl : list binder) :
  Tac (genv & term & list binder) =
  (* Note that here, we use the initial list of binders only to count *)
  match bl with
  | [] -> ge, t, []
  | _ :: bl' ->
    match inspect t with
    | Tv_Abs b _ ->
      (* Introduce the new binder *)
      let bv, _ = inspect_binder b in
      let bvv = inspect_bv bv in
      let ty = bvv.bv_sort in
      let name = bvv.bv_ppname in
      let b', ge1 = genv_push_fresh_binder ge ("__" ^ name) ty in
      let bv' = bv_of_binder b' in
      let t1 = mk_e_app t [pack (Tv_Var bv')] in
      let t2 = norm_term_env ge1.env [] t1 in
      (* Recursion *)
      let ge2, t3, nbl = _subst_with_fresh_vars ge1 t2 bl' in
      (* Return *)
      ge2, t3, b' :: nbl
    | _ -> mfail "_subst_with_fresh_vars: not a Tv_Abs"

let subst_with_fresh_vars ge t bl =
  let t' = mk_abs t bl in
  _subst_with_fresh_vars ge t' bl

/// TODO: see remark for ``subst_vars`` (problem with dependent types - might be
/// a problem whenever we introduce new variables/binders elsewhere in the code)
/// Substitutes the shadowed variables in the term with fresh abstract variables
/// introduce in the environment.
val substitute_free_vars_with_abs (ge : genv) (t : term) : Tac (genv & term)
let substitute_free_vars_with_abs ge t =
  let free_vars = free_in t in (* *)
  let free_vars = find_shadowed_bvs ge free_vars in
  (* The shadowed variables *)
  let shad_vars = List.Tot.filter (fun (bv, b) -> b) free_vars in
  let shad_vars = List.Tot.map fst shad_vars in
  let shad_binders = List.Tot.map (fun bv -> pack_binder bv Q_Explicit) shad_vars in
  (* Introduce fresh variables and substitute them in the term *)
  let ge', t', abs_binders = subst_with_fresh_vars ge t shad_binders in
  (* Introduce variables for *)
  ge', t'

val opt_substitute_free_vars_with_abs : (ge : genv) -> (opt_t : option term) ->
                                        Tac (genv & option term)
let opt_substitute_free_vars_with_abs ge opt_t =
  match opt_t with
  | None -> ge, None
  | Some t ->
    let ge', t' = substitute_free_vars_with_abs ge t in
    ge', Some t'

/// Auxiliary function: convert type information to a ``abs_effect_info``
let _typ_to_abs_effect_info (ge : genv) (etype : effect_type) (tinfo : type_info) (m : list (binder & binder)) :
  Tac (genv & abs_effect_info) =
  let rty = get_rawest_type tinfo in
  let refin = get_opt_refinment tinfo in
  let ge1, rty = substitute_free_vars_with_abs ge rty in
  let ge2, refin = opt_substitute_free_vars_with_abs ge1 refin in
  ge2, mk_abs_effect_info etype None (Some rty) refin None

/// Returns the binders introduced 
let typ_or_comp_to_abs_effect_info (ge : genv) (c : typ_or_comp) :
  Tac (genv & abs_effect_info) =
  match c with
  | TC_Typ ty m ->
    let tinfo = get_type_info_from_type ty in
    _typ_to_abs_effect_info ge E_Total tinfo m
  | TC_Comp cv m ->
    let opt_einfo = comp_to_effect_info cv in
    match opt_einfo with
    | None -> mfail ("typ_or_comp_to_abs_effect_info failed on: " ^ acomp_to_string cv)
    | Some einfo ->
      let subst_src, subst_tgt = unzip m in
      let subst_tgt = map (fun x -> pack (Tv_Var (bv_of_binder x))) subst_tgt in
      let subst = zip subst_src subst_tgt in
      let opt_subst (opt : option term) : Tac (option term) =
        match opt with
        | None -> None
        | Some x -> Some (subst_vars ge.env x subst)
      in
      let pre = opt_subst einfo.ei_pre in
      let post = opt_subst einfo.ei_post in
      let ge1, pre = opt_substitute_free_vars_with_abs ge pre in
      let ge2, post = opt_substitute_free_vars_with_abs ge1 post in
      let ge3, cci0 = _typ_to_abs_effect_info ge2 einfo.ei_type einfo.ei_ret_type m in
      ge3, { cci0 with cc_pre = pre; cc_post = post }

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

/// Generate the propositions equivalent to a correct type cast.
/// Note that the type refinements need to be instantiated.
val cast_info_to_propositions : genv -> cast_info -> Tac (list proposition)
let cast_info_to_propositions ge ci =
  match compare_cast_types ci with
  | Refines -> []
  | Same_raw_type ->
    let refin = get_refinement (Some?.v ci.exp_ty) in
    let inst_refin = mk_app_norm ge refin [ci.term] in
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
      let inst_opt_refin = opt_mk_app_norm ge e_ty.refin [ci.term] in
      opt_cons inst_opt_refin [type_cast]
    | _ -> []

/// Generates a list of propositions from a list of ``cast_info``. Note that
/// the user should revert the list before printing the propositions.
val cast_info_list_to_propositions : genv -> list cast_info -> Tac (list proposition)
let cast_info_list_to_propositions ge ls =
  let lsl = map (cast_info_to_propositions ge) ls in
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

val push_two_fresh_vars : env -> string -> typ -> Tac (term & binder & term & binder & env)
let push_two_fresh_vars e0 basename ty =
  let b1, e1 = push_fresh_binder e0 basename ty in
  let b2, e2 = push_fresh_binder e1 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  let v2 = pack (Tv_Var (bv_of_binder b2)) in
  v1, b1, v2, b2,  e2

val genv_push_two_fresh_vars : genv -> string -> typ -> Tac (term & binder & term & binder & genv)
let genv_push_two_fresh_vars ge0 basename ty =
  let b1, ge1 = genv_push_fresh_binder ge0 basename ty in
  let b2, ge2 = genv_push_fresh_binder ge1 basename ty in
  let v1 = pack (Tv_Var (bv_of_binder b1)) in
  let v2 = pack (Tv_Var (bv_of_binder b2)) in
  v1, b1, v2, b2,  ge2

val _introduce_variables_for_abs : genv -> typ -> Tac (list term & list binder & genv)
let rec _introduce_variables_for_abs ge ty =
  match inspect ty with
  | Tv_Arrow b c ->
    let b1, ge1 = genv_push_fresh_binder ge ("__" ^ name_of_binder b) (type_of_binder b) in
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
  -> Tac (genv & option proposition & option proposition)

let pre_post_to_propositions dbg ge0 etype v ret_abs_binder ret_type opt_pre opt_post =
  print_dbg dbg "[> pre_post_to_propositions: begin";
  let brs = match ret_abs_binder with | None -> [] | Some b -> [b] in
  (* Analyze the pre and the postcondition and introduce the necessary variables *)
  let ge3, (pre_values, pre_binders), (post_values, post_binders) =
    match etype with
    | E_Lemma ->
      print_dbg dbg "E_Lemma";
      ge0, ([], []), ([], [])
    | E_Total | E_GTotal ->
      print_dbg dbg "E_Total/E_GTotal";
      ge0, ([], []), ([], [])
    | E_PURE | E_Pure ->
      print_dbg dbg "E_PURE/E_Pure";
      ge0, ([], []), ([v], brs)
    | E_Stack | E_ST ->
      print_dbg dbg "E_Stack/E_ST";
      (* Introduce variables for the memories *)
      let h1, b1, h2, b2, ge1 = genv_push_two_fresh_vars ge0 "__h" (`HS.mem) in
      ge1, ([h1], [b1]), ([h1; v; h2], List.Tot.flatten ([b1]::brs::[[b2]]))
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
  let pre_prop = opt_mk_app_norm ge3 opt_pre pre_values in // opt_term_to_opt_abs_term ge3 opt_pre pre_values pre_binders in
  (* - from the postcondition *)
  let post_prop = opt_mk_app_norm ge3 opt_post post_values in // opt_term_to_opt_abs_term ge3 opt_post post_values post_binders in
  (* return *)
  print_dbg dbg "[> pre_post_to_propositions: end";
  ge3, pre_prop, post_prop

(* /// Instantiate optional pre and post conditions which may contain abstracted
/// parameters
val abs_pre_post_to_propositions :
     dbg:bool
  -> ge:genv
  -> etype:effect_type
  -> ret_value:term
  -> ret_abs_binder:option binder
  -> ret_type:type_info
  -> opt_pre:option term
  -> opt_post:option term
  -> Tac (genv & option proposition & option proposition)

let abs_pre_post_to_propositions dbg ge0 etype v ret_abs_binder ret_type opt_pre opt_post =
  print_dbg dbg "[> abs_pre_post_to_propositions: begin";
  (* Start by normalizing the pre and the post so that the abstractions get
   * simplified (we will put them back later) *)
  let simpl ge opt_p : Tac (option proposition) = 
    match opt_p with
    | None -> None
    | Some p -> Some ({ p with body = norm_term_env ge.env [] p.body })
  in
  let get_opt_body opt_p : Tac (option term) =
    match opt_p with
    | None -> None
    | Some p -> Some p.body
  in
  let get_opt_abs opt_p : Tac (list binder) =
    match opt_p with
    | None -> []
    | Some p -> p.abs
  in
  let opt_pre1 = simpl ge0 opt_pre in
  let opt_post1 = simpl ge0 opt_post in
  (* Instantiate the remaining parameters *)
  let ge1, opt_pre2, opt_post2 = 
    pre_post_to_propositions dbg ge0 etype v ret_abs_binder ret_type
                             (get_opt_body opt_pre1) (get_opt_body opt_post1) in
  (* Reintroduce the abstracted parameters *)
  let opt_pre3 = simpl ge1 opt_pre2 in
  let pre_abs1 = get_opt_abs opt_pre in
  let pre_abs2 = get_opt_abs opt_pre2 in
  let pre_abs3 = List.Tot.append pre_abs1 pre_abs2 in
  let opt_pre4 = opt_term_to_opt_abs_term ge1 (get_opt_body opt_pre3) [] pre_abs3 in
  let opt_post3 = simpl ge1 opt_post2 in
  let post_abs1 = get_opt_abs opt_post in
  let post_abs2 = get_opt_abs opt_post2 in
  let post_abs3 = List.Tot.append post_abs1 post_abs2 in
  let opt_post4 = opt_term_to_opt_abs_term ge1 (get_opt_body opt_post3) [] post_abs3 in
  (* return *)
  print_dbg dbg "[> abs_pre_post_to_propositions: end";
  ge1, opt_pre4, opt_post4 *)

(* TODO HERE *)
/// Convert effectful type information to a list of propositions. May have to
/// introduce additional binders for the preconditions/postconditions/goal (hence
/// the environment in the return type).
/// The ``bind_var`` parameter is a variable if the studied term was bound in a let
/// expression.
val eterm_info_to_assertions : bool -> genv -> term -> bool -> eterm_info -> option term -> option typ_or_comp -> Tac (genv & assertions)
let eterm_info_to_assertions dbg ge t is_let info bind_var opt_c =
  print_dbg dbg "[> eterm_info_to_assertions";
  (* Introduce additional variables to instantiate the return type refinement,
   * the precondition, the postcondition and the goal *)
  (* First, the return value: returns an updated env, the value to use for
   * the return type and a list of abstract binders *)
  let ge0, (v : term), (opt_b : option binder) =
    match bind_var with
    | Some v -> ge, v, None
    | None ->
      (* If the studied term is stateless, we can use it directly in the
       * propositions, otherwise we need to introduced a variable for the return
       * type *)
      if effect_type_is_stateful info.etype then
        let b = fresh_binder ge.env "__ret" info.ret_type.ty in
        let bv = bv_of_binder b in
        let tm = pack (Tv_Var bv) in
        genv_push_binder b true None ge, tm, Some b
      else ge, t, None
  in
  (* Instantiate the pre and post-conditions by introducing the necessary variables *)
  let ge1, pre_prop, post_prop =
    pre_post_to_propositions dbg ge0 info.etype v opt_b info.ret_type info.pre info.post in
  (* Compute and instantiate the global pre and post-conditions *)
  let ge2, gpre_prop, gpost_prop =
    match opt_c with
    | None -> ge1, None, None
    | Some c ->
      let ge2, ci = typ_or_comp_to_abs_effect_info ge1 c in
      print_dbg dbg (abs_effect_info_to_string ci);
      (* Precondition, post-condition *)
      (* TODO: not sure about the return type parameter: maybe catch failures *)
      let ge3, gpre_prop, gpost_prop =
        pre_post_to_propositions dbg ge2 ci.cc_type v opt_b info.ret_type
                                 ci.cc_pre ci.cc_post in
      (* Filter the pre/post (note that we can't do that earlier because it may
       * prevent ``abs_pre_post_to_propositions`` from succeeding its analysis) *)
      (* The global pre-condition is to be used only if none of its variables
       * are shadowed (which implies that we are close enough to the top of
       * the function *)
      let gpre_prop =
        (* Note that we check the previous value of the pre: some abstract
         * state variables might have been introduced since then *)
        begin match ci.cc_pre with
        | None -> None
        | Some pre ->
          let abs_vars = abs_free_in ge3 pre in
          if Cons? abs_vars then None else gpre_prop
        end <: Tac (option proposition)
      in
      (* The global post-condition is to be used only if we are not analyzing
       * a let expression *)
      let gpost_prop = if is_let then None else gpost_prop in
      (* Return type: TODO *)
      ge3, gpre_prop, gpost_prop
  in
  (**) print_dbg dbg ("global pre: " ^ option_to_string term_to_string gpre_prop);
  (**) print_dbg dbg ("global post: " ^ option_to_string term_to_string gpost_prop);
  (* Generate the propositions: *)
  (* - from the parameters' cast info *)
  let params_props = cast_info_list_to_propositions ge2 info.parameters in
  (* - from the return type *)
  let (ret_values : list term), (ret_binders : list binder) =
    if E_Lemma? info.etype then ([] <: list term), ([] <: list binder)
    else [v], (match opt_b with | Some b -> [b] | None -> []) in
  let ret_refin_prop = opt_mk_app_norm ge2 (get_opt_refinment info.ret_type) ret_values in
//  opt_term_to_opt_abs_term ge2 (get_opt_refinment info.ret_type) ret_values ret_binders in
  (* Concatenate, revert and return *)
  let pres = opt_cons gpre_prop (List.Tot.rev (opt_cons pre_prop params_props)) in
  let posts = opt_cons ret_refin_prop (opt_cons post_prop (opt_cons gpost_prop [])) in
  ge2, { pres = pres; posts = posts }

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

let printout_assertions (ge:genv) (prefix:string) (a:assertions) : Tac unit =
  print (prefix ^ ":BEGIN");
  printout_propositions ge (prefix ^ ":pres") a.pres;
  printout_propositions ge (prefix ^ ":posts") a.posts;
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

(*** Post-processing tactics *)

/// We declare some identifiers that we will use to guide the meta processing
assume type meta_info
assume val focus_on_term : meta_info

let pp_explore (dbg : bool)
               (#a : Type0) (f : a -> genv -> option typ_or_comp -> term_view -> Tac (a & ctrl_flag))
               (x : a) :
  Tac unit =
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg dbg ("[> pp_explore:\n" ^ term_to_string g);
  begin match term_as_formula g with
  | Comp (Eq _) l r ->
    let c : option typ_or_comp =
      match safe_tcc e l with
      | Some c -> Some (TC_Comp c [])
      | None -> None
    in
    let ge = mk_genv e [] in
    let x = explore_term dbg #a f x ge c l in
    trefl()
  | _ -> mfail "pp_explore: not a squashed equality"
  end


/// Effectful term analysis: analyze a term in order to print propertly instantiated
/// pre/postconditions and type conditions.

/// Check for meta-identifiers. Note that we can't simply use ``term_eq`` which
/// sometimes unexpectedly fails (maybe because of information hidden to Meta-F*)
val is_focus_on_term : term -> Tac bool
let is_focus_on_term t =
  match inspect t with
  | Tv_FVar fv ->
    if flatten_name (inspect_fv fv) = `%PrintTactics.focus_on_term then true else false
  | _ -> false

val analyze_effectful_term : bool -> unit -> genv -> option typ_or_comp -> term_view -> Tac (unit & ctrl_flag)

let analyze_effectful_term dbg () ge opt_c t =
  if dbg then
    begin
    print ("[> analyze_effectful_term: " ^ term_view_construct t ^ ":\n" ^ term_to_string t)
    end;
  match t with
  | Tv_Let recf attrs bv def body ->
    (* We need to check if the let definition is a meta identifier *)
       if is_focus_on_term def then
       begin
       print_dbg dbg ("[> Focus on term: " ^ term_to_string body);
       print_dbg dbg ("[> Environment information: ");
       if dbg then print_binders_info false ge.env;
       (* Start by analyzing the effectful term and checking whether it is
        * a 'let' or not *)
       let ge1, studied_term, info, ret_arg, is_let =
         begin match inspect body with
         | Tv_Let _ _ fbv fterm _ ->
           let ret_arg = pack (Tv_Var fbv) in
           genv_push_bv fbv false None ge, fterm, compute_eterm_info ge.env fterm, Some ret_arg, true
         | _ -> ge, body, compute_eterm_info ge.env body, None, false
         end
       in
       (* Instantiate the refinements *)
       let ge2, asserts =
         eterm_info_to_assertions dbg ge1 studied_term is_let info ret_arg opt_c in
       (* Simplify and filter *)
       let sasserts = simp_filter_assertions ge2.env [primops; simplify] asserts in
       (* Print *)
       printout_assertions ge2 "ainfo" sasserts;
       (), Abort
       end
     else (), Continue
  | _ -> (), Continue

val pp_focused_term : bool -> unit -> Tac unit
let pp_focused_term dbg () =
  pp_explore dbg (analyze_effectful_term dbg) ()

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
  ST.Stack nat
  (requires (fun _ -> True))
  (ensures (fun _ n _ -> n >= 2)) =
  let x = 2 in
  let _ = focus_on_term in
  x

/// Tests with shadowed dependent types
type ty1 (a : Type) : Type0 = list a
type ty2 (a b : Type0) = list a & option b
let pred1 (#a : Type) (x : ty1 a) : Tot bool = Cons? x

/// x is shadowed, so the global precondition should be dropped. However the
/// global post-condition should be displayed.
[@(postprocess_with (pp_focused_term false))]
let pp_test7 (a : Type) (x : ty1 a) :
  Pure (ty1 a)
  (requires x == x /\ a == a)
  (ensures fun x' -> x == x') =
  let y = x in
  let a = nat in
  let x = 3 in
  let _ = focus_on_term in
  y

(* TODO HERE *)
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

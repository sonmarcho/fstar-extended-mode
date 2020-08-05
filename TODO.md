* implement general functions to detect the equivalent of ST.get () to find proper state variable instantations
* the generation of the global postcondition sometimes doesn't work
* calling unfold in the middle of an identifier like FStar.UInt64.n doesn't work (we have to call it exactly on "n")

* when finding where to insert the post-processing instruction: we need to ignore the `module _ = _` instructions:
module U64 = FStar.UInt64
// TODO HERE
// The deprecated update_last just calls the new update_last.
// This one is a bit trickier than the others because we need to recompute
// the length of the data seen so far.
#push-options "--z3rlimit 800 --z3cliopt smt.arith.nl=false"
let update_last #ga s last total_len =
  let a = alg_of_state ga s in
  let last_len = U64.(total_len %^ Int.Cast.uint32_to_uint64 (block_len a)) in
  assume(U64.v (Int.Cast.uint32_to_uint64 (block_len a)) = block_length a);
  assert(U64.v last_len = FStar.UInt.mod (U64.v total_len) (U64.v (Int.Cast.uint32_to_uint64 (block_len a))));
  Math.Lemmas.euclidean_division_definition (U64.v total_len) (block_length a);
  assert(FStar.UInt64.v total_len - FStar.UInt64.v last_len <= (Prims.pow2 64 - 1 <: Prims.Tot Prims.int));
  Math.Lemmas.modulo_range_lemma (U64.v total_len) (block_length a);

gives:

#push-options "--admit_smt_queries true"
[@(FStar.Tactics.postprocess_with (FEM.Process.pp_analyze_effectful_term false false true))]
module U64 = FStar.UInt64
// TODO HERE
// The deprecated update_last just calls the new update_last.
// This one is a bit trickier than the others because we need to recompute
// the length of the data seen so far.
#push-options "--z3rlimit 800 --z3cliopt smt.arith.nl=false"
let update_last #ga s last total_len =
  let a = alg_of_state ga s in
  let last_len = U64.(total_len %^ Int.Cast.uint32_to_uint64 (block_len a)) in
  assume(U64.v (Int.Cast.uint32_to_uint64 (block_len a)) = block_length a);
  assert(U64.v last_len = FStar.UInt.mod (U64.v total_len) (U64.v (Int.Cast.uint32_to_uint64 (block_len a))));
  Math.Lemmas.euclidean_division_definition (U64.v total_len) (block_length a);
  assert(FStar.UInt64.v total_len - FStar.UInt64.v last_len <= (Prims.pow2 64 - 1 <: Prims.Tot Prims.int));
  let _ = FEM.Process.focus_on_term in
  Math.Lemmas.modulo_range_lemma (U64.v total_len) (block_length a); admit()

- switch assert assume: if no selection, only switch the assert on the current line
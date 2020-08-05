* implement general functions to detect the equivalent of ST.get () to find proper state variable instantations
* the generation of the global postcondition sometimes doesn't work
* smart indentation for roll-admit doesn't work in the following case:
#push-options "--z3rlimit 800 --z3cliopt smt.arith.nl=false"
let update_last #ga s last total_len =
  let a = alg_of_state ga s in
  let last_len = FStar.UInt64.(total_len %^ Int.Cast.uint32_to_uint64 (block_len a)) in
  assume(FStar.UInt.size (FStar.UInt64.v total_len - FStar.UInt64.v last_len) FStar.UInt64.n);
  let prev_len = FStar.UInt64.(total_len -^ last_len) in
  [@inline_let]
  let last_len = Int.Cast.uint64_to_uint32 last_len in
  assume(FStar.Integers.v last_len = LowStar.Monotonic.Buffer.length last);
  assert(
    FStar.Integers.v prev_len + FStar.Integers.v last_len <=
    Spec.Hash.Definitions.max_input_length (FStar.Ghost.reveal ga));
  assert(FStar.Integers.v prev_len % Spec.Hash.Definitions.block_length (FStar.Ghost.reveal ga) = 0);

* calling unfold in the middle of an identifier like FStar.UInt64.n doesn't work (we have to call it exactly on "n")
* doesn't work on lemma conclusions anymore

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

- roll-admit: doesn't ask for removal below
noextract inline_for_extraction
let mk_hash a alloca update_multi update_last finish input input_len dst =
  (**) assert (extra_state a == unit);
  (**) let h0 = ST.get () in
  ST.push_frame ();
  let s, _ = alloca () in
  let (blocks_n, blocks_len, blocks, rest_len, rest) = split_blocks a input input_len in
  admit()
  (**) let blocks_v0 : Ghost.erased _ = B.as_seq h0 blocks in
  (**) let rest_v0 : Ghost.erased _ = B.as_seq h0 rest in
  (**) let input_v0 : Ghost.erased _ = B.as_seq h0 input in
  (**) assert(input_v0 `S.equal` S.append blocks_v0 rest_v0);

- switch assert assume: if no selection, only switch the assert on the current line
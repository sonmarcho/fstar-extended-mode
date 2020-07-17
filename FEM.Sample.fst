/// This file gathers some sample code which was reworked by using the extended mode to analyze
/// and isolate the problematic proof obligations, and remove the unnecessary assetions.

(*** Hacl.Hash.Blake2.fst *)
(**** mk_update_last *)
(***** Before *)

// TODO: this proof often loops
#push-options "--z3rlimit 300"
let mk_update_last a m update_multi blake2_update_last_block s ev prev_len input input_len =
  (**) let h0 = ST.get () in
  (**) let input_v : Ghost.erased _ = B.as_seq h0 input in
  (* Compute the lengths to split the blocks *)
  let blocks_n, blocks_len, rest_len = split a input_len in
  (* Call update_multi on the longest series of complete blocks *)
  (**) assert (U32.v blocks_len % block_length a = 0);
  let blocks = B.sub input 0ul blocks_len in
  (**) let blocks_v : Ghost.erased _ = B.as_seq h0 blocks in
  (**) assert(
  (**)   let blocks_s, _, rem_s = Spec.Hash.Incremental.last_split_blake a input_v in
  (**)   blocks_v `Seq.equal` blocks_s /\ v rest_len == rem_s);
  let ev' = update_multi s ev blocks blocks_n in
  (**) update_multi_extra_state_eq a (as_seq h0 s, ev) blocks_v;
  (**) assert(ev' == extra_state_add_nat ev (v blocks_len));
  (**) let h1 = ST.get () in
  (**) assert (S.equal (as_seq h1 s)
  (**)         (fst (Spec.Agile.Hash.update_multi a (as_seq h0 s, ev) (B.as_seq h0 blocks))));
  (* Call update_block on the last padded block *)
  let rest = B.sub input blocks_len rest_len in
  (**) let rest_v : Ghost.erased _ = B.as_seq h0 rest in
  blake2_update_last_block s ev' rest rest_len;
  (**) let h2 = ST.get () in
  (**) assert(rest_v `Seq.equal` Seq.slice input_v (v blocks_len) (v input_len));
  (**) assert(as_seq h2 s `Seq.equal`
  (**)   fst (Spec.Hash.Incremental.update_last_blake a (as_seq h0 s, ev)
  (**)   (len_v a prev_len) input_v));
  initial_extra_state a
#pop-options


(***** After *)
noextract inline_for_extraction
val split_data (a : hash_alg{is_blake a}) (input_len : U32.t)
               (input : B.buffer uint8{B.length input = U32.v input_len}) :
  ST.Stack (size_t & size_t & size_t & B.buffer uint8 & B.buffer uint8)
  (requires (fun h0 -> B.live h0 input))
  (ensures (fun h0 (num_blocks, blocks_len, rest_len, blocks, rest) h1 ->
    B.(modifies loc_none h0 h1) /\
    begin
    let blocks_s, _, rest_s = Spec.Hash.Incremental.last_split_blake a (B.as_seq h0 input) in
    (num_blocks, blocks_len, rest_len) == split a input_len /\
    blocks == B.gsub input 0ul blocks_len /\
    rest == B.gsub input blocks_len rest_len /\
    blocks_s `Seq.equal` B.as_seq h1 blocks /\
    rest_s = U32.v rest_len /\
    U32.v blocks_len % block_length a = 0 /\
    U32.v blocks_len = U32.v num_blocks * block_length a /\
    B.live h1 blocks /\
    B.live h1 rest /\
    B.disjoint blocks rest
    end))

let split_data a input_len input =
  let num_blocks, blocks_len, rest_len = split a input_len in
  let blocks = B.sub input 0ul blocks_len in
  let rest = B.sub input blocks_len rest_len in
  num_blocks, blocks_len, rest_len, blocks, rest

noextract inline_for_extraction
val mk_update_last:
     a:hash_alg{is_blake a}
  -> m:m_spec a
  -> update_multi_st (|a, m|)
  -> blake2_update_last_block_st a m ->
  update_last_st (|a, m|)

let mk_update_last a m update_multi blake2_update_last_block s ev prev_len input input_len =
  (**) let h0 = ST.get () in
  let num_blocks, blocks_len, rest_len, blocks, rest = split_data a input_len input in
  (**) assert(B.disjoint s blocks);
  (**) assert(B.disjoint s rest);
  let ev' = update_multi s ev blocks num_blocks in
  (**) Spec.Hash.Incremental.Lemmas.update_multi_extra_state_eq a (as_seq h0 s, ev)
  (**)                                                            (B.as_seq h0 blocks);
  (**) Spec.Hash.Lemmas.extra_state_add_nat_bound_lem1 ev (B.length blocks);
  (**) assert(extra_state_v ev' = extra_state_v ev + B.length blocks);
  (**) assert(extra_state_v ev' + U32.v rest_len <= max_input a);
  blake2_update_last_block s ev' rest rest_len;
  initial_extra_state a

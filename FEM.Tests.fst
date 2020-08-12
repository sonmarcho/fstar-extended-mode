module FEM.Tests

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul
open FEM.Tutorial.Definitions

module FEM = FEM.Process

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

(*** Functors *)

noeq
type functor1 : Type0 =
|  Funct1:
   f1 : (n:nat -> b:B.buffer nat ->
         ST.Stack nat (requires (fun h0 -> B.live h0 b /\ n % 2 = 0))
         (ensures (fun h0 n' h1 -> B.modifies B.loc_none h0 h1 /\ (n' + n) % 3 = 0))) ->
   functor1

let inst1 =
  Funct1
  (fun n b ->
    let n1 = 2 * n in
    let h0 = ST.get () in
    n1)


(*** Simplification *)

let x = let x, y = 3, 4 in x + y = 7

let simpl_f1 () : Tot unit =
  let x = 3 in
  assert(let x, y = (x, 4) in x + y = 7)


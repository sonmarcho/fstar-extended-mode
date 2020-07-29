module FEM.ParseTest

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul

open FEM.Process

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"

let f1 (n : int) (m : nat) : Pure nat (requires (n > 3)) (ensures (fun _ -> True)) =
  m % (n - 3)

let f2 (x y : nat) :
  Pure (z:nat{z >= 8}) (requires True) (ensures (fun z -> z % 2 = 0)) =
  2 * (x + y) + 8

let f3 (x : nat) : nat =
  2 * x

let f4 (n : int{n % 2 = 0}) : Tot (n':int{n' % 2 = 0}) =
  n + 2

assume val sf1 (r : B.buffer int) :
  ST.Stack int
  (requires (fun _ -> True))
  (ensures (fun h0 n h1 ->
    B.live h0 r /\ B.as_seq h0 r == B.as_seq h1 r /\
    n = List.Tot.fold_left (fun x y -> x + y) 0 (Seq.seq_to_list (B.as_seq h0 r))))

assume val sf2 (l : list int) :
  ST.ST (B.buffer int)
  (requires (fun _ -> True))
  (ensures (fun h0 r h1 ->
    B.live h0 r /\
    B.as_seq h1 r == Seq.seq_of_list l))

let pred1 (x y z : nat) = True
let pred2 (x y z : nat) = True
let pred3 (x y z : nat) = True
let pred4 (x y z : nat) = True
let pred5 (x y z : nat) = True
let pred6 (x y z : nat) = True

let lpred1 (l1 l2 : Seq.seq int) = True
let lpred2 (l1 l2 : Seq.seq int) = True
let lpred3 (l1 l2 : Seq.seq int) = True

let spred1 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred2 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred3 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred4 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True

(*** Tests *)
let a'_ = 3
let f = FEM.ParseTest.a'_

let x1 = Some?.v (Some 3)
let x2 = 3
let x3 = x1-x2

let simpl_ex1 (x : nat) =
  let y = 4 in
  let 'x = 7 in
  let 'a = 4 in
  let 'd = "hello world!" in
  let '_u''x = 5 in
  let z = 3 in
  let w : w:nat{w >= 10} =
    if x > 3 then
      begin
      assert(y + x > 7);
      let x' = x + 1 in
      assert(y + x' > 8);
      let x'' = 2 * (y + x') in
      assert(x'' > 16);
      assert(x'' >= 10);
      2 * x'
      end
    else 12
  in
  assert(
    x >= 0 /\
    y >= 0);
  let w' = 2 * w + z in
  w'

let test1 b l =
  if b then
    match l with
    | [] -> true
    | _ -> false
  else
    match l with
    | [x] -> true
    | _ -> false

let test2 b l =
  if b then ()
  else assert(not b);
  let x = 3 in
  let y =
    4 +
    begin
    if b then
    let x = 4 in 2 * x
    else 8
    end
  in
  x + y

module FEM.PTests

open FStar.All
open FStar.Tactics

val tac : list (nat & nat) -> Tac unit
let tac ls =
  let l1, l2 = List.Tot.unzip ls in
  if List.length l1 >= 0 then trefl() else trefl()

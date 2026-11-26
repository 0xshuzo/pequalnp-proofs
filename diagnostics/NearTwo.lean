import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9345.Near
abbrev V := Fin 21
abbrev Box := Finset V × Finset V
def cover : List Box := [
({0,4,11,17},{2,6,8,12,14,15,19}),
({8,10,11,12,13,20},{0,1,2,3,5,14}),
({1,5,9,13,14,20},{2,3,7,11,15,17}),
({5,9,11,16,18},{3,6,13,19,20}),
({0,3,8,14,18,19},{1,6,9,11,12,16}),
({0,2,3,4,5,12},{6,13,14,15,16,18}),
({4,6,7,8,9,16},{1,10,17,18,19,20}),
({2,7,10,14,16,17},{4,5,8,11,18,20}),
({6,7,13,18},{0,1,8,10,15,16,19}),
({1,6,12,16,17,19},{4,7,9,10,14,20}),
({2,3,9,11,13,15,19},{0,4,6,17}),
({0,2,6,8,9,15,20},{3,10,12,18}),
({1,3,4,10,15,18},{5,7,12,13,16,19}),
({5,7,11,15,19,20},{0,2,8,9,13,17})]
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (i j : V) := !(board.getD i.val 0).testBit j.val
def missed (i j : V) := (i=0 ∧ j=4) ∨ (i=17 ∧ j=0)
instance (i j) : Decidable (missed i j) := by unfold missed; infer_instance
set_option maxHeartbeats 0
set_option maxRecDepth 8192
theorem valid : ∀ k : Fin cover.length, ∀ i j : V, i∈(cover.get k).1 →
    j∈(cover.get k).2 → zeroCell i j=true := by decide +kernel
theorem exactly : ∀ i j : V, (∃ k : Fin cover.length, i∈(cover.get k).1 ∧ j∈(cover.get k).2) ↔
    zeroCell i j=true ∧ ¬missed i j := by decide +kernel
theorem twoSeparate (b : Box) (ok : ∀ i∈b.1, ∀ j∈b.2, zeroCell i j=true)
    (a : (0:V)∈b.1) (d : (0:V)∈b.2) : False := by
  have bad := ok 0 a 0 d
  exact (by decide +kernel : zeroCell 0 0≠true) bad
end PEqualNP.Outside.L_meta_9345.Near

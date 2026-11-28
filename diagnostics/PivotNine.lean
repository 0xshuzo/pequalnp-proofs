import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9792.PivotNine
def neighbors (l : Fin 11) : Finset (Fin 13) :=
  match l.val with
  | 0 => {2, 3, 5, 11}
  | 1 => {3, 4, 6, 12}
  | 2 => {0, 4, 5, 7}
  | 3 => {1, 5, 6, 8}
  | 4 => {2, 6, 7, 9}
  | 5 => {3, 7, 8, 10}
  | 6 => {4, 8, 9, 11}
  | 7 => {5, 9, 10, 12}
  | 8 => {0, 6, 10, 11}
  | 9 => {1, 7, 11, 12}
  | _ => {0, 2, 8, 12}
def test (i : Fin 11) := ∀ j k : Fin 11, i ≠ j → i ≠ k → j ≠ k →
  9 ≤ (neighbors i ∪ neighbors j ∪ neighbors k).card
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row0 : test 0 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row1 : test 1 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row2 : test 2 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row3 : test 3 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row4 : test 4 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row5 : test 5 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row6 : test 6 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row7 : test 7 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row8 : test 8 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row9 : test 9 := by unfold test; decide +kernel
set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
private theorem row10 : test 10 := by unfold test; decide +kernel
theorem triples (i : Fin 11) : test i := by
  fin_cases i
  · exact row0
  · exact row1
  · exact row2
  · exact row3
  · exact row4
  · exact row5
  · exact row6
  · exact row7
  · exact row8
  · exact row9
  · exact row10
theorem costs (P : Finset (Fin 13)) (L : Finset (Fin 11))
    (cover : ∀ i ∉ L, neighbors i ⊆ P) : 9 ≤ P.card ∨ 9 ≤ L.card := by
  classical
  by_cases h : 9 ≤ L.card
  · exact Or.inr h
  · left
    have big : 2 < (Finset.univ \ L).card := by
      rw [Finset.card_sdiff (Finset.subset_univ _)]
      have univCard : (Finset.univ : Finset (Fin 11)).card = 11 := by decide
      omega
    obtain ⟨i, j, k, hi, hj, hk, neij, neik, nejk⟩ := Finset.two_lt_card_iff.mp big
    have lo := triples i j k neij neik nejk
    have si := cover i (Finset.mem_sdiff.mp hi).2
    have sj := cover j (Finset.mem_sdiff.mp hj).2
    have sk := cover k (Finset.mem_sdiff.mp hk).2
    exact lo.trans (Finset.card_le_card (Finset.union_subset (Finset.union_subset si sj) sk))

theorem budget (total guards outside single pivots loss distinctDirty : Nat)
    (k : 3 ≤ guards) (priced : 43 + 2*guards + outside + single + pivots + distinctDirty ≤ total + loss)
    (P : Finset (Fin 13)) (L : Finset (Fin 11)) (cover : ∀i ∉ L, neighbors i ⊆ P)
    (pointBound : P.card ≤ outside + single + pivots)
    (lineBound : L.card ≤ outside + single + pivots)
    (limit : total ≤ 53) : 2 * guards - 1 + distinctDirty ≤ loss := by
  rcases costs P L cover with h|h <;> omega
end PEqualNP.Outside.L_meta_9792.PivotNine

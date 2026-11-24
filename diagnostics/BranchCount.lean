import Mathlib

namespace PlaneBranch4467

theorem branch_count {V : Type*} [DecidableEq V]
    (U : Finset V) (root : V) (kids : V → Finset V)
    (covers : U ⊆ insert root (U.biUnion kids))
    (binary : ∀ v ∈ U, (kids v).card ≤ 2) :
    (U.filter fun v => (kids v).card = 0).card ≤
      (U.filter fun v => (kids v).card = 2).card + 1 := by
  classical
  have he1 := Finset.card_le_card covers
  have he2 := Finset.card_insert_le root (U.biUnion kids)
  have he3 : (U.biUnion kids).card ≤ ∑ v ∈ U, (kids v).card := Finset.card_biUnion_le
  have hsum :
      (∑ v ∈ U, (kids v).card) + (U.filter fun v => (kids v).card = 0).card =
      U.card + (U.filter fun v => (kids v).card = 2).card := by
    clear covers he1 he2 he3
    induction U using Finset.induction_on with
    | empty => simp
    | @insert v S hnot ih =>
      have hb : (kids v).card ≤ 2 := binary v (Finset.mem_insert_self _ _)
      have hs := ih (fun x hx => binary x (Finset.mem_insert_of_mem hx))
      have hz : v ∉ S.filter fun x => (kids x).card = 0 := by simp [hnot]
      have ht : v ∉ S.filter fun x => (kids x).card = 2 := by simp [hnot]
      rcases (show (kids v).card = 0 ∨ (kids v).card = 1 ∨ (kids v).card = 2 by omega) with h|h|h <;>
        simp [Finset.sum_insert, hnot, Finset.filter_insert, h, hz, ht] <;> omega
  omega

end PlaneBranch4467

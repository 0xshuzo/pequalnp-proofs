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
      have h02 : ¬ (0 : ℕ) = 2 := by decide
      have h10 : ¬ (1 : ℕ) = 0 := by decide
      have h12 : ¬ (1 : ℕ) = 2 := by decide
      have h20 : ¬ (2 : ℕ) = 0 := by decide
      rcases (show (kids v).card = 0 ∨ (kids v).card = 1 ∨ (kids v).card = 2 by omega) with h|h|h <;>
        simp only [Finset.sum_insert hnot, Finset.filter_insert, h, Finset.card_insert_of_notMem hnot,
          Finset.card_insert_of_notMem hz, Finset.card_insert_of_notMem ht, h02, h10, h12, h20, ↓reduceIte] <;> omega
  omega

end PlaneBranch4467

import Mathlib

namespace PencilForest

variable {α : Type*} [DecidableEq α]

/-- Charge one binary split if a clean wire needs two earlier clean wires.
The frontier is a set so reconvergent paths charge each split only once. -/
theorem frontier (labels : ℕ → Finset α) (clean pay : ℕ → Prop) [DecidablePred pay]
    (step : ∀ k, clean k → 1 < (labels k).card → ∃ D ⊆ Finset.range k,
      (∀ d ∈ D, clean d) ∧ D.card ≤ (if pay k then 2 else 1) ∧ labels k ⊆ D.biUnion labels)
    (k : ℕ) (F : Finset ℕ) (old : F ⊆ Finset.range k) (good : ∀ w ∈ F, clean w) :
    (F.biUnion labels).card ≤ F.card + ((Finset.range k).filter pay).card := by
  classical
  induction k generalizing F with
  | zero =>
    have eq : F = ∅ := Finset.subset_empty.mp (by simpa using old)
    simp [eq]
  | succ k ih =>
    by_cases top : k ∈ F
    · let A := F.erase k
      have aOld : A ⊆ Finset.range k := by
        intro w hw
        obtain ⟨wk,wf⟩ := Finset.mem_erase.mp hw
        have hlt := Finset.mem_range.mp (old wf)
        exact Finset.mem_range.mpr (by omega)
      have aGood : ∀ w ∈ A, clean w := fun w hw => good w (Finset.mem_of_mem_erase hw)
      have erase : A.card + 1 = F.card := Finset.card_erase_add_one top
      have more : ((Finset.range k).filter pay).card ≤ ((Finset.range (k+1)).filter pay).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
      by_cases small : (labels k).card ≤ 1
      · have sub : F.biUnion labels ⊆ A.biUnion labels ∪ labels k := by
          intro x hx
          obtain ⟨w,wf,xw⟩ := Finset.mem_biUnion.mp hx
          by_cases wk : w=k
          · exact Finset.mem_union_right _ (wk ▸ xw)
          · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w,Finset.mem_erase.mpr ⟨wk,wf⟩,xw⟩)
        have u := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
        have h := ih A aOld aGood
        omega
      obtain ⟨D,dOld,dGood,cap,covers⟩ := step k (good k top) (by omega)
      have adOld : A ∪ D ⊆ Finset.range k := Finset.union_subset aOld dOld
      have adGood : ∀ w ∈ A ∪ D, clean w :=
        fun w hw => (Finset.mem_union.mp hw).elim (aGood w) (dGood w)
      have sub : F.biUnion labels ⊆ (A ∪ D).biUnion labels := by
        intro x hx
        obtain ⟨w,wf,xw⟩ := Finset.mem_biUnion.mp hx
        by_cases wk : w=k
        · obtain ⟨d,hd,xd⟩ := Finset.mem_biUnion.mp (covers (wk ▸ xw))
          exact Finset.mem_biUnion.mpr ⟨d,Finset.mem_union_right _ hd,xd⟩
        · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨wk,wf⟩),xw⟩
      have h := (Finset.card_le_card sub).trans (ih (A ∪ D) adOld adGood)
      have sz := Finset.card_union_le A D
      by_cases charged : pay k
      · have inc : ((Finset.range (k+1)).filter pay).card = ((Finset.range k).filter pay).card+1 := by
          rw [Finset.range_succ,Finset.filter_insert,if_pos charged,Finset.card_insert_of_notMem]
          simp
        simp only [charged,if_true] at cap
        omega
      · simp only [charged,if_false] at cap
        omega
    · have prior : F ⊆ Finset.range k := by
        intro w hw
        have h := Finset.mem_range.mp (old hw)
        have wk : w ≠ k := by rintro rfl; exact top hw
        exact Finset.mem_range.mpr (by omega)
      have h := ih F prior good
      exact h.trans (Nat.add_le_add_left (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))) _)

end PencilForest

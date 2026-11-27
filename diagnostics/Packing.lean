import PEqualNP.Defs

namespace Packing851

theorem slice (q m : ℕ) (c : Fin q → ℕ) (hm : m ≤ ∑ j, c j) :
    ∃ v : Fin q → ℕ, (∀ j, v j ≤ c j) ∧ ∑ j, v j = m := by
  induction q generalizing m with
  | zero =>
    simp at hm
    exact ⟨c, fun _ => le_rfl, by simp [hm]⟩
  | succ q ih =>
    let a := min m (c 0)
    have ha : a ≤ m := min_le_left _ _
    have hb : m-a ≤ ∑ j : Fin q, c j.succ := by
      rw [Fin.sum_univ_succ] at hm
      dsimp [a]
      omega
    obtain ⟨v,hl,hs⟩ := ih (m-a) (fun j => c j.succ) hb
    refine ⟨Fin.cons a v, ?_, ?_⟩
    · intro j
      exact Fin.cases (by simpa using (min_le_right m (c 0))) (fun i => by simpa using hl i) j
    · rw [Fin.sum_univ_succ]
      simpa [hs, Nat.add_sub_cancel' ha] using (show a + (m-a) = m by omega)

theorem groups (q m E : ℕ) (c : Fin q → ℕ) (hm : ∑ j, c j = m*E) :
    ∃ g : Fin m → Fin q → ℕ, (∀ i, ∑ j, g i j = E) ∧ ∀ j, ∑ i, g i j = c j := by
  induction m generalizing c with
  | zero =>
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro j
    have hj : c j ≤ ∑ k, c k := Finset.single_le_sum (fun k _ => Nat.zero_le (c k)) (Finset.mem_univ j)
    simp at hm
    simp [show c j = 0 by omega]
  | succ m ih =>
    have hE : E ≤ ∑ j, c j := by rw [hm, Nat.succ_mul]; omega
    obtain ⟨v,hv,hs⟩ := slice q E c hE
    let w := fun j => c j-v j
    have hw (j) : w j+v j = c j := Nat.sub_add_cancel (hv j)
    have hws : ∑ j, w j = m*E := by
      have h : (∑ j, w j) + ∑ j, v j = ∑ j, c j := by
        rw [←Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => hw j
      rw [hs, hm, Nat.succ_mul] at h
      omega
    obtain ⟨g,hg,hj⟩ := ih w hws
    refine ⟨Fin.cons v g, ?_, ?_⟩
    · intro i
      exact Fin.cases (by simpa using hs) (fun k => by simpa using hg k) i
    · intro j
      rw [Fin.sum_univ_succ]
      simpa [hj, Nat.add_comm] using hw j

end Packing851

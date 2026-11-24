import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5244_1
    (peel : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO G C →
      ∃ H : Finset (Sym2 (Fin n)), H ⊆ PEqualNP.TopForm.Ustar G C ∧
        (∀ v : Fin n, 0 < (H.filter fun e => v ∈ e).card → 4 ≤ (H.filter fun e => v ∈ e).card) ∧
        (PEqualNP.TopForm.Ustar G C).card ≤ H.card + 3 * (C.size + 1))
    (dense : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → ∀ (H : Finset (Sym2 (Fin x2))), H ⊆ PEqualNP.TopForm.Ustar x3 x7 → (∀ v : Fin x2, 0 < (H.filter fun e => v ∈ e).card → 4 ≤ (H.filter fun e => v ∈ e).card) → H.card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∀ x12 ∈ PEqualNP.TopForm.junk x3 x7, x12 = x11 ∨ PEqualNP.EdgeOwnership.InCone x2 x7 x12 x11) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, bound⟩ := dense
  refine ⟨c + 3, ?_⟩
  intro n G _ hg he C hL ht hj ha hn
  obtain ⟨H, hsub, hdeg, hremoved⟩ := peel n G C hL
  have h := bound n G hg he C hL ht hj ha hn H hsub hdeg
  calc
    _ ≤ H.card + 3 * (C.size + 1) := hremoved
    _ ≤ c * (C.size + 1) + 3 * (C.size + 1) := Nat.add_le_add_right h _
    _ = (c + 3) * (C.size + 1) := (Nat.add_mul _ _ _).symm

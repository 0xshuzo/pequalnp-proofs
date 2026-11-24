import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3775_2
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let sig (v : Fin n) (j : {i // i ∈ PEqualNP.TopForm.junk G C}) (b : Fin 2) :=
          decide (v ∈ PEqualNP.TopForm.side (n := n) C j.val b)
      let Q := Finset.univ.filter fun v : Fin n => ∀ w : Fin n, sig w = sig v → w = v
      let H := (PEqualNP.TopForm.Ustar G C).filter fun e => ∃ v ∈ Q, v ∈ e
      (PEqualNP.TopForm.Ustar G C).card ≤ H.card + (C.size + 1) ∧
      H.card ≤ Q.card * (C.size + 1) ∧ Q.card ≤ 4^(PEqualNP.TopForm.junk G C).card)
    (remaining : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → 
      let sig (v : Fin x2) (j : {i // i ∈ PEqualNP.TopForm.junk x3 x7}) (b : Fin 2) :=
          decide (v ∈ PEqualNP.TopForm.side (n := x2) x7 j.val b)
      let Q := Finset.univ.filter fun v : Fin x2 => ∀ w : Fin x2, sig w = sig v → w = v
      let H := (PEqualNP.TopForm.Ustar x3 x7).filter fun e => ∃ v ∈ Q, v ∈ e
      256 < Q.card → 5 ≤ (PEqualNP.TopForm.junk x3 x7).card → H.card ≤ x1 * (x7.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (¬∃ (x12 : Finset (Fin x2)) (x13 : Finset (Sym2 (Fin x2))), x12.card ≤ (4 : ℕ) ∧ x13.card ≤ x7.size + (1 : ℕ) ∧ ∀ x14 ∈ PEqualNP.TopForm.Ustar x3 x7, x14 ∈ x13 ∨ ∃ (x16 : Fin x2) (x17 : Fin x2), x14 = s(x16, x17) ∧ ((∃ x18 ∈ x12, x3.Adj x16 x18) ∨ ∃ x18 ∈ x12, x3.Adj x17 x18)) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨c,hc⟩ := remaining
  refine ⟨max 256 c + 1, ?_⟩
  intro n G _ hg he C hL ht hj hn hno
  let sig (v : Fin n) (j : {i // i ∈ PEqualNP.TopForm.junk G C}) (b : Fin 2) :=
      decide (v ∈ PEqualNP.TopForm.side (n := n) C j.val b)
  let Q := Finset.univ.filter fun v : Fin n => ∀ w : Fin n, sig w = sig v → w = v
  let H := (PEqualNP.TopForm.Ustar G C).filter fun e => ∃ v ∈ Q, v ∈ e
  have bounds :
      (PEqualNP.TopForm.Ustar G C).card ≤ H.card + (C.size+1) ∧
      H.card ≤ Q.card * (C.size+1) ∧ Q.card ≤ 4^(PEqualNP.TopForm.junk G C).card :=
    geometry n G C hg hL ht
  have high : H.card ≤ max 256 c * (C.size+1) := by
    by_cases small : Q.card ≤ 256
    · exact bounds.2.1.trans (Nat.mul_le_mul_right _ (small.trans (le_max_left _ _)))
    · have many : 5 ≤ (PEqualNP.TopForm.junk G C).card := by
        by_contra h
        have hk : (PEqualNP.TopForm.junk G C).card ≤ 4 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
        have pw : 4^(PEqualNP.TopForm.junk G C).card ≤ (4:Nat)^4 := Nat.pow_le_pow_right (by decide) hk
        have bigQ : Q.card ≤ 256 := bounds.2.2.trans pw
        exact small bigQ
      have largeQ : 256 < Q.card := Nat.lt_of_not_ge small
      exact (hc n G hg he C hL ht hj hn hno largeQ many).trans
        (Nat.mul_le_mul_right _ (le_max_right _ _))
  calc
    _ ≤ H.card + (C.size+1) := bounds.1
    _ ≤ max 256 c * (C.size+1) + (C.size+1) := Nat.add_le_add_right high _
    _ = (max 256 c + 1) * (C.size + 1) := (Nat.succ_mul _ _).symm

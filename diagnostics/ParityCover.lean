import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.Parity
open Finset
open scoped BigOperators
abbrev V := Fin 31
abbrev F := ZMod 2
def rows : Array ℕ := #[1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def N : Matrix V V F := fun p l => if (rows[p.val]!).testBit l.val then 0 else 1
def L {k : ℕ} (R : Fin k → Finset V × Finset V) : Matrix V (Fin k) F :=
  fun p t => if p ∈ (R t).1 then 1 else 0
def H {k : ℕ} (R : Fin k → Finset V × Finset V) : Matrix (Fin k) V F :=
  fun t l => if l ∈ (R t).2 then 1 else 0
def parityError {k : ℕ} (R : Fin k → Finset V × Finset V) : Matrix V V F :=
  N - L R * H R

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem orthogonal : N * N.transpose = 1 := by
  ext i j
  revert j
  fin_cases i <;> decide +kernel

private theorem matrix_rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    have hsum : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by simp
    rw [hsum]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono : Module.finrank (ZMod 2) (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
    Submodule.finrank_mono hle
  omega


theorem unrestricted {k : ℕ} (R : Fin k → Finset V × Finset V) :
    31 ≤ k + (parityError R).rank := by
  have left : 31 ≤ N.rank := by
    have h := Matrix.rank_mul_le_left N N.transpose
    rw [orthogonal, Matrix.rank_one, Fintype.card_fin] at h
    exact h
  have prod : (L R * H R).rank ≤ k := by
    calc (L R * H R).rank ≤ (L R).rank := Matrix.rank_mul_le_left _ _
         _ = Module.finrank F (LinearMap.range (L R).mulVecLin) := rfl
         _ ≤ Module.finrank F (Fin k → F) := LinearMap.finrank_range_le _
         _ = Fintype.card (Fin k) := Module.finrank_pi F
         _ = k := Fintype.card_fin k
  have split : L R * H R + parityError R = N := by unfold parityError; abel
  have sum := matrix_rank_add_le (L R * H R) (parityError R)
  rw [split] at sum
  omega

theorem seventeen (R : Fin 17 → Finset V × Finset V) : 14 ≤ (parityError R).rank := by
  have h := unrestricted R
  omega

theorem entry {k : ℕ} (R : Fin k → Finset V × Finset V) (p l : V) :
    (L R * H R) p l =
      (((univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card : ℕ) : F) := by
  rw [Matrix.mul_apply, card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro t _
  by_cases a : p ∈ (R t).1 <;> by_cases b : l ∈ (R t).2 <;> simp [L, H, a, b]

private theorem selected (A : Finset V) (i : V) (f : V → F) :
    (∑ r : ↥A, if i = r.val then f r.val else 0) = if i ∈ A then f i else 0 := by
  classical
  by_cases hi : i ∈ A
  · let r : ↥A := ⟨i, hi⟩
    rw [Finset.sum_eq_single r]
    · simp [r, hi]
    · intro b _ ne
      have diff : i ≠ b.val := by
        intro e
        exact ne (Subtype.ext e.symm)
      simp [diff]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    have diff : i ≠ b.val := fun e => hi (e.symm ▸ b.property)
    simp [diff]

theorem supportCover (E : Matrix V V F) (A B : Finset V)
    (h : ∀ i ∉ A, ∀ j ∉ B, E i j = 0) : E.rank ≤ A.card + B.card := by
  classical
  let P : Matrix V (↥A ⊕ ↥B) F := fun i t =>
    match t with
    | .inl a => if i = a.val then 1 else 0
    | .inr b => if i ∈ A then 0 else E i b.val
  let Q : Matrix (↥A ⊕ ↥B) V F := fun t j =>
    match t with
    | .inl a => E a.val j
    | .inr b => if j = b.val then 1 else 0
  have eq : P * Q = E := by
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    change (∑ r : ↥A, (if i = r.val then (1 : F) else 0) * E r.val j) +
      (∑ b : ↥B, (if i ∈ A then (0 : F) else E i b.val) * (if j = b.val then 1 else 0)) = E i j
    have leq : (∑ r : ↥A, (if i = r.val then (1 : F) else 0) * E r.val j) =
        (∑ r : ↥A, if i = r.val then E r.val j else 0) := by simp only [ite_mul, one_mul, zero_mul]
    have req : (∑ b : ↥B, (if i ∈ A then (0 : F) else E i b.val) * (if j = b.val then 1 else 0)) =
        (∑ b : ↥B, if j = b.val then (if i ∈ A then 0 else E i b.val) else 0) := by
      simp only [mul_ite, mul_one, mul_zero]
    rw [leq, req, selected A i (fun a => E a j), selected B j (fun b => if i ∈ A then 0 else E i b)]
    by_cases hi : i ∈ A
    · simp [hi]
    · by_cases hj : j ∈ B
      · simp [hi, hj]
      · simp [hi, hj, h i hi j hj]
  rw [← eq]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
       _ = Module.finrank F (LinearMap.range P.mulVecLin) := rfl
       _ ≤ Module.finrank F (↥A ⊕ ↥B → F) := LinearMap.finrank_range_le _
       _ = Fintype.card (↥A ⊕ ↥B) := Module.finrank_pi F
       _ = A.card + B.card := by simp

theorem fourteenRowsCols (R : Fin 17 → Finset V × Finset V) (A B : Finset V)
    (h : ∀ i ∉ A, ∀ j ∉ B, (parityError R) i j = 0) : 14 ≤ A.card + B.card :=
  (seventeen R).trans (supportCover _ A B h)

end PEqualNP.Outside.L_meta_10007.Parity

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10025.Moments
open Finset
open scoped BigOperators

def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def inc (p : Fin 25) (l : Fin 30) : Bool := (rows.getD p.val 0).testBit l.val
def I (p : Fin 25) (l : Fin 30) : ℤ := if inc p l then 1 else 0
def cls (l : Fin 30) : Fin 6 := ⟨l.val / 5, by omega⟩

set_option maxRecDepth 20000 in
theorem row_sum : ∀ p, ∑ l, I p l = 6 := by decide +kernel
set_option maxRecDepth 20000 in
theorem row_pair : ∀ p q, ∑ l, I p l * I q l = if p = q then 6 else 1 := by decide +kernel
set_option maxRecDepth 20000 in
theorem col_sum : ∀ l, ∑ p, I p l = 5 := by decide +kernel
set_option maxRecDepth 20000 in
theorem col_pair : ∀ l m, ∑ p, I p l * I p m = if l = m then 5 else if cls l = cls m then 0 else 1 := by decide +kernel
set_option maxRecDepth 20000 in
theorem cls_sum : ∀ p c, ∑ l with cls l = c, I p l = 1 := by decide +kernel

abbrev E := EuclideanSpace ℝ (Fin 25)
noncomputable def basisVector (j : Fin 25) : E := EuclideanSpace.basisFun (Fin 25) ℝ j
theorem basis_apply (j k : Fin 25) : basisVector j k = if k = j then 1 else 0 := by
  simp [basisVector, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]

theorem trace_reflect (K : Submodule ℝ E) :
    ∑ j : Fin 25, (K.reflection (basisVector j)) j = 2 * (Module.finrank ℝ K : ℝ) - 25 := by
  classical
  let P := K.orthogonalProjectionOnto.toLinearMap
  have comp : P.comp K.subtype = LinearMap.id := by
    ext x
    simp [P]
  have fe : K.reflection.toLinearEquiv.toLinearMap = (2:ℝ) • (K.subtype.comp P) - LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (2 : ℕ) • K.starProjection x - x = (2 : ℝ) • (K.orthogonalProjectionOnto x : E) - x
    rw [two_smul, two_smul]
    rfl
  have tr := LinearMap.trace_comp_comm' P K.subtype
  rw [comp, LinearMap.trace_id] at tr
  have diagon : ∀ (f : E →ₗ[ℝ] E), (∑ j : Fin 25, (f (basisVector j)) j) = LinearMap.trace ℝ E f := by
    intro f
    rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 25) ℝ).toBasis]
    simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, basisVector]
  change (∑ j : Fin 25, (K.reflection.toLinearEquiv.toLinearMap (basisVector j)) j) = _
  rw [diagon K.reflection.toLinearEquiv.toLinearMap, fe]
  simp [tr, LinearMap.trace_id]

theorem refl_inner (K : Submodule ℝ E) (x y : E) :
    inner ℝ (K.reflection x) y = inner ℝ x (K.reflection y) := by
  rw [← K.reflection.inner_map_map x (K.reflection y)]
  simp

theorem inner_sum_apply (x y : E) : inner ℝ x y = ∑ j, x j * y j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

noncomputable def q (l : Fin 30) : E := WithLp.toLp 2 (fun p => ((1 - 4 * I p l : ℤ) : ℝ))
theorem q_apply (l : Fin 30) (p : Fin 25) : q l p = ((1 - 4 * I p l : ℤ) : ℝ) := rfl

theorem q_inner (l m : Fin 30) : inner ℝ (q l) (q m) = (((-15 + 16 * (∑ p, I p l * I p m)) : ℤ) : ℝ) := by
  rw [inner_sum_apply]
  simp only [q_apply]
  have h : (∑ p, (1 - 4 * I p l) * (1 - 4 * I p m)) = -15 + 16 * (∑ p, I p l * I p m) := by
    have e : ∀ p, (1 - 4 * I p l) * (1 - 4 * I p m) = 1 - 4 * I p l - 4 * I p m + 16 * (I p l * I p m) := fun p => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, col_sum]
    simp
  rw [← h]; push_cast; rfl

theorem q_self (l : Fin 30) : inner ℝ (q l) (q l) = 65 := by
  rw [q_inner, col_pair]; norm_num
theorem q_cross (l m : Fin 30) (h : l ≠ m) : inner ℝ (q l) (q m) ≤ 1 := by
  rw [q_inner, col_pair, if_neg h]; split <;> norm_num

theorem norm_y (n : Fin 30 → ℕ) :
    ‖∑ l, (n l : ℝ) • q l‖ ^ 2 ≤ 64 * (∑ l, (n l : ℝ) ^ 2) + (∑ l, (n l : ℝ)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  have step : ∀ l, inner ℝ ((n l : ℝ) • q l) (∑ m, (n m : ℝ) • q m) ≤
      (n l : ℝ) * (∑ m, (n m : ℝ)) + 64 * (n l : ℝ) ^ 2 := by
    intro l
    rw [inner_sum]
    have t : ∀ m, inner ℝ ((n l : ℝ) • q l) ((n m : ℝ) • q m) ≤
        (n l : ℝ) * (n m : ℝ) + if l = m then 64 * (n l : ℝ) ^ 2 else 0 := by
      intro m
      rw [real_inner_smul_left, real_inner_smul_right]
      by_cases h : l = m
      · subst h; rw [q_self, if_pos rfl]; nlinarith
      · rw [if_neg h, add_zero]
        have := q_cross l m h
        have h1 : (0:ℝ) ≤ (n l : ℝ) * (n m : ℝ) := by positivity
        nlinarith
    calc _ ≤ ∑ m, ((n l : ℝ) * (n m : ℝ) + if l = m then 64 * (n l : ℝ) ^ 2 else 0) := sum_le_sum fun m _ => t m
      _ = _ := by simp [sum_add_distrib, mul_sum]
  calc _ ≤ ∑ l, ((n l : ℝ) * (∑ m, (n m : ℝ)) + 64 * (n l : ℝ) ^ 2) := sum_le_sum fun l _ => step l
    _ = _ := by rw [sum_add_distrib, ← sum_mul, ← mul_sum]; ring

noncomputable def one (B : Finset (Fin 25)) : E := WithLp.toLp 2 (fun p => if p ∈ B then (1:ℝ) else 0)
theorem one_inner (B : Finset (Fin 25)) (x : E) : inner ℝ x (one B) = ∑ p ∈ B, x p := by
  rw [inner_sum_apply]
  simp [one]

theorem zero_column (j : Fin 25) : ∑ l, ((1 - I j l : ℤ) : ℝ) • q l = (20:ℝ) • basisVector j + (4:ℝ) • one univ := by
  ext k
  have h : (∑ l, (1 - I j l) * (1 - 4 * I k l)) = 20 * (if k = j then 1 else 0) + 4 := by
    have e : ∀ l, (1 - I j l) * (1 - 4 * I k l) = 1 - I j l - 4 * I k l + 4 * (I j l * I k l) := fun l => by ring
    simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, row_sum, row_pair]
    by_cases hk : k = j
    · subst hk; simp
    · have : ¬ j = k := fun h => hk h.symm
      simp [hk, this]
  have h' : (∑ l, ((1 - I j l : ℤ) : ℝ) * ((1 - 4 * I k l : ℤ) : ℝ)) = 20 * (if k = j then 1 else 0) + 4 := by
    exact_mod_cast h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, basis_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simpa [one, q_apply] using h'

abbrev Box := Finset (Fin 25) × Finset (Fin 30)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def nn {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ := cov R p l - 1

theorem swap_sum {k : ℕ} (R : Fin k → Box) (f : Fin 25 → Fin 30 → ℝ) :
    ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, f p l = ∑ p, ∑ l, (cov R p l : ℝ) * f p l := by
  have c : ∀ p l, (cov R p l : ℝ) * f p l = ∑ t, if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0 := by
    intro p l
    rw [cov, card_filter]; push_cast; rw [sum_mul]
    exact sum_congr rfl fun t _ => by split <;> simp
  simp only [c]
  have r : ∀ p, ∑ l, ∑ t, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) =
      ∑ t, ∑ l, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) := fun p => sum_comm
  simp only [r]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  have z : ∀ l, ∑ p, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) =
      if l ∈ (R t).2 then ∑ p ∈ (R t).1, f p l else 0 := by
    intro l
    by_cases h : l ∈ (R t).2
    · simp [h]
    · simp [h]
  calc _ = ∑ l, (if l ∈ (R t).2 then ∑ p ∈ (R t).1, f p l else 0) := by simp
    _ = ∑ l, ∑ p, (if p ∈ (R t).1 ∧ l ∈ (R t).2 then f p l else 0) := by simp only [z]
    _ = _ := sum_comm

theorem cov_split {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (covers : ∀ p l, inc p l = false → 0 < cov R p l) (p : Fin 25) (l : Fin 30) :
    (cov R p l : ℤ) = (nn R p l : ℤ) + (1 - I p l) := by
  unfold nn I
  by_cases h : inc p l = true
  · have : cov R p l = 0 := by
      rw [cov, card_eq_zero, filter_eq_empty_iff]
      rintro t - ⟨h1, h2⟩
      have := good t p h1 l h2
      rw [h] at this; exact absurd this (by simp)
    simp [this, h]
  · have h' : inc p l = false := by simpa using h
    have := covers p l h'
    simp [h']; omega

theorem spectral {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (covers : ∀ p l, inc p l = false → 0 < cov R p l) :
    ∃ W : Fin 30 → Fin 25 → ℝ,
      (1000 - 40 * (k : ℝ)) + ∑ p, ∑ l, (nn R p l : ℝ) ≤ ∑ p, ∑ l, (nn R p l : ℝ) * W l p ∧
      (∀ p, (∑ l, (nn R p l : ℝ) * W l p) ^ 2 ≤
        64 * (∑ l, (nn R p l : ℝ) ^ 2) + (∑ l, (nn R p l : ℝ)) ^ 2) ∧
      (∀ l, (∑ p, (nn R p l : ℝ) * W l p) ^ 2 ≤ 65 * ∑ p, (nn R p l : ℝ) ^ 2) := by
  classical
  let K : Submodule ℝ E := Submodule.span ℝ (Set.range fun t => one (R t).1)
  have dim : Module.finrank ℝ K ≤ k := by
    have := finrank_range_le_card (R := ℝ) (fun t => one (R t).1)
    simp only [Fintype.card_fin] at this
    exact this
  let W : Fin 30 → Fin 25 → ℝ := fun l p => (K.reflection (q l)) p
  have Wdef : ∀ l p, W l p = (K.reflection (q l)) p := fun _ _ => rfl
  refine ⟨W, ?_, ?_, ?_⟩
  · have charge : ∀ t, ∀ l ∈ (R t).2, ∑ p ∈ (R t).1, W l p = ((R t).1.card : ℝ) := by
      intro t l hl
      have m : one (R t).1 ∈ K := Submodule.subset_span ⟨t, rfl⟩
      have e := one_inner (R t).1 (K.reflection (q l))
      rw [refl_inner, K.reflection_mem_subspace_eq_self m, one_inner] at e
      simp only [Wdef]
      rw [← e]
      have : ∀ p ∈ (R t).1, q l p = 1 := by
        intro p hp
        have := good t p hp l hl
        simp [q_apply, I, this]
      rw [sum_congr rfl this]; simp
    have tot : ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, W l p = ∑ t, ∑ l ∈ (R t).2, ∑ p ∈ (R t).1, (1:ℝ) := by
      refine sum_congr rfl fun t _ => sum_congr rfl fun l hl => ?_
      rw [charge t l hl]; simp
    rw [swap_sum R (fun p l => W l p), swap_sum R (fun _ _ => 1)] at tot
    have split : ∀ p l, (cov R p l : ℝ) = (nn R p l : ℝ) + ((1 - I p l : ℤ) : ℝ) := by
      intro p l
      have := cov_split R good covers p l
      exact_mod_cast this
    have zero : ∑ p, ∑ l, ((1 - I p l : ℤ) : ℝ) * W l p ≤ 40 * (k : ℝ) - 400 := by
      have col : ∀ p, ∑ l, ((1 - I p l : ℤ) : ℝ) * W l p =
          20 * (K.reflection (basisVector p)) p + 4 * (K.reflection (one univ)) p := by
        intro p
        have := congrArg (fun v => (K.reflection v) p) (zero_column p)
        simp only [map_sum, map_smul, map_add, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          WithLp.ofLp_sum, Finset.sum_apply] at this
        simpa [Wdef] using this
      simp only [col]
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, trace_reflect]
      have u : ∑ p, (K.reflection (one univ)) p ≤ 25 := by
        rw [← one_inner univ]
        have n1 : ‖one univ‖ ^ 2 = 25 := by
          rw [← real_inner_self_eq_norm_sq, one_inner]; simp [one]
        have := real_inner_le_norm (K.reflection (one univ)) (one univ)
        rw [LinearIsometryEquiv.norm_map] at this
        nlinarith
      have : (Module.finrank ℝ K : ℝ) ≤ k := by exact_mod_cast dim
      linarith
    have area : ∑ p, ∑ l, ((1 - I p l : ℤ) : ℝ) = 600 := by
      have : (∑ p, ∑ l, (1 - I p l)) = 600 := by
        simp only [sum_sub_distrib, row_sum]; simp
      exact_mod_cast this
    simp only [split, add_mul, sum_add_distrib, mul_one] at tot
    linarith
  · intro p
    have e : ∑ l, (nn R p l : ℝ) * W l p = (K.reflection (∑ l, (nn R p l : ℝ) • q l)) p := by
      simp [map_sum, map_smul, Wdef]
    rw [e]
    refine le_trans ?_ (norm_y (fun l => nn R p l))
    have := PiLp.norm_apply_le (K.reflection (∑ l, (nn R p l : ℝ) • q l)) p
    rw [LinearIsometryEquiv.norm_map, Real.norm_eq_abs] at this
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  · intro l
    have cs := sum_mul_sq_le_sq_mul_sq univ (fun p => (nn R p l : ℝ)) (fun p => W l p)
    have n : ∑ p, (W l p) ^ 2 = 65 := by
      have h := q_self l
      rw [← K.reflection.inner_map_map, inner_sum_apply] at h
      simpa [Wdef, pow_two] using h
    rw [n] at cs
    linarith


def excess {k : ℕ} (R : Fin k → Box) : ℕ := ∑ p, ∑ l, nn R p l
def moment {k : ℕ} (R : Fin k → Box) : ℕ := ∑ p, ∑ l, (nn R p l) ^ 2

theorem globalMoment {k : ℕ} (R : Fin k → Box) (hk : k ≤ 25) (good : ∀ t, Good (R t))
    (hits : ∀ p l, inc p l = false → 0 < cov R p l) :
    ((1000 - 40 * (k : ℝ)) + (excess R : ℝ)) ^ 2 ≤ 1950 * (moment R : ℝ) := by
  obtain ⟨W, hw, _, cols⟩ := spectral R good hits
  let z := fun l : Fin 30 => ∑ p, (nn R p l : ℝ) * W l p
  have e : (excess R : ℝ) = ∑ p, ∑ l, (nn R p l : ℝ) := by simp [excess]
  have m : (moment R : ℝ) = ∑ l, ∑ p, (nn R p l : ℝ)^2 := by
    simp only [moment, Nat.cast_sum, Nat.cast_pow]
    exact Finset.sum_comm
  rw [sum_comm (f := fun p l => (nn R p l : ℝ) * W l p), ← e] at hw
  have hk' : (k : ℝ) ≤ 25 := by exact_mod_cast hk
  have ep : (0:ℝ) ≤ excess R := Nat.cast_nonneg _
  have h0 : 0 ≤ 1000 - 40 * (k : ℝ) + excess R := by linarith
  have cs := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin 30)) (fun _ => (1:ℝ)) z
  have cs' : (∑ l, z l)^2 ≤ 30 * ∑ l, (z l)^2 := by simpa using cs
  have c := sum_le_sum fun l (_ : l ∈ (univ : Finset (Fin 30))) => cols l
  rw [← mul_sum, ← m] at c
  have h1 : (1000 - 40 * (k : ℝ) + excess R)^2 ≤ (∑ l, z l)^2 :=
    pow_le_pow_left₀ h0 hw 2
  linarith

theorem shallowMoment {k : ℕ} (R : Fin k → Box) (depth : ∀ p l, cov R p l ≤ 2) :
    moment R = excess R := by
  unfold moment excess
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro l _
  have n : nn R p l ≤ 1 := by
    have := depth p l
    unfold nn
    omega
  interval_cases h : nn R p l <;> norm_num

theorem shallow15 {k : ℕ} (hk : k ≤ 15) (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hits : ∀ p l, inc p l = false → 0 < cov R p l) (depth : ∀ p l, cov R p l ≤ 2) :
    162 ≤ excess R := by
  have g := globalMoment R (by omega) good hits
  rw [shallowMoment R depth] at g
  have h : (k : ℝ) ≤ 15 := by exact_mod_cast hk
  have n : (0:ℝ) ≤ excess R := Nat.cast_nonneg _
  have q : (400 + (excess R : ℝ))^2 ≤ (1000 - 40 * (k : ℝ) + excess R)^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  by_contra hn
  have small : excess R ≤ 161 := by omega
  have small' : (excess R : ℝ) ≤ 161 := by exact_mod_cast small
  nlinarith [mul_nonneg (show 0 ≤ 161 - (excess R : ℝ) by linarith)
    (show 0 ≤ 989 - (excess R : ℝ) by linarith)]

end PEqualNP.Outside.L_meta_10025.Moments

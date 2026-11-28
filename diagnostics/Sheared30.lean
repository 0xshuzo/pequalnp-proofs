import PEqualNP.Outside.L_meta_10006

namespace PEqualNP.Outside.L_meta_10007.Sheared30
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators

def pairs : ℕ → ℕ
  | 0 => 0
  | n+1 => pairs n + n

theorem square_count (n : ℕ) : n^2 = n + 2 * pairs n := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (n+1)^2 = n+1+2*(pairs n+n)
    nlinarith only [ih]

theorem square_sum (f : V → ℕ) :
    ∑ j, (f j)^2 = (∑ j, f j) + 2 * ∑ j, pairs (f j) := by
  simp_rw [square_count]
  rw [sum_add_distrib, ← mul_sum]

open scoped RealInnerProductSpace

def sheared (i j : V) : ℤ := if matrix i j then -27 else 7

set_option maxRecDepth 200000 in
set_option maxHeartbeats 3000000 in
theorem gram_literal : ∀ i i' : V, ∑ j, sheared i j * sheared i' j = if i = i' then 5599 else -181 := by decide +kernel

theorem shearInner (c : V → V → ℤ)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 5599 else -181) (i i' : V) :
    ⟪signedRow c i, signedRow c i'⟫ = if i = i' then 5599 else -181 := by
  simp only [PiLp.inner_apply, Real.inner_apply, signedRow_apply]
  by_cases equal : i = i' <;> simp only [equal, ↓reduceIte] <;>
    exact_mod_cast (by simpa [equal] using gram i i')

theorem shearNorm (c : V → V → ℤ)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 5599 else -181) (f : V → ℝ) :
    ‖∑ i, f i • signedRow c i‖ ^ 2 = 5780 * ∑ i, (f i)^2 - 181 * (∑ i, f i)^2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, shearInner c gram]
  have term (i i' : V) :
      f i * (f i' * (if i = i' then 5599 else -181)) =
        (if i = i' then 5780 * (f i)^2 else 0) - 181 * (f i * f i') := by
    by_cases e : i = i'
    · subst i'; simp; ring
    · simp [e]; ring
  simp_rw [term, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← Finset.mul_sum]
  have eq : (∑ i : V, ∑ j : V, 181 * (f i * f j)) = 181 * (∑ i, f i)^2 := by
    calc
      _ = ∑ i : V, 181 * (f i * ∑ j : V, f j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [eq]

theorem shearStats {k : ℕ} (M : V → V → Bool) (c : V → V → ℤ) (R : Fin k → Box)
    (good : ∀ t, Area.Moments.EmptyRectangle M (R t).1 (R t).2)
    (covers : ∀ i j, M i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2)
    (count : ∀ j, (Finset.univ.filter fun i => M i j = false).card = 25)
    (ones : ∀ i j, M i j = false → c i j = 7)
    (gram : ∀ i i', ∑ j, c i j * c i' j = if i = i' then 5599 else -181)
    (j : V) :
    columnWitness c R j j = 7*(25 + (load M R j : ℝ)) ∧
      ‖columnWitness c R j‖^2 = 5780*(25+2*(load M R j : ℝ)+squares M R j)-181*(25+(load M R j : ℝ))^2 := by
  obtain ⟨zsum, zsq⟩ := zeroEntry_sum_sq M count j
  have sumM : (∑ i, (multiplicity R i j : ℝ)) = 25 + load M R j := by
    unfold load
    simp_rw [multiplicity_eq M R good covers, Nat.cast_add, Finset.sum_add_distrib]
    exact_mod_cast congrArg (· + ∑ i, extra M R i j) zsum
  have incidents (i : V) (h : M i j = true) : multiplicity R i j = 0 := by
    rw [multiplicity_eq M R good covers, extra_eq_zero_of_incident M R good h]
    simp [zeroEntry,h]
  constructor
  · unfold columnWitness
    change ev j (∑ i, (multiplicity R i j : ℝ) • signedRow c i) = _
    rw [map_sum, ← sumM, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, ev_apply, signedRow_apply]
    cases h : M i j
    · simp [ones i j h, mul_comm]
    · simp [incidents i h]
  · unfold columnWitness
    rw [shearNorm c gram, sumM]
    have squaresM : (∑ i, (multiplicity R i j : ℝ)^2) =
        25 + 2 * load M R j + squares M R j := by
      have val (i : V) : (multiplicity R i j : ℝ)^2 =
          (zeroEntry M i j : ℝ)^2 + 2 * extra M R i j + (extra M R i j : ℝ)^2 := by
        rw [multiplicity_eq M R good covers, Nat.cast_add]
        cases h : M i j
        · simp [zeroEntry,h]; ring
        · simp [zeroEntry,h, extra_eq_zero_of_incident M R good h]
      simp_rw [val, Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold load squares
      push_cast
      have f : (∑ i, (zeroEntry M i j : ℝ)^2) = 25 := by exact_mod_cast zsq
      rw [f]
    rw [squaresM]

private theorem tangent (n x p : ℝ) (h : 0 < n) (b : x^2 ≤ p*n) :
    820*x ≤ n+168100*p := by
  apply (mul_le_mul_iff_left₀ h).mp
  nlinarith only [sq_nonneg (n-410*x),b]

theorem thirty {k : ℕ} (R : Fin k → Box) (budget : k ≤ 17)
    (good : ∀ t, Area.Moments.EmptyRectangle matrix (R t).1 (R t).2)
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    30 ≤ ∑ j, ∑ i, pairs (extra matrix R i j) := by
  classical
  let K := Submodule.span ℝ (Set.range fun t => ∑ i ∈ (R t).1, signedRow sheared i)
  have dim : Module.finrank ℝ K ≤ k := by
    simpa [K,Set.finrank] using
      (finrank_range_le_card (R:=ℝ) (fun t : Fin k => ∑ i ∈ (R t).1, signedRow sheared i))
  have score (j : V) : (103143 : ℝ) ≤ 11560*(∑ i, pairs (extra matrix R i j) : ℕ) +
      168100*(K.starProjection (basisVector j)) j := by
    obtain ⟨coord,ns⟩ := shearStats matrix sheared R good covers count_table
      (fun i j z => by simp [sheared,z]) gram_literal j
    have nonzero : columnWitness sheared R j ≠ 0 := by
      intro h
      rw [h] at coord
      change (0 : ℝ) = 7*(25+(load matrix R j : ℝ)) at coord
      have pos : (0 : ℝ) ≤ load matrix R j := Nat.cast_nonneg _
      linarith only [pos,coord]
    have pos : 0 < ‖columnWitness sheared R j‖^2 := by positivity
    have b := tangent _ _ _ pos (coord_sq_le K j (columnWitness_mem sheared R j))
    rw [coord,ns] at b
    have qt : squares matrix R j = load matrix R j + 2*(∑ i, pairs (extra matrix R i j)) :=
      square_sum (fun i => extra matrix R i j)
    rw [qt] at b
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at b
    nlinarith only [b, sq_nonneg (362*(load matrix R j : ℝ)-2550)]
  have sums := sum_le_sum (fun j (_ : j ∈ (univ : Finset V)) => score j)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat, trace_projection] at sums
  have dim17 : (Module.finrank ℝ K : ℝ) ≤ 17 := by exact_mod_cast dim.trans budget
  by_contra! small
  have bound : (∑ j, ∑ i, pairs (extra matrix R i j)) ≤ 29 := by omega
  have boundR : (∑ j, (↑(∑ i, pairs (extra matrix R i j)) : ℝ)) ≤ 29 := by exact_mod_cast bound
  linarith only [sums,dim17,boundR]

end PEqualNP.Outside.L_meta_10007.Sheared30

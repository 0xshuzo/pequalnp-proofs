import PEqualNP.Outside.L_meta_10006

namespace PEqualNP.Outside.L_meta_10007.VariancePairs
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

private theorem price (d h z : ℝ) (pos : 0 < z)
    (amount : z = (25+d)^2+125*(d+2*h)-5*d^2) :
    55696*(1-(25+d)^2/z) + (8*d-57)^2 ≤ 21745+4000*h := by
  have tangent : 118*(25+d)-z ≤ (3481*(25+d)^2)/z :=
    (le_div_iff₀ pos).mpr (by nlinarith only [sq_nonneg (59*(25+d)-z)])
  have loss : 3481*(1-(25+d)^2/z) ≤ 3481-118*(25+d)+z := by
    rw [mul_sub, mul_one, ← mul_div_assoc]
    linarith only [tangent]
  calc
    _ ≤ 16*(3481-118*(25+d)+z)+(8*d-57)^2 := by linarith only [loss]
    _ = _ := by rw [amount]; ring

theorem weighted_bound {k : ℕ} (R : Fin k → Box) (budget : k ≤ 17)
    (good : ∀ t, Area.Moments.EmptyRectangle matrix (R t).1 (R t).2)
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    (105649 : ℝ) + (∑ i, (8*(rowLoad matrix R i : ℝ)-57)^2) ≤
      4000*(∑ i, (∑ j, pairs (extra matrix R i j) : ℕ) : ℕ) := by
  have goodT (t : Fin k) : Area.Moments.EmptyRectangle (transposeMatrix matrix) (flip R t).1 (flip R t).2 :=
    fun j hj i hi => good t i hi j hj
  have coverT (j i : V) (h : transposeMatrix matrix j i = false) :
      ∃ t, j ∈ (flip R t).1 ∧ i ∈ (flip R t).2 := by
    obtain ⟨t,hi,hj⟩ := covers i j h
    exact ⟨t,hj,hi⟩
  have onesT (j i : V) (h : transposeMatrix matrix j i = false) : PEqualNP.Outside.L_meta_10006.code i j = 1 := by
    change matrix i j = false at h
    simp [PEqualNP.Outside.L_meta_10006.code,h]
  obtain ⟨den,proj⟩ := row_loss_data R (fun j i => PEqualNP.Outside.L_meta_10006.code i j) goodT coverT row_counts onesT signedData_transpose
  have score (i : V) : 55696 * projectionLoss (rowLoad matrix R i) (∑ j, (extra matrix R i j)^2) +
      (8*(rowLoad matrix R i : ℝ)-57)^2 ≤ 21745+4000*(∑ j, pairs (extra matrix R i j) : ℕ) := by
    let d := rowLoad matrix R i
    let h := ∑ j, pairs (extra matrix R i j)
    let q := ∑ j, (extra matrix R i j)^2
    have qt : q = d+2*h := square_sum (extra matrix R i)
    have rel : (q : ℝ) = (d : ℝ)+2*h := by exact_mod_cast qt
    exact price (d : ℝ) (h : ℝ) _ (den i) (by
      change (25+(d:ℝ))^2+125*(q:ℝ)-5*(d:ℝ)^2 = (25+(d:ℝ))^2+125*((d:ℝ)+2*(h:ℝ))-5*(d:ℝ)^2
      rw [rel])
  have s := sum_le_sum (fun i (_ : i ∈ (univ : Finset V)) => score i)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] at s
  have kk : (k:ℝ) ≤ 17 := by exact_mod_cast budget
  rw [Nat.cast_sum]
  linarith only [s,proj,kk]

theorem twentySeven {k : ℕ} (R : Fin k → Box) (budget : k ≤ 17)
    (good : ∀ t, Area.Moments.EmptyRectangle matrix (R t).1 (R t).2)
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    27 ≤ ∑ i, ∑ j, pairs (extra matrix R i j) := by
  have w := weighted_bound R budget good covers
  have pos : 0 ≤ ∑ i, (8*(rowLoad matrix R i : ℝ)-57)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra! bad
  have small : (∑ i, ∑ j, pairs (extra matrix R i j)) ≤ 26 := by omega
  have cast : ((∑ i, ∑ j, pairs (extra matrix R i j) : ℕ) : ℝ) ≤ 26 := by exact_mod_cast small
  linarith only [w,pos,cast]

end PEqualNP.Outside.L_meta_10007.VariancePairs

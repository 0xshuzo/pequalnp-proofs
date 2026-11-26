import PEqualNP.Outside.L_meta_10006

namespace PEqualNP.Outside.L_meta_10007.Excess
open PEqualNP.Outside.L_meta_10006 Finset
open scoped BigOperators

def excessRow (f : V → ℕ) := ∑ j, (f j - 1)
def price (s : ℕ) : ℤ := 384500 + 103700 * s

theorem squaresOfList (f : V → ℕ) : (∑ j, (f j)^2) ≤ (∑ j, f j)^2 := by
  have h (j : V) : f j ≤ ∑ i, f i := single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (mem_univ j)
  calc
    _ ≤ ∑ j, (∑ i, f i) * f j := sum_le_sum (fun j _ => by rw [pow_two]; exact Nat.mul_le_mul_right _ (h j))
    _ = _ := by rw [← mul_sum, pow_two]

theorem bounds (f : V → ℕ) :
    (∑ j, f j) ≤ 31 + excessRow f ∧
    (∑ j, (f j)^2) ≤ min ((∑ j, f j)^2) ((∑ j, f j) + excessRow f * (excessRow f + 1)) := by
  let a (j : V) := f j - 1
  have val (j : V) : f j ≤ 1 + a j := by dsimp [a]; omega
  have one (j : V) : (f j)^2 = f j + a j + (a j)^2 := by
    cases e : f j with
    | zero => simp [a,e]
    | succ z => simp [a,e]; ring
  have u := sum_le_sum (fun j (_ : j ∈ (univ : Finset V)) => val j)
  have q := squaresOfList a
  constructor
  · simpa [sum_add_distrib,a,excessRow] using u
  · apply le_min (squaresOfList f)
    simp_rw [one, sum_add_distrib]
    change _ ≤ (∑ j, f j) + (∑ j, a j) * ((∑ j, a j) + 1)
    nlinarith only [q]

set_option maxRecDepth 10000 in
theorem priceTable : ∀ (d : Fin 52) (s : Fin 21),
    fits d.val (min (d.val^2) (d.val+s.val*(s.val+1))) (price s.val) = true := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem twentyOne {k : ℕ} (R : Fin k → Box) (budget : k ≤ 17)
    (good : ∀ t, Area.Moments.EmptyRectangle matrix (R t).1 (R t).2)
    (covers : ∀ i j, matrix i j = false → ∃ t, i ∈ (R t).1 ∧ j ∈ (R t).2) :
    21 ≤ ∑ i, excessRow (extra matrix R i) := by
  by_contra fail
  have bound : (∑ i, excessRow (extra matrix R i)) ≤ 20 := by omega
  have goodT (t : Fin k) : Area.Moments.EmptyRectangle (transposeMatrix matrix) (flip R t).1 (flip R t).2 :=
    fun j hj i hi => good t i hi j hj
  have coverT (j i : V) (h : transposeMatrix matrix j i = false) :
      ∃ t, j ∈ (flip R t).1 ∧ i ∈ (flip R t).2 := by
    obtain ⟨t,hi,hj⟩ := covers i j h
    exact ⟨t,hj,hi⟩
  have onesT (j i : V) (h : transposeMatrix matrix j i = false) : code i j = 1 := by
    change matrix i j = false at h
    simp [PEqualNP.Outside.L_meta_10006.code,h]
  obtain ⟨den,proj⟩ := row_loss_data R (fun j i => code i j) goodT coverT row_counts onesT signedData_transpose
  have cost (i : V) : 1000000 * projectionLoss (rowLoad matrix R i) (∑ j, (extra matrix R i j)^2) ≤
      (384500 : ℝ) + 103700 * excessRow (extra matrix R i) := by
    let f := extra matrix R i
    let d := ∑ j, f j
    let s := excessRow f
    have ss : s ≤ 20 := le_trans (single_le_sum (f:=fun j => excessRow (extra matrix R j))
      (fun _ _ => Nat.zero_le _) (mem_univ i)) bound
    have ⟨hd,hu⟩ := bounds f
    have dd : d < 52 := by change d ≤ 31+s at hd; omega
    have tab := priceTable ⟨d,dd⟩ ⟨s,by omega⟩
    have pos := den i
    have pn : (0:ℤ) ≤ rationalDenom d (∑ j, (f j)^2) := by
      have hh : (0 : ℝ) ≤ (rationalDenom d (∑ j, (f j)^2) : ℝ) := by rw [rationalDenom_real]; exact pos.le
      exact_mod_cast hh
    have h := loss_of_numeric_bound d (∑ j, (f j)^2) (price s)
      (fits_sound tab hu (le_refl _) pn) pos
    change 1000000 * projectionLoss d (∑ j, (f j)^2) ≤ (384500 : ℝ) + 103700 * s
    simpa only [price, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] using h
  have sums := sum_le_sum (fun i (_ : i ∈ (univ : Finset V)) => cost i)
  rw [← mul_sum, sum_add_distrib, ← mul_sum] at sums
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at sums
  have bb : (∑ i, (excessRow (extra matrix R i) : ℝ)) ≤ 20 := by exact_mod_cast bound
  have kk : (k : ℝ) ≤ 17 := by exact_mod_cast budget
  linarith

end PEqualNP.Outside.L_meta_10007.Excess

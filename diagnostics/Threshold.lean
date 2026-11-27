import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_912_aux

theorem census_threshold {t : ℕ} (ht : 35 ≤ t) :
    2*(6*t)^2 ≤ 2^(3*t-5) ∧ 32*(6*t)^10*(12*t*(7*t-1)) < 2^(3*t-5) := by
  let C : ℕ := 32*6^10*84
  have hexp (k : ℕ) (hk : 35 ≤ k) : C*k^12 < 2^(3*k-5) := by
    induction k, hk using Nat.le_induction with
    | base => decide +kernel
    | succ k hk ih =>
      have hh : 8*(k+1) ≤ 9*k := by omega
      have hpow := Nat.pow_le_pow_left hh 12
      rw [Nat.mul_pow,Nat.mul_pow] at hpow
      norm_num at hpow
      have hs : (k+1)^12 ≤ 8*k^12 := by omega
      have hr : 3*(k+1)-5 = 3*k-5+3 := by omega
      rw [hr,pow_add]
      calc
        C*(k+1)^12 ≤ C*(8*k^12) := Nat.mul_le_mul_left _ hs
        _ = (C*k^12)*8 := by ring
        _ < _ := Nat.mul_lt_mul_of_pos_right ih (by decide)
  have htop : 12*t*(7*t-1) ≤ 84*t^2 := by
    have hk := Nat.mul_le_mul_left (12*t) (Nat.sub_le (7*t) 1)
    nlinarith
  have hstraight : 32*(6*t)^10*(12*t*(7*t-1)) ≤ C*t^12 := by
    calc
      _ ≤ 32*(6*t)^10*(84*t^2) := Nat.mul_le_mul_left _ htop
      _ = _ := by dsimp [C]; ring
  have hlast := hstraight.trans_lt (hexp t ht)
  refine ⟨?_,hlast⟩
  have ha : 1 ≤ 6*t := by omega
  have hpow : (6*t)^2 ≤ (6*t)^10 := Nat.pow_le_pow_right ha (by decide)
  have hc : 1 ≤ 12*t*(7*t-1) := Nat.mul_pos (by omega) (by omega)
  have hm := Nat.mul_le_mul_left (32*(6*t)^10) hc
  omega

end PEqualNP.Outside.L_lib_912_aux

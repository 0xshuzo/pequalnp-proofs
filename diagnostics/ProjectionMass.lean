import PEqualNP.Defs
namespace Research9350.Mass
open Finset
abbrev V := Fin 21
def board : List Nat := [1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480]
def zeroCell (r c : V) : Bool := !((board.getD r.val 0).testBit c.val)
def column (c r : V) : ℚ := if zeroCell r c then 1 else 0
def dual (c r : V) : ℚ := if zeroCell r c then 1 else -3
set_option maxRecDepth 8192
set_option maxHeartbeats 0
theorem evaluate : ∀ i j : V, (∑ r : V, dual i r * column j r) =
    if i=j then 16 else 0 := by decide +kernel

def seed (j i : V) : ℚ := if j = i then 1 else 0
def u (r i : V) : ℚ := dual i r / 16 + 1/336
def v (c i : V) : ℚ := seed c i - 1/42
def dot (f g : V → ℚ) := ∑ i : V, f i * g i
def energy (f : V → ℚ) := ∑ i : V, (f i)^2
theorem energy_exact : ∀ r c : V, zeroCell r c = true →
    (∑ i : V, (2*u r i-v c i)^2) = (187/112 : ℚ) := by decide +kernel

theorem energy_nonneg (f : V → ℚ) : 0 ≤ energy f :=
  Finset.sum_nonneg fun i _ => sq_nonneg (f i)

theorem contraction (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g)) (f : V → ℚ) :
    energy (P f) ≤ energy f := by
  have eq : energy (P f) = dot f (P f) := by
    simpa only [energy,dot,pow_two] using orth f f
  have split : energy (f - P f) = energy f + energy (P f) - 2 * dot f (P f) := by
    unfold energy dot
    simp only [Pi.sub_apply,mul_sum,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  have pos := energy_nonneg (f-P f)
  linarith

theorem cell_bound (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g))
    (r c : V) (h : zeroCell r c = true) :
    -(187/896 : ℚ) ≤ dot (v c) (P (u r)) := by
  let a := u r
  let b := v c
  have lower := contraction P orth ((2:ℚ) • a - b)
  have disc : energy ((2:ℚ) • a - b) = 187/112 := by
    simpa [energy,a,b] using energy_exact r c h
  have plus := energy_nonneg (P ((2:ℚ) • a + b))
  have split : energy (P ((2:ℚ) • a + b)) - energy (P ((2:ℚ) • a - b)) =
      8 * dot (P b) (P a) := by
    simp only [map_add,map_sub,map_smul,energy,dot,Pi.add_apply,Pi.sub_apply,
      Pi.smul_apply,smul_eq_mul,mul_sum,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    ring
  rw [orth] at split
  change -(187/896 : ℚ) ≤ dot b (P a)
  linarith

-- The linear map is a rational orthogonal projection onto a left kernel.
-- Its trace is the dimension of the space it fixes. The hypotheses record
-- those two linear-algebra facts explicitly.
theorem excess34 (D : V → V → Nat) (P : (V → ℚ) →ₗ[ℚ] (V → ℚ))
    (supp : ∀ r c, zeroCell r c = false → D r c = 0)
    (orth : ∀ f g, dot (P f) (P g) = dot f (P g))
    (large : 7 ≤ ∑ i : V, P (seed i) i)
    (ann : ∀ i : V, P (seed i + ∑ r : V, ∑ c : V, ((D r c : ℚ) * v c i) • u r) = 0) :
    34 ≤ ∑ r : V, ∑ c : V, D r c := by
  have eq (i : V) : P (seed i) i +
      (∑ r : V, ∑ c : V, (D r c : ℚ) * (v c i * P (u r) i)) = 0 := by
    have e := congrFun (ann i) i
    simpa only [map_add,map_sum,map_smul,Pi.add_apply,sum_apply,Pi.smul_apply,
      smul_eq_mul,mul_assoc,Pi.zero_apply] using e
  have traceEq : (∑ i : V, P (seed i) i) +
      ∑ r : V, ∑ c : V, (D r c : ℚ) * dot (v c) (P (u r)) = 0 := by
    have es : (∑ i : V, P (seed i) i) +
        (∑ i : V, ∑ r : V, ∑ c : V, (D r c : ℚ) * (v c i * P (u r) i)) = 0 := by
      rw [← sum_add_distrib]
      simp [eq]
    convert es using 2
    unfold dot
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro _ _
    rw [sum_comm]
  have term (r c : V) : (D r c : ℚ) * (-(187/896 : ℚ)) ≤
      (D r c : ℚ) * dot (v c) (P (u r)) := by
    cases z : zeroCell r c with
    | false => simp [supp r c z]
    | true => exact mul_le_mul_of_nonneg_left (cell_bound P orth r c z) (by positivity)
  have total := sum_le_sum (s := (univ : Finset V)) fun r _ =>
    sum_le_sum (s := (univ : Finset V)) fun c _ => term r c
  simp only [← sum_mul] at total
  by_contra! low
  have weak : ∑ r : V, ∑ c : V, D r c ≤ 33 := by omega
  have small : (∑ r : V, ∑ c : V, (D r c : ℚ)) ≤ 33 := by exact_mod_cast weak
  linarith

end Research9350.Mass

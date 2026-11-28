import PEqualNP.Defs
namespace Research9348.Round
open Finset
abbrev V := Fin 21
abbrev Box := Finset V × Finset V
def board : List Nat := [1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480]
def zero (i j : V) := !((board.getD i.val 0).testBit j.val)
def circ (w : Nat) := (w+2)/3
def fiber (rel : V → V → Bool) (i : V) := univ.filter fun j => rel i j = true
theorem rows : ∀ r, (fiber zero r).card = 16 := by decide +kernel
theorem cols : ∀ c, (fiber (fun i j => zero j i) c).card = 16 := by decide +kernel

theorem roundCounts {m : Nat} (rel : V → V → Bool) (sizes : ∀ r, (fiber rel r).card = 16)
    (B : Fin m → Box) (hit : ∀ i j, rel i j = true → ∃ t, i ∈ (B t).1 ∧ j ∈ (B t).2) :
    126 ≤ ∑ t, (B t).1.card * circ (B t).2.card := by
  classical
  let strip (r : V) (t : Fin m) : Finset V := if r ∈ (B t).1 then (B t).2 else ∅
  let unit (r : V) (t : Fin m) := if r ∈ (B t).1 then circ (B t).2.card else 0
  have atRow (r : V) : 6 ≤ ∑ t, unit r t := by
    have sub : fiber rel r ⊆ univ.biUnion (strip r) := by
      intro j h
      obtain ⟨t,a,b⟩ := hit r j (Finset.mem_filter.mp h).2
      exact Finset.mem_biUnion.mpr ⟨t,mem_univ _,by simpa [strip,a] using b⟩
    have size := Finset.card_le_card sub
    rw [sizes] at size
    have gross := Finset.card_biUnion_le (s := (univ : Finset (Fin m))) (t := strip r)
    have cap : (∑ t, (strip r t).card) ≤ ∑ t, 3 * unit r t := by
      apply Finset.sum_le_sum
      intro t _
      by_cases h : r ∈ (B t).1
      · simp only [strip,unit,if_pos h,circ]
        omega
      · simp [strip,unit,h]
    rw [← Finset.mul_sum] at cap
    omega
  have total := Finset.sum_le_sum (s := (univ : Finset V)) (fun r _ => atRow r)
  change (∑ _ : V, 6) ≤ ∑ r : V, ∑ t : Fin m, unit r t at total
  rw [Finset.sum_comm] at total
  have swap (t : Fin m) : (∑ r : V, unit r t) = (B t).1.card * circ (B t).2.card := by
    classical
    simp [unit, ← Finset.sum_filter]
  simp only [swap] at total
  simpa using total

theorem both {m : Nat} (B : Fin m → Box)
    (hit : ∀ i j, zero i j = true → ∃ t, i ∈ (B t).1 ∧ j ∈ (B t).2) :
    126 ≤ ∑ t, (B t).1.card * circ (B t).2.card ∧
    126 ≤ ∑ t, (B t).2.card * circ (B t).1.card := by
  refine ⟨roundCounts zero rows B hit, ?_⟩
  apply roundCounts (fun i j => zero j i) cols (fun t => ((B t).2,(B t).1))
  intro i j h
  obtain ⟨t,a,b⟩ := hit j i h
  exact ⟨t,b,a⟩

-- Normalized short-side histogram. The variables enumerate the two orientations
-- of 1x16, 2x12, 3x8 and 3x9 in that order.
theorem profile (s u a b c d e f : Nat)
    (length : s+u+a+b+c+d+e+f ≤ 14)
    (mass : 370 ≤ 16*(s+u) + 24*(a+b+c+d) + 27*(e+f))
    (left : 126 ≤ 6*s+16*u+8*a+12*b+9*c+8*d+9*e+9*f)
    (right : 126 ≤ 16*s+6*u+12*a+8*b+8*c+9*d+9*e+9*f) :
    s=0 ∧ u=0 ∧ c=0 ∧ d=0 ∧
      ((a=0 ∧ b=0 ∧ e+f=14) ∨ (a=1 ∧ b=1 ∧ e+f=12)) := by
  have zero : s+u = 0 := by omega
  have few : a+b+c+d ≤ 2 := by omega
  have gate₁ : a+d ≤ 3*b := by omega
  have gate₂ : b+c ≤ 3*a := by omega
  by_cases az : a = 0
  · have bz : b = 0 := by omega
    exact ⟨by omega,by omega,by omega,by omega,Or.inl ⟨az,bz,by omega⟩⟩
  · have bz : 0 < b := by omega
    exact ⟨by omega,by omega,by omega,by omega,Or.inr ⟨by omega,by omega,by omega⟩⟩
end Research9348.Round

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9708.SignedRank

abbrev Vec := Fin 6 → ℤ
def w : ℕ → ℤ
  | 0 => 2
  | n+1 => 2*w n-1

theorem wpos (k : ℕ) : 1 ≤ w k := by
  induction k with
  | zero => decide
  | succ k h => simp only [w]; omega

inductive Source where
  | collision (i j : Fin 6)
  | lower (i : Fin 6)
  | upper (i : Fin 6)
deriving DecidableEq, Fintype

def row : Source → Vec
  | .collision i j => fun t => if t=i ∨ t=j then 1 else 0
  | .lower i => fun t => if t=i then -1 else 0
  | .upper i => fun t => if t=i then 1 else 0

def bound : Source → ℤ
  | .lower _ => 0
  | _ => 1

def Safe (k : ℕ) (a : Vec) (b : ℤ) : Prop :=
  0≤b ∧ (∀ t, a t≤b) ∧ (∀ S : Finset (Fin 6), ∑ t ∈ S, a t ≤ w k*b)

theorem source_safe : ∀ g, Safe 0 (row g) (bound g) := by
  unfold Safe
  decide +kernel

inductive Der : ℕ → Vec → ℤ → Prop where
  | ax (g : Source) : Der 0 (row g) (bound g)
  | lift {k a b} : Der k a b → Der (k+1) a b
  | plus {k a b c f} : Der k a b → Der k c f → Der k (fun t => a t + c t) (b+f)
  | scale {k a b} (q : ℕ) : Der k a b → Der k (fun t => (q:ℤ) * a t) ((q:ℤ)*b)
  | cut {k a b c f} (q : ℤ) (pos : 0<q) : Der k a b →
      (∀ i, a i = q*c i) → q*f ≤ b → b < q*(f+1) → Der (k+1) c f

theorem estimate {k a b} (h : Der k a b) : Safe k a b := by
  induction h with
  | ax g => exact source_safe g
  | @lift k a b h ih =>
    refine ⟨ih.1, ih.2.1, fun S => (ih.2.2 S).trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ ih.1
    have := wpos k
    simp only [w]
    omega
  | plus ha hc ia ic =>
    refine ⟨add_nonneg ia.1 ic.1, fun t => add_le_add (ia.2.1 t) (ic.2.1 t), fun S => ?_⟩
    simpa only [Finset.sum_add_distrib,mul_add] using add_le_add (ia.2.2 S) (ic.2.2 S)
  | @scale k a b q h ih =>
    have qn : (0:ℤ) ≤ q := by positivity
    refine ⟨mul_nonneg qn ih.1, fun t => mul_le_mul_of_nonneg_left (ih.2.1 t) qn, fun S => ?_⟩
    simpa only [← Finset.mul_sum,mul_left_comm] using mul_le_mul_of_nonneg_left (ih.2.2 S) qn
  | @cut k a b c f q pos h eq low high ih =>
    have fn : 0 ≤ f := by
      by_contra! fh
      have neg := mul_nonpos_of_nonneg_of_nonpos (le_of_lt pos) (show f+1≤0 by omega)
      have bn := ih.1
      omega
    have unit : ∀ t, c t ≤ f := by
      intro t
      have ht := ih.2.1 t
      rw [eq t] at ht
      by_contra! bad
      have low' := mul_le_mul_of_nonneg_left (show f+1 ≤ c t by omega) (le_of_lt pos)
      omega
    refine ⟨fn,unit,fun S => ?_⟩
    have old := ih.2.2 S
    simp only [eq, ← Finset.mul_sum] at old
    have wp := wpos k
    have upper := mul_lt_mul_of_pos_left high (show 0<w k by omega)
    have strict : ∑ t ∈ S, c t < w k*(f+1) := by
      by_contra! bad
      have opp := mul_le_mul_of_nonneg_left bad (le_of_lt pos)
      have contra : q*(∑ t ∈ S, c t) < q*(w k*(f+1)) :=
        lt_of_le_of_lt old (by simpa only [mul_left_comm] using upper)
      exact (not_le_of_gt contra) opp
    by_cases z : f=0
    · rw [z,mul_zero]
      exact Finset.sum_nonpos (fun t _ => (unit t).trans_eq z)
    · have extra := mul_le_mul_of_nonneg_left (show 1 ≤ f by omega) (show 0 ≤ w k-1 by omega)
      rw [mul_one] at extra
      simp only [w]
      rw [mul_add,mul_one] at strict
      nlinarith

theorem capacity_needs_three_rounds {k} (h : Der k (fun _ => 1) 1) : 3 ≤ k := by
  have hm := (estimate h).2.2 Finset.univ
  change (∑ _ : Fin 6, (1:ℤ)) ≤ w k * 1 at hm
  have val : (∑ _ : Fin 6, (1:ℤ))=6 := by decide
  rw [val,mul_one] at hm
  by_contra z
  have upper : k≤2 := by omega
  interval_cases k <;> simp [w] at hm

end PEqualNP.Outside.L_meta_9708.SignedRank

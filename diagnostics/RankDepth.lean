import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9708.LocalRank

abbrev Vec := Fin 6 → ℕ

def mass (a : Vec) : ℕ := ∑ i, a i
def weight : ℕ → ℕ
  | 0 => 2
  | n+1 => 2 * weight n - 1

theorem weight_pos (n : ℕ) : 1 ≤ weight n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [weight]; omega

def edge (i j : Fin 6) : Vec :=
  fun t => (if i=t then 1 else 0) + (if j=t then 1 else 0)

inductive Der : ℕ → Vec → ℕ → Prop where
  | ax (i j : Fin 6) (ne : i≠j) : Der 0 (edge i j) 1
  | lift {k a b} : Der k a b → Der (k+1) a b
  | plus {k a b c f} : Der k a b → Der k c f → Der k (fun t => a t + c t) (b+f)
  | scale {k a b} (q : ℕ) : Der k a b → Der k (fun t => q * a t) (q*b)
  | cut {k a b c f} (q : ℕ) (pos : 0<q) : Der k a b →
      (∀ i, a i = q*c i) → q*f ≤ b → b < q*(f+1) → Der (k+1) c f

theorem estimate {k a b} (h : Der k a b) :
    (∀ t, a t ≤ b) ∧ mass a ≤ weight k * b := by
  induction h with
  | ax i j ne =>
    constructor
    · intro t
      by_cases hi : i=t <;> by_cases hj : j=t <;> simp_all [edge]
    · simp [mass, edge, Finset.sum_add_distrib, weight]
  | @lift k a b h ih =>
    refine ⟨ih.1, ih.2.trans (Nat.mul_le_mul_right b ?_)⟩
    have := weight_pos k
    simp only [weight]
    omega
  | plus ha hc ia ic =>
    constructor
    · intro t; exact Nat.add_le_add (ia.1 t) (ic.1 t)
    · simpa only [mass, Finset.sum_add_distrib,Nat.mul_add] using Nat.add_le_add ia.2 ic.2
  | @scale k a b q h ih =>
    constructor
    · exact fun t => Nat.mul_le_mul_left q (ih.1 t)
    · have aux := Nat.mul_le_mul_left q ih.2
      simpa [mass, ← Finset.mul_sum, Nat.mul_left_comm] using aux
  | @cut k a b c f q pos h eq low high ih =>
    have unit : ∀ t, c t ≤ f := by
      intro t
      have ht := ih.1 t
      rw [eq t] at ht
      exact Nat.le_of_lt_succ ((Nat.mul_lt_mul_left pos).mp (lt_of_le_of_lt ht high))
    refine ⟨unit, ?_⟩
    have total : mass a = q * mass c := by
      simp only [mass,eq,Finset.mul_sum]
    have hi := ih.2
    rw [total] at hi
    have wt := weight_pos k
    have more := Nat.mul_lt_mul_of_pos_left high (show 0 < weight k by omega)
    have top : mass c < weight k*(f+1) := by
      apply (Nat.mul_lt_mul_left pos).mp
      exact lt_of_le_of_lt hi (by simpa only [Nat.mul_left_comm] using more)
    by_cases z : f=0
    · subst f
      have vanish : ∀ t, c t=0 := fun t => Nat.eq_zero_of_le_zero (unit t)
      simp [mass,vanish]
    · have extra : weight k-1 ≤ (weight k-1)*f := by
        simpa using Nat.mul_le_mul_left (weight k-1) (show 1≤f by omega)
      have id : weight (k+1) = weight k + (weight k-1) := by
        simp only [weight]; omega
      rw [id,Nat.add_mul]
      rw [Nat.mul_add,Nat.mul_one] at top
      omega

theorem six_clique_needs_three_rounds {k} (h : Der k (fun _ => 1) 1) : 3 ≤ k := by
  have hm := (estimate h).2
  have eq : mass (fun _ => 1) = 6 := by decide
  rw [eq,Nat.mul_one] at hm
  by_contra bad
  have hk : k ≤ 2 := by omega
  interval_cases k <;> simp [weight] at hm

end PEqualNP.Outside.L_meta_9708.LocalRank

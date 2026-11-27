import PEqualNP.Defs

namespace ReserveCycle851

def walk (cap carry : ℕ → ℕ) (s : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k+1, x => min (cap (s+k)) (2*walk cap carry s k x + carry (s+k))

theorem normal (cap carry : ℕ → ℕ) (s k : ℕ) :
    ∃ U C, ∀ x, walk cap carry s (k+1) x = min U (2^(k+1)*x+C) := by
  induction k with
  | zero =>
    exact ⟨cap s, carry s, fun x => by simp [walk]⟩
  | succ k ih =>
    obtain ⟨U,C,h⟩ := ih
    refine ⟨min (cap (s+(k+1))) (2*U+carry (s+(k+1))), 2*C+carry (s+(k+1)), ?_⟩
    intro x
    rw [walk, h, min_assoc]
    congr 1
    rw [pow_succ]
    by_cases hv : U ≤ 2^(k+1)*x+C
    · rw [min_eq_left hv, min_eq_left]
      nlinarith
    · rw [min_eq_right (by omega : 2^(k+1)*x+C ≤ U), min_eq_right]
      · ring
      · nlinarith

theorem cap_normal (cap carry : ℕ → ℕ) (s k E : ℕ)
    (hc : ∀ b, cap b < E) :
    ∃ U C, U < E ∧ ∀ x, walk cap carry s (k+1) x = min U (2^(k+1)*x+C) := by
  obtain ⟨U,C,H⟩ := normal cap carry s k
  refine ⟨min (cap (s+k)) U, C, lt_of_le_of_lt (min_le_left _ _) (hc _), ?_⟩
  intro x
  rw [min_assoc, ← H, min_eq_right]
  exact min_le_left _ _

theorem stabilizes (M U C E u x : ℕ) (hM : 1 ≤ M) (hU : U < E) (hE : E ≤ M^u) :
    (fun y : ℕ => min U (M*y+C))^[u+2] x =
       (fun y : ℕ => min U (M*y+C))^[u+1] x := by
  let f := fun y : ℕ => min U (M*y+C)
  change f^[u+2] x = f^[u+1] x
  conv_lhs => rw [Function.iterate_succ_apply']
  by_cases hz : f x = 0
  · have h0 : f 0 = 0 := by
      dsimp [f] at *
      rcases le_total U (M*x+C) with h|h
      · rw [min_eq_left h] at hz
        simp [hz]
      · rw [min_eq_right h] at hz
        have : C = 0 := by omega
        simp [this]
    have hh : ∀ t, f^[t+1] x = 0 := by
      intro t
      induction t with
      | zero => simpa using hz
      | succ t ih => rw [Function.iterate_succ_apply', ih, h0]
    rw [hh, h0]
  · have hx : 1 ≤ f x := by omega
    have hh : f^[u+1] x = U := by
      have halt : f U = U := by
        dsimp [f]
        rw [min_eq_left]
        nlinarith [Nat.mul_le_mul_right U hM]
      have grow : ∀ t, f^[t+1] x = U ∨ M^t ≤ f^[t+1] x := by
        intro t
        induction t with
        | zero => right; simpa using hx
        | succ t ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with hi|hi
          · exact Or.inl (by rw [hi, halt])
          · by_cases hc : U ≤ M*(f^[t+1] x)+C
            · exact Or.inl (min_eq_left hc)
            · right
              change M^(t+1) ≤ min U (M*(f^[t+1] x)+C)
              rw [min_eq_right (by omega : M*(f^[t+1] x)+C ≤ U), pow_succ]
              nlinarith [Nat.mul_le_mul_left M hi]
      rcases grow u with h|h
      · exact h
      · have hu : f^[u+1] x ≤ U := by
          rw [Function.iterate_succ_apply']
          exact min_le_left _ _
        omega
    rw [hh]
    dsimp [f]
    rw [min_eq_left]
    nlinarith [Nat.mul_le_mul_right U hM]

end ReserveCycle851

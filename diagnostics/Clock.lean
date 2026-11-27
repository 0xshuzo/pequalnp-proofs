import PEqualNP.Defs

namespace Clock851

def clock (B p b : ℕ) : ℕ := if b < B then b else B+(b-B)%p

theorem clock_lt (B b : ℕ) {p : ℕ} (hp : 0<p) : clock B p b < B+p := by
  unfold clock
  split_ifs <;> have h := Nat.mod_lt (b-B) hp <;> omega

theorem clock_early (B p b : ℕ) (h : b < B+p) : clock B p b = b := by
  unfold clock
  split_ifs with hb
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega : b-B < p)]
    omega

theorem clock_period (B p b : ℕ) (hb : B ≤ b) : clock B p (b+p) = clock B p b := by
  simp only [clock, if_neg (by omega : ¬b+p<B), if_neg (by omega : ¬b<B)]
  rw [show b+p-B=b-B+p by omega, Nat.add_mod_right]

theorem clock_eq {α : Type} (f : ℕ → α) (B p : ℕ) (hp : 0<p)
    (hf : ∀ b ≥ B, f (b+p) = f b) (b : ℕ) : f (clock B p b) = f b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b<B+p
    · rw [clock_early _ _ _ hb]
    · have he : b-p+p=b := by omega
      have hc := clock_period B p (b-p) (by omega)
      have hprev := ih (b-p) (by omega)
      have hnext := hf (b-p) (by omega)
      rw [he] at hc hnext
      rw [hc,hprev,hnext]

theorem clock_next (B p b : ℕ) (hp : 0<p) :
    clock B p ((clock B p b)+1) = clock B p (b+1) := by
  apply clock_eq (fun x => clock B p (x+1)) B p hp
  intro d hd
  rw [show d+p+1=d+1+p by omega, clock_period _ _ _ (by omega)]

theorem eventual {α : Type} (f : ℕ → α) (step : ℕ → α → α) (h p : ℕ)
    (hs : ∀ b, f (b+1)=step b (f b))
    (hp : ∀ b ≥ h, step (b+p) = step b) (B : ℕ) (hh : h ≤ B)
    (hB : f (B+p)=f B) : ∀ b ≥ B, f (b+p)=f b := by
  intro b hb
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hb
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    rw [show B+(k+1)+p=B+k+p+1 by omega, show B+(k+1)=B+k+1 by omega,
      hs (B+k+p), hs (B+k), hp _ (by omega), ih]

theorem block (cap carry f : ℕ → ℕ) (h p : ℕ) (step : ∀ b, f (b+1)=min (cap b) (2*f b+carry b))
    (hc : ∀ b ≥ h, cap (b+p)=cap b) (hd : ∀ b ≥ h, carry (b+p)=carry b)
    (walk : ℕ → ℕ → ℕ) (w0 : ∀ x, walk 0 x=x)
    (ws : ∀ k x, walk (k+1) x=min (cap (h+k)) (2*walk k x+carry (h+k))) (t : ℕ) :
    f (h+p*t) = (walk p)^[t] (f h) := by
  have shift (g : ℕ → ℕ) (hg : ∀ b ≥ h, g (b+p)=g b) (k d : ℕ) : g (h+p*k+d)=g (h+d) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show h+p*(k+1)+d = (h+p*k+d)+p by ring, hg _ (by omega), ih]
  have chunk (k d : ℕ) : f (h+p*k+d) = walk d (f (h+p*k)) := by
    induction d with
    | zero => simp [w0]
    | succ d ih =>
      rw [show h+p*k+(d+1)=h+p*k+d+1 by omega, step, ih, ws, shift cap hc, shift carry hd]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show h+p*(t+1)=h+p*t+p by ring, chunk, ih, Function.iterate_succ_apply']

end Clock851

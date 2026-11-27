import PEqualNP.Defs

namespace Layers851

variable {q : ℕ}

def fl (D : ℕ) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) := 2^b * A j / D

def tot (D : ℕ) (A : Fin q → ℕ) (b : ℕ) := ∑ j, fl D A b j

def width (E D : ℕ) (A : Fin q → ℕ) (b : ℕ) := 2^b - tot D A b / E

def carry (D : ℕ) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) :=
  fl D A (b+1) j - 2*fl D A b j

theorem scaled (D E : ℕ) (A : Fin q → ℕ) (hs : ∑ j, A j = D*E) (b : ℕ) :
    tot D A b * D ≤ (2^b*E)*D := by
  calc
    _ = ∑ j, fl D A b j * D := Finset.sum_mul ..
    _ ≤ ∑ j, 2^b * A j := Finset.sum_le_sum fun j _ => Nat.div_mul_le_self _ _
    _ = _ := by rw [← Finset.mul_sum, hs]; ring

theorem scaled' {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (b : ℕ) : tot D A b / E ≤ 2^b := by
  have t := scaled D E A hs b
  have hh := Nat.div_mul_le_self (tot D A b) E
  have h : tot D A b ≤ 2^b*E := Nat.le_of_mul_le_mul_right t hd
  exact Nat.le_of_mul_le_mul_right (hh.trans h) he

theorem zero_width {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (hn : ∃ j, A j % D ≠ 0) : width E D A 0 = 1 := by
  obtain ⟨j0,hj⟩ := hn
  have hlt : tot D A 0 * D < ∑ j, A j := by
    rw [tot, Finset.sum_mul]
    apply Finset.sum_lt_sum
    · intro j _
      simpa [fl] using Nat.div_mul_le_self (A j) D
    · refine ⟨j0,Finset.mem_univ _, ?_⟩
      simp only [fl, pow_zero, one_mul]
      have h := Nat.mod_add_div (A j0) D
      rw [mul_comm D] at h
      omega
  rw [hs, mul_comm D E] at hlt
  have small : tot D A 0 < E := by
    by_contra! h
    exact (not_lt_of_ge (Nat.mul_le_mul_right D h)) hlt
  simp [width, Nat.div_eq_of_lt small]

theorem floor_step {D : ℕ} (hd : 0 < D) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) :
    2*fl D A b j ≤ fl D A (b+1) j := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := Nat.div_mul_le_self (2^b*A j) D
  dsimp [fl]
  rw [pow_succ]
  nlinarith

theorem width_step {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (b : ℕ) : width E D A (b+1) ≤ 2*width E D A b := by
  have h : 2*tot D A b ≤ tot D A (b+1) := by
    unfold tot
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => floor_step hd A b j
  have hh : 2*(tot D A b/E) ≤ tot D A (b+1)/E := by
    apply (Nat.le_div_iff_mul_le he).mpr
    have h0 := Nat.div_mul_le_self (tot D A b) E
    nlinarith
  have hb := scaled' hd he A hs b
  have hb' := scaled' hd he A hs (b+1)
  unfold width
  rw [pow_succ] at *
  omega

theorem period_lift {D h p b : ℕ} (hdv : D ∣ 2^h*(2^p-1)) (hb : h ≤ b) :
    ∃ m, 2^(b+p) = 2^b + m*D := by
  obtain ⟨t,ht⟩ := hdv
  refine ⟨2^(b-h)*t, ?_⟩
  have hx : b-h+h=b := by omega
  have ha : 2^(b-h)*2^h = 2^b := by rw [←pow_add, hx]
  have hp0 : 0 < (2:ℕ)^p := by positivity
  have hp : 2^p-1+1=2^p := by omega
  rw [pow_add, ←ha, ←hp]
  nlinarith [congrArg (2^(b-h) * ·) ht]

theorem floor_shift {D : ℕ} (hd : 0<D) (A : Fin q → ℕ) (b p m : ℕ)
    (hp : 2^(b+p)=2^b+m*D) (j : Fin q) :
    fl D A (b+p) j = fl D A b j + m*A j := by
  unfold fl
  rw [hp, show (2^b + m*D)*A j = 2^b*A j+(m*A j)*D by ring,
    Nat.add_mul_div_right _ _ hd]

theorem periods {D E h p : ℕ} (hd : 0<D) (he : 0<E)
    (hdv : D ∣ 2^h*(2^p-1)) (A : Fin q → ℕ) (hs : ∑ j, A j = D*E)
    (b : ℕ) (hb : h ≤ b) :
    width E D A (b+p) = width E D A b ∧
    tot D A (b+p) % E = tot D A b % E ∧
    ∀ j, carry D A (b+p) j = carry D A b j := by
  obtain ⟨m,hm⟩ := period_lift hdv hb
  have ht : tot D A (b+p) = tot D A b + (m*D)*E := by
    simp only [tot, floor_shift hd A b p m hm, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold width
    rw [hm, ht, Nat.add_mul_div_right _ _ he]
    omega
  · simp [ht]
  · intro j
    have h1 : 2^(b+1+p)=2^(b+1)+(2*m)*D := by
      rw [show b+1+p=b+p+1 by omega, pow_succ, hm, pow_succ]
      ring
    unfold carry
    rw [show b+p+1=b+1+p by omega, floor_shift hd A (b+1) p (2*m) h1,
      floor_shift hd A b p m hm]
    ring_nf
    omega

end Layers851

namespace Reserves851

variable {q : ℕ}

def extN (a : Fin q → ℕ) (i : ℕ) := if h : i < q then a ⟨i,h⟩ else 0

def pref (a : Fin q → ℕ) (k : ℕ) := ∑ i ∈ Finset.range k, extN a i

theorem pref_full (a : Fin q → ℕ) : pref a q = ∑ j, a j := by
  unfold pref
  rw [←Fin.sum_univ_eq_sum_range]
  simp [extN]

theorem pref_step (a : Fin q → ℕ) (i : Fin q) : pref a (i.val+1) = pref a i + a i := by
  simp [pref, Finset.sum_range_succ, extN, i.isLt]

def reserve (cap : ℕ → ℕ) (c : ℕ → Fin q → ℕ) (init : Fin q → ℕ) : ℕ → ℕ → ℕ
  | 0,k => pref init k
  | b+1,k => min (cap (b+1)) (2*reserve cap c init b k + pref (c b) k)

variable (cap : ℕ → ℕ) (c : ℕ → Fin q → ℕ) (init : Fin q → ℕ)

def row (b : ℕ) (j : Fin q) := reserve cap c init b (j.val+1) - reserve cap c init b j.val

theorem bottom (b : ℕ) : reserve cap c init b 0 = 0 := by
  induction b with
  | zero => simp [reserve,pref]
  | succ b ih => simp [reserve,pref,ih]

theorem full (hc0 : (∑ j, init j) = cap 0) (hc : ∀ b, cap (b+1) ≤ 2*cap b + ∑ j, c b j)
    (b : ℕ) : reserve cap c init b q = cap b := by
  induction b with
  | zero => simpa [reserve, pref_full] using hc0
  | succ b ih => simp [reserve, ih, pref_full, min_eq_left (hc b)]

theorem mono (b : ℕ) (j : Fin q) :
    reserve cap c init b j.val ≤ reserve cap c init b (j.val+1) := by
  induction b with
  | zero => simp [reserve, pref_step]
  | succ b ih =>
    simp only [reserve, pref_step]
    omega

theorem prefix_row (b k : ℕ) (hk : k ≤ q) : pref (row cap c init b) k = reserve cap c init b k := by
  induction k with
  | zero => simp [pref, bottom]
  | succ k ih =>
    let j : Fin q := ⟨k, by omega⟩
    change pref (row cap c init b) (j.val+1) = _
    rw [pref_step, show j.val=k by rfl, ih (by omega)]
    have h := mono cap c init b j
    unfold row
    change reserve cap c init b j.val + (reserve cap c init b (j.val+1) - reserve cap c init b j.val) =
      reserve cap c init b (j.val+1)
    omega

theorem row_zero (j : Fin q) : row cap c init 0 j = init j := by
  simp [row,reserve,pref_step]

theorem row_le (b : ℕ) (j : Fin q) : row cap c init (b+1) j ≤ 2*row cap c init b j + c b j := by
  have h := mono cap c init b j
  simp only [row, reserve, pref_step]
  omega

def pay (b : ℕ) (j : Fin q) := 2*row cap c init b j + c b j - row cap c init (b+1) j

theorem balance (b : ℕ) (j : Fin q) :
    pay cap c init b j + row cap c init (b+1) j = 2*row cap c init b j + c b j :=
  Nat.sub_add_cancel (row_le ..)

theorem pay_total (hc0 : (∑ j, init j) = cap 0) (hc : ∀ b, cap (b+1) ≤ 2*cap b + ∑ j, c b j)
    (b : ℕ) : (∑ j, pay cap c init b j) + cap (b+1) = 2*cap b + ∑ j, c b j := by
  have h (d : ℕ) : (∑ j, row cap c init d j) = cap d := by
    rw [←pref_full, prefix_row _ _ _ _ _ le_rfl, full _ _ _ hc0 hc]
  have t := Finset.sum_congr (s := (Finset.univ : Finset (Fin q))) rfl
    (fun j _ => balance cap c init b j)
  simpa only [Finset.sum_add_distrib, ←Finset.mul_sum, h] using t

end Reserves851

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
    rw [pow_succ (2:ℕ) (k+1)]
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

namespace Schedule851
open Layers851 Reserves851 ReserveCycle851 Clock851
variable {q E D h p u : ℕ} (A : Fin q → ℕ)

def cap (b : ℕ) := tot D A b % E
def r (b : ℕ) (j : Fin q) := row (cap (E:=E) (D:=D) A) (carry D A) (fl D A 0) b j
def emit (b : ℕ) (j : Fin q) := pay (cap (E:=E) (D:=D) A) (carry D A) (fl D A 0) b j

theorem layer_id (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (b : ℕ) :
    (2*width E D A b-width E D A (b+1))*E + cap (D:=D) (E:=E) A (b+1)
    = 2*cap (D:=D) (E:=E) A b + ∑ j, carry D A b j := by
  have hf (j) : carry D A b j+2*fl D A b j = fl D A (b+1) j :=
    Nat.sub_add_cancel (floor_step hd ..)
  have hh := Finset.sum_congr (s:=(Finset.univ : Finset (Fin q))) rfl (fun j _ => hf j)
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum, ←tot] at hh
  have hT (x) := Nat.mod_add_div (tot D A x) E
  have hu := scaled' hd he A hs b
  have hv := scaled' hd he A hs (b+1)
  have hw := width_step hd he A hs b
  have hw' := Nat.sub_add_cancel hw
  have hw0 := Nat.sub_add_cancel hu
  have hw1 := Nat.sub_add_cancel hv
  change width E D A b + _ = _ at hw0
  change width E D A (b+1) + _ = _ at hw1
  have H : (2*width E D A b-width E D A (b+1)) + 2*(tot D A b/E) = tot D A (b+1)/E := by
    rw [pow_succ] at hw1
    omega
  unfold cap
  nlinarith [hT b, hT (b+1), congrArg (· * E) H]

theorem cap_init (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (hn : ∃ j, A j%D≠0) :
    (∑ j,fl D A 0 j) = cap (D:=D) (E:=E) A 0 := by
  have h := zero_width hd he A hs hn
  have hu := scaled' hd he A hs 0
  simp only [width, pow_zero] at h hu
  have ht : tot D A 0/E=0 := by omega
  unfold cap
  change tot D A 0 = _
  have hh := Nat.mod_add_div (tot D A 0) E
  simpa [ht] using hh.symm

theorem pay_count (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (hn : ∃ j, A j%D≠0) (b : ℕ) :
    (∑ j,emit (D:=D) (E:=E) A b j) = (2*width E D A b-width E D A (b+1))*E := by
  have hi := cap_init A hd he hs hn
  have hc (d : ℕ) : cap (D:=D) (E:=E) A (d+1) ≤ 2*cap (D:=D) (E:=E) A d+∑ j, carry D A d j := by
    have t := layer_id A hd he hs d
    omega
  have h1 := pay_total _ _ _ hi hc b
  have h2 := layer_id A hd he hs b
  change (∑ j, pay _ _ _ _ j) = _
  omega

theorem eventual_row (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) :
    ∀ b ≥ h+p*(u+1), ∀ j, r (D:=D) (E:=E) A (b+p) j = r (D:=D) (E:=E) A b j := by
  let R := reserve (cap (D:=D) (E:=E) A) (carry D A) (fl D A 0)
  have per (k : ℕ) : ∀ b ≥ h+p*(u+1), R (b+p) k=R b k := by
    let a := fun b => cap (D:=D) (E:=E) A (b+1)
    let c := fun b => pref (carry D A b) k
    have ha (b) (hb : h≤b) : a (b+p)=a b := by
      change tot D A (b+p+1)%E = _
      rw [show b+p+1=b+1+p by omega]
      exact (periods hd he hv A hs (b+1) (by omega)).2.1
    have hc (b) (hb : h≤b) : c (b+p)=c b := by
      have e : carry D A (b+p)=carry D A b := funext (periods hd he hv A hs b hb).2.2
      simp [c,e]
    have eq (b) : R (b+1) k = min (a b) (2*R b k+c b) := rfl
    let W := walk a c h
    obtain ⟨U,C,hU,hW⟩ : ∃ U C, U<E ∧ ∀ x, W p x=min U (2^p*x+C) := by
      obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
      rw [hl]
      exact cap_normal a c h l E (fun _ => Nat.mod_lt _ he)
    have hblk (t) := block a c (fun b => R b k) h p eq ha hc W (fun _ => rfl) (fun _ _ => rfl) t
    have heq : W p = fun x => min U (2^p*x+C) := funext hW
    have hstab := stabilizes (2^p) U C E u (R h k) (by positivity) hU (by simpa [←pow_mul] using hu)
    apply eventual (fun b => R b k) (fun b x => min (a b) (2*x+c b)) h p eq
    · intro b hb; simp [ha b hb, hc b hb]
    · omega
    · rw [show h+p*(u+1)+p=h+p*(u+2) by ring, hblk, hblk, heq]
      exact hstab
  intro b hb j
  change R (b+p) (j.val+1) - R (b+p) j.val = _
  rw [per _ b hb, per _ b hb]
  rfl

theorem periodic_emit (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) (b) (hb : h+p*(u+1)≤b) (j) :
    emit (D:=D) (E:=E) A (b+p) j = emit (D:=D) (E:=E) A b j := by
  have hper := eventual_row A hd he hp hv hu hs
  change 2*r A (b+p) j + carry D A (b+p) j - r A (b+p+1) j = _
  rw [show b+p+1=b+1+p by omega, hper _ hb, hper _ (by omega : h+p*(u+1)≤b+1),
      (periods hd he hv A hs b (by omega)).2.2]
  rfl

end Schedule851

namespace Schedule851
open Layers851 Reserves851
variable {q E D h p u : ℕ} (A : Fin q → ℕ)

noncomputable def debt (b : ℕ) (j : Fin q) : ℝ :=
  ((2^b*A j : ℕ) : ℝ)/D - (fl D A b j:ℝ) + (r (E:=E) (D:=D) A b j:ℝ)

theorem debt_initial (j) : debt (D:=D) (E:=E) A 0 j=(A j:ℝ)/D := by
  simp [debt, r, row_zero]

theorem debt_period (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) (b) (hb : h+p*(u+1) ≤ b) (j) :
    debt (D:=D) (E:=E) A (b+p) j=debt (D:=D) (E:=E) A b j := by
  obtain ⟨m,hm⟩ := period_lift hv (by omega : h≤b)
  unfold debt
  rw [eventual_row A hd he hp hv hu hs b hb j, floor_shift hd A b p m hm j, hm]
  push_cast
  field_simp
  <;> ring

theorem debt_step (hd : 0<D) (b) (j) : 2*debt (D:=D) (E:=E) A b j =
    debt (D:=D) (E:=E) A (b+1) j + (emit (D:=D) (E:=E) A b j : ℝ) := by
  have H := balance (cap (D:=D) (E:=E) A) (carry D A) (fl D A 0) b j
  change emit A b j + r A (b+1) j = 2*r A b j + carry D A b j at H
  have H' : (emit (E:=E) (D:=D) A b j : ℝ) + r (E:=E) (D:=D) A (b+1) j =
      2*(r (E:=E) (D:=D) A b j:ℝ) + carry D A b j := by exact_mod_cast H
  have hg : (carry D A b j : ℝ)+2*(fl D A b j:ℝ)=fl D A (b+1) j := by
    exact_mod_cast Nat.sub_add_cancel (floor_step hd A b j)
  unfold debt
  push_cast
  rw [pow_succ]
  linarith only [H', hg, show (2:ℝ)^b*2*A j/D=2*(2^b*A j/D) by ring]

theorem same_initial (V W pay : ℕ → ℝ) (B p : ℕ) (hp : 0<p)
    (hs : ∀ b, 2*V b=V (b+1)+pay b) (ht : ∀ b, 2*W b=W (b+1)+pay b)
    (hv : V (B+p)=V B) (hw : W (B+p)=W B) : V 0 = W 0 := by
  have step (b) : V b-W b=2^b*(V 0-W 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [pow_succ]
      linarith [hs b, ht b, show (2:ℝ)^b*2*(V 0-W 0)=2*(2^b*(V 0-W 0)) by ring]
  have hh := step (B+p)
  rw [hv,hw,step B,pow_add] at hh
  have hn : (2:ℝ)^p>1 := one_lt_pow₀ (by norm_num) (by omega)
  have hB : 0<(2:ℝ)^B := by positivity
  have hzero : (2:ℝ)^B*((2:ℝ)^p-1)*(V 0-W 0)=0 := by nlinarith only [hh]
  rcases mul_eq_zero.mp hzero with h|h
  · have hnz : 0<(2:ℝ)^B*((2:ℝ)^p-1) := mul_pos hB (by linarith)
    linarith
  · linarith

end Schedule851

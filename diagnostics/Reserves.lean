import PEqualNP.Defs

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

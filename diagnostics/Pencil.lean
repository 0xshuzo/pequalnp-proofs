import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10007.Pencil
open Finset
def rows : List ℕ := [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210, 134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584, 6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504, 1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868, 570949736]
def inc (p : Fin 31) (l : Fin 31) : Bool := (rows.getD p.val 0).testBit l.val
abbrev Box := Finset (Fin 31) × Finset (Fin 31)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 31) (l : Fin 31) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def tp {k : ℕ} (R : Fin k → Box) (p : Fin 31) : Finset (Fin k) := univ.filter fun t => p ∈ (R t).1
def tl {k : ℕ} (R : Fin k → Box) (l : Fin 31) : Finset (Fin k) := univ.filter fun t => l ∈ (R t).2

theorem cov_tp {k : ℕ} (R : Fin k → Box) (p : Fin 31) : ∑ l, cov R p l = ∑ t ∈ tp R p, (R t).2.card := by
  have e : ∀ l, cov R p l = ∑ t ∈ tp R p, if l ∈ (R t).2 then 1 else 0 := by
    intro l; unfold cov tp; rw [← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_tl {k : ℕ} (R : Fin k → Box) (l : Fin 31) : ∑ p, cov R p l = ∑ t ∈ tl R l, (R t).1.card := by
  have e : ∀ p, cov R p l = ∑ t ∈ tl R l, if p ∈ (R t).1 then 1 else 0 := by
    intro p; unfold cov tl
    rw [filter_congr (fun t _ => and_comm), ← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_le_tp {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tp R p).card :=
  card_le_card fun t ht => by simp [tp] at ht ⊢; exact ht.1
theorem cov_le_tl {k : ℕ} (R : Fin k → Box) (p l) : cov R p l ≤ (tl R l).card :=
  card_le_card fun t ht => by simp [tl] at ht ⊢; exact ht.2

theorem swap_tp {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ p, ∑ t ∈ tp R p, f t = ∑ t, (R t).1.card * f t := by
  unfold tp; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp
theorem swap_tl {k : ℕ} (R : Fin k → Box) (f : Fin k → ℕ) : ∑ l, ∑ t ∈ tl R l, f t = ∑ t, (R t).2.card * f t := by
  unfold tl; simp only [sum_filter]; rw [sum_comm]
  exact sum_congr rfl fun t _ => by simp


set_option maxRecDepth 8000 in
theorem countRow : ∀ p, (∑ l : Fin 31, if inc p l = false then 1 else 0 : ℕ) = 25 := by decide +kernel

theorem lowRows {k : ℕ} (hk : k ≤ 17) (R : Fin k → Box)
    (rowsix : ∀ t, (R t).1.card ≤ 6) (colnine : ∀ t, (R t).2.card ≤ 10)
    (hits : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2) :
    22 ≤ (univ.filter fun p => (tp R p).card = 3).card := by
  classical
  have lo (p : Fin 31) : 3 ≤ (tp R p).card := by
    have per (l : Fin 31) : (if inc p l = false then 1 else 0 : ℕ) ≤ cov R p l := by
      split
      · rename_i h
        obtain ⟨t,pt,lt⟩ := hits p l h
        exact card_pos.mpr ⟨t, by simp [pt,lt,cov]⟩
      · omega
    have h := sum_le_sum fun l (_ : l ∈ (univ : Finset (Fin 31))) => per l
    rw [countRow, cov_tp] at h
    have u := sum_le_sum fun t (_ : t ∈ tp R p) => colnine t
    simp only [sum_const, nsmul_eq_mul] at u
    change (∑ t ∈ tp R p, (R t).2.card) ≤ (tp R p).card * 10 at u
    omega
  have upper : ∑ p, (tp R p).card ≤ 100 := by
    have e := swap_tp R (fun _ => 1)
    simp only [Nat.mul_one, sum_const, nsmul_eq_mul] at e
    change (∑ p, (tp R p).card) = ∑ t, (R t).1.card at e
    rw [e]
    have u := sum_le_sum fun t (_ : t ∈ (univ : Finset (Fin k))) => rowsix t
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at u
    change (∑ t, (R t).1.card) ≤ k * 6 at u
    omega
  have per (p : Fin 31) : 4 ≤ (tp R p).card + (if (tp R p).card = 3 then 1 else 0 : ℕ) := by
    have := lo p
    split <;> omega
  have all := sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin 31))) => per p
  rw [sum_add_distrib, ← card_filter] at all
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at all
  omega

-- The second row lies in each of the low point's rectangles except t.
def confined (p x : Fin 31) : Finset (Fin 31) :=
  univ.filter fun q => ∀ l : Fin 31, inc x l = true → inc p l = false → inc q l = false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem five : ∀ p x : Fin 31, p ≠ x → (confined p x).card = 5 := by
  intro p
  fin_cases p <;> decide +kernel

theorem confinement {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hit : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)
    (p x : Fin 31) (t : Fin k)
    (only : ∀ a, p ∈ (R a).1 → a ≠ t → x ∈ (R a).1) :
    (R t).1 ⊆ confined p x := by
  intro q hq
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro l xl pl
  obtain ⟨a,pa,la⟩ := hit p l pl
  have e : a = t := by
    by_contra ne
    have bad := good a x (only a pa ne) l la
    rw [xl] at bad
    contradiction
  subst a
  exact good t q hq l la

theorem twiceSeparated {k : ℕ} (R : Fin k → Box) (good : ∀ t, Good (R t))
    (hit : ∀ p l, inc p l = false → ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2)
    (wide : ∀ t, 6 ≤ (R t).1.card) (p x : Fin 31) (neq : p ≠ x) :
    ∀ t : Fin k, ∃ a, p ∈ (R a).1 ∧ a ≠ t ∧ x ∉ (R a).1 := by
  intro t
  by_contra h
  push_neg at h
  have sub := confinement R good hit p x t h
  have z := card_le_card sub
  rw [five p x neq] at z
  have := wide t
  omega

end PEqualNP.Outside.L_meta_10007.Pencil

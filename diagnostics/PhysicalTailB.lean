import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10025.Low
open Finset
def rows : List ℕ := [34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688]
def inc (p : Fin 25) (l : Fin 30) : Bool := (rows.getD p.val 0).testBit l.val
abbrev Box := Finset (Fin 25) × Finset (Fin 30)
def Good (R : Box) : Prop := ∀ p ∈ R.1, ∀ l ∈ R.2, inc p l = false
def cov {k : ℕ} (R : Fin k → Box) (p : Fin 25) (l : Fin 30) : ℕ :=
  (univ.filter fun t => p ∈ (R t).1 ∧ l ∈ (R t).2).card
def tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : Finset (Fin k) := univ.filter fun t => p ∈ (R t).1
def tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : Finset (Fin k) := univ.filter fun t => l ∈ (R t).2

theorem cov_tp {k : ℕ} (R : Fin k → Box) (p : Fin 25) : ∑ l, cov R p l = ∑ t ∈ tp R p, (R t).2.card := by
  have e : ∀ l, cov R p l = ∑ t ∈ tp R p, if l ∈ (R t).2 then 1 else 0 := by
    intro l; unfold cov tp; rw [← filter_filter, card_filter]
  simp only [e]
  rw [sum_comm]; simp

theorem cov_tl {k : ℕ} (R : Fin k → Box) (l : Fin 30) : ∑ p, cov R p l = ∑ t ∈ tl R l, (R t).1.card := by
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
theorem countRow : ∀ p, (∑ l : Fin 30, if inc p l = false then 1 else 0 : ℕ) = 24 := by decide +kernel


theorem tailLayers {k : ℕ} (R : Fin k → Box) (extra : Fin 25 → Finset (Fin 30))
    (small : ∀ p, (extra p).card ≤ 5)
    (rowsix : ∀ t, (R t).1.card ≤ 6) (colnine : ∀ t, (R t).2.card ≤ 9)
    (hits : ∀ p l, inc p l = false → l ∈ extra p ∨ ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2) :
    (∀ p, 3 ≤ (tp R p).card) ∧
      100 ≤ 6 * k + (univ.filter fun p => (tp R p).card = 3).card := by
  classical
  have lo (p : Fin 25) : 3 ≤ (tp R p).card := by
    have per (l : Fin 30) : (if inc p l = false then 1 else 0 : ℕ) ≤
        cov R p l + (if l ∈ extra p then 1 else 0) := by
      by_cases incf : inc p l = false
      · simp only [incf,if_true]
        rcases hits p l incf with inside | ⟨t, pt, lt⟩
        · simp [inside]
        · have pos : 0 < cov R p l := card_pos.mpr ⟨t, by simp [pt,lt]⟩
          omega
      · simp [incf]
    have h := sum_le_sum fun l (_ : l ∈ (univ : Finset (Fin 30))) => per l
    rw [countRow, sum_add_distrib, cov_tp] at h
    have ex : (∑ l : Fin 30, if l ∈ extra p then 1 else 0 : ℕ) = (extra p).card := by simp
    rw [ex] at h
    have u := sum_le_sum fun t (_ : t ∈ tp R p) => colnine t
    simp only [sum_const, nsmul_eq_mul] at u
    change (∑ t ∈ tp R p, (R t).2.card) ≤ (tp R p).card * 9 at u
    have hx := small p
    omega
  refine ⟨lo, ?_⟩
  have upper : ∑ p, (tp R p).card ≤ k * 6 := by
    have e := swap_tp R (fun _ => 1)
    simp only [Nat.mul_one, sum_const, nsmul_eq_mul] at e
    change (∑ p, (tp R p).card) = ∑ t, (R t).1.card at e
    rw [e]
    have u := sum_le_sum fun t (_ : t ∈ (univ : Finset (Fin k))) => rowsix t
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at u
    change (∑ t : Fin k, (R t).1.card) ≤ k * 6 at u
    omega
  have step (p : Fin 25) : 4 ≤ (tp R p).card +
      (if (tp R p).card = 3 then 1 else 0 : ℕ) := by
    have := lo p
    split <;> omega
  have all := sum_le_sum fun p (_ : p ∈ (univ : Finset (Fin 25))) => step p
  rw [sum_add_distrib, ← card_filter] at all
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at all
  omega

theorem physicalTail {k : ℕ} (R : Fin k → Box) (extra : Fin 25 → Finset (Fin 30))
    (small : ∀ p, (extra p).card ≤ 5)
    (rowsix : ∀ t, (R t).1.card ≤ 6) (colnine : ∀ t, (R t).2.card ≤ 9)
    (hits : ∀ p l, inc p l = false → l ∈ extra p ∨ ∃ t, p ∈ (R t).1 ∧ l ∈ (R t).2) :
    ∃ B : Finset (Fin 25),
      (100 ≤ 6*k+B.card) ∧
      (∀ p ∈ B, (tp R p).card=3) ∧
      (∀ p ∈ B, ∀ l, inc p l=false → l ∉ extra p → ∃ t ∈ tp R p, l ∈ (R t).2) ∧
      (∀ p ∈ B, ∀ q ∈ B, ∀ t ∈ tp R p, q ∈ (R t).1 → t ∈ tp R q) := by
  refine ⟨univ.filter (fun p => (tp R p).card = 3), (tailLayers R extra small rowsix colnine hits).2, ?_, ?_, ?_⟩
  · intro p hp
    exact (mem_filter.mp hp).2
  · intro p _ l zero out
    obtain ⟨t,pt,lt⟩ := (hits p l zero).resolve_left out
    exact ⟨t,by simpa [tp] using pt,lt⟩
  · intro p _ q _ t _ hq
    simpa [tp] using hq
end PEqualNP.Outside.L_meta_10025.Low

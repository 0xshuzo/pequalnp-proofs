import PEqualNP.Defs

namespace HallFrontier177
open Finset
abbrev Rect := Finset (Fin 5) × Finset (Fin 4)

def inside (q r : Rect) : Prop := q.1 ⊆ r.1 ∧ q.2 ⊆ r.2
instance (q r : Rect) : Decidable (inside q r) := by unfold inside; infer_instance

def score (F : Finset Rect) (r : Rect) : Nat := ∑ q ∈ F, if inside q r then 1 else 0

def price (k m : Nat) := (m-1).choose (k-1)

def rowChild (r : Rect) (i : Fin 5) (h : Fin 4) : Rect := (r.1.erase i, r.2.erase h)

def Closed (R : Finset Rect) : Prop :=
  ∀ r ∈ R, 2 ≤ r.1.card →
    (∃ i ∈ r.1, ∀ h ∈ r.2, rowChild r i h ∈ R) ∨
    (∃ h ∈ r.2, ∀ i ∈ r.1, rowChild r i h ∈ R)

theorem child_inside {q r : Rect} {i h} (c : inside q (rowChild r i h)) : inside q r :=
  ⟨fun _ hx => Finset.mem_of_mem_erase (c.1 hx), fun _ hx => Finset.mem_of_mem_erase (c.2 hx)⟩

theorem forbidden {α : Type} [DecidableEq α] (U T : Finset α) (P : α → Prop)
    [DecidablePred P] (ht : T ⊆ U) (no : ∀ a ∈ U, P a → a ∉ T) :
    (∑ a ∈ U, if P a then 1 else 0) ≤ U.card - T.card := by
  rw [← Finset.card_filter, ← Finset.card_sdiff_of_subset ht]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨hu, hp⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_sdiff.mpr ⟨hu, no a hu hp⟩

theorem layer {α : Type} [DecidableEq α] (F : Finset Rect) (r : Rect) (U : Finset α)
    (child : α → Rect) (excluded : Rect → Finset α) (d lower : Nat)
    (parent : ∀ q j, inside q (child j) → inside q r)
    (sub : ∀ q ∈ F, inside q r → excluded q ⊆ U)
    (absent : ∀ q j, inside q (child j) → j ∉ excluded q)
    (diff : ∀ q ∈ F, U.card - (excluded q).card ≤ d)
    (ih : ∀ j ∈ U, lower ≤ score F (child j)) :
    U.card * lower ≤ d * score F r := by
  classical
  calc
    U.card * lower = ∑ _j ∈ U, lower := by simp
    _ ≤ ∑ j ∈ U, score F (child j) := Finset.sum_le_sum ih
    _ = ∑ q ∈ F, ∑ j ∈ U, if inside q (child j) then 1 else 0 := by
      unfold score
      exact Finset.sum_comm
    _ ≤ ∑ q ∈ F, d * (if inside q r then 1 else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases h : inside q r
      · simp only [if_pos h, Nat.mul_one]
        exact (forbidden U (excluded q) (fun j => inside q (child j)) (sub q hq h)
          (fun j _ hx => absent q j hx)).trans (diff q hq)
      · simp only [if_neg h, Nat.mul_zero]
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro j _
        exact if_neg (fun h' => h (parent q j h'))
    _ = d * score F r := by rw [score, Finset.mul_sum]

theorem int_step (m k N : Nat) (hlo : 2 ≤ k) (hkm : k < m) (hm : m ≤ 5)
    (h : (m-1) * price k (m-1) ≤ (m-k) * N) : price k m ≤ N := by
  interval_cases m <;> interval_cases k <;> norm_num [price, Nat.choose] at * <;> omega

theorem frontier (R : Finset Rect) (closed : Closed R)
    (valid : ∀ r ∈ R, r.1.card = r.2.card+1 ∧ r.1.card ≤ 5) (k : Nat) (hk : 2 ≤ k) :
    ∀ m (r : Rect), r ∈ R → r.1.card = m → k ≤ m →
      price k m ≤ score (R.filter (fun q => q.1.card = k)) r := by
  classical
  let F := R.filter (fun q => q.1.card = k)
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro r hr hm hkm
    change price k m ≤ score F r
    have hv := valid r hr
    have rowSize (q : Rect) (hq : q ∈ F) : q.1.card = k := (Finset.mem_filter.mp hq).2
    have colSize (q : Rect) (hq : q ∈ F) : q.2.card = k-1 := by
      have h₁ := (valid q (Finset.mem_filter.mp hq).1).1
      have h₂ := rowSize q hq
      omega
    by_cases stop : m = k
    · have mem : r ∈ F := Finset.mem_filter.mpr ⟨hr, hm.trans stop⟩
      have pr : price k m = 1 := by simp [price, stop]
      rw [pr, score]
      have self : inside r r := ⟨fun _ h => h, fun _ h => h⟩
      simpa [self] using (Finset.single_le_sum (f := fun q => if inside q r then (1:Nat) else 0)
        (fun q _ => Nat.zero_le _) mem)
    · have recu (i h) (hi : i ∈ r.1) (hmem : rowChild r i h ∈ R) :
          price k (m-1) ≤ score F (rowChild r i h) := by
        apply ih (m-1) (by omega) (rowChild r i h) hmem
        · simp [rowChild, Finset.card_erase_of_mem hi, hm]
        · omega
      apply int_step m k _ hk (by omega) (by omega)
      rcases closed r hr (by omega) with ⟨i, hi, ch⟩ | ⟨h, hh, ch⟩
      · have hrow := layer F r r.2 (fun j => rowChild r i j) Prod.snd
          (m-k) (price k (m-1)) (fun _ _ hx => child_inside hx)
          (fun _ _ hx => hx.2) (fun q j hc hj => Finset.notMem_erase _ _ (hc.2 hj))
          (fun q hq => by rw [colSize q hq]; omega)
          (fun j hj => recu i j hi (ch j hj))
        have hcard : r.2.card = m-1 := by omega
        rwa [hcard] at hrow
      · have hcol := layer F r r.1 (fun j => rowChild r j h) Prod.fst
          (m-k) (price k (m-1)) (fun _ _ hx => child_inside hx)
          (fun _ _ hx => hx.1) (fun q j hc hj => Finset.notMem_erase _ _ (hc.1 hj))
          (fun q hq => by rw [rowSize q hq, hm])
          (fun j hj => recu j h hj (ch j hj))
        rw [hm] at hcol
        exact (Nat.mul_le_mul_right _ (Nat.sub_le m 1)).trans hcol

def root : Rect := (Finset.univ, Finset.univ)

theorem root_level (R : Finset Rect) (closed : Closed R) (hr : root ∈ R)
    (valid : ∀ r ∈ R, r.1.card = r.2.card+1 ∧ r.1.card ≤ 5) (k : Nat) (hk : 2 ≤ k)
    (hk5 : k ≤ 5) : price k 5 ≤ (R.filter (fun q => q.1.card = k)).card := by
  have h := frontier R closed valid k hk 5 root hr (by decide) hk5
  have all (q : Rect) : inside q root := ⟨Finset.subset_univ _, Finset.subset_univ _⟩
  simpa [score, all] using h

theorem mixed_hall_line_bound (R : Finset Rect) (closed : Closed R) (hr : root ∈ R)
    (valid : ∀ r ∈ R, r.1.card = r.2.card+1 ∧ r.1.card ≤ 5) :
    157 ≤ 45 + 2*(R.filter (fun r => r.1.card=2)).card +
      6*(R.filter (fun r => r.1.card=3)).card +
      12*(R.filter (fun r => r.1.card=4)).card +
      20*(R.filter (fun r => r.1.card=5)).card := by
  have h2 := root_level R closed hr valid 2 (by decide) (by decide)
  have h3 := root_level R closed hr valid 3 (by decide) (by decide)
  have h4 := root_level R closed hr valid 4 (by decide) (by decide)
  have h5 := root_level R closed hr valid 5 (by decide) (by decide)
  change 4 ≤ _ at h2
  change 6 ≤ _ at h3
  change 4 ≤ _ at h4
  change 1 ≤ _ at h5
  omega

/-- Even crediting each arm with a two-line block, there are 64 derived lines.
    Any reuse of physical lines between blocks must be accounted for separately. -/
theorem aggregate_budget (R : Finset Rect) (closed : Closed R) (hr : root ∈ R)
    (valid : ∀ r ∈ R, r.1.card = r.2.card+1 ∧ r.1.card ≤ 5) :
    109 ≤ 45 + 2*(R.filter (fun r => r.1.card=2)).card +
      4*(R.filter (fun r => r.1.card=3)).card +
      6*(R.filter (fun r => r.1.card=4)).card +
      8*(R.filter (fun r => r.1.card=5)).card := by
  have h2 := root_level R closed hr valid 2 (by decide) (by decide)
  have h3 := root_level R closed hr valid 3 (by decide) (by decide)
  have h4 := root_level R closed hr valid 4 (by decide) (by decide)
  have h5 := root_level R closed hr valid 5 (by decide) (by decide)
  change 4 ≤ _ at h2
  change 6 ≤ _ at h3
  change 4 ≤ _ at h4
  change 1 ≤ _ at h5
  omega

end HallFrontier177

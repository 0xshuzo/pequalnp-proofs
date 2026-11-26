import PEqualNP.Outside.L_meta_3696

namespace PlaneSmall
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3696

theorem bound44 (a b s e : ℕ) (hs : s ≤ 15312) (hab : a + b ≤ s + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    (he : e ^ 2 ≤ a * (e + b * (b - 1))) : e ≤ 44 * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hc : 1 + c - 1 = c := by omega
  rw [hc] at he
  have h0 : 44 * (1 + c + d + c + 1) ≤ e + 43 := by omega
  zify at he h0 hab hs
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hlim : 2 * (1 + (c : ℤ)) + d ≤ 15313 := by linarith
  set B : ℤ := 1 + c with hB
  have hB1 : 1 ≤ B := by linarith
  have hcB : (c : ℤ) = B - 1 := by linarith
  rw [hcB] at he h0
  have h1 : 88 * B + 44 * d - 43 ≤ (e : ℤ) := by linarith
  have h2 : (88 * B + 44 * d - 43) * (87 * B + 43 * d - 43) ≤ (e : ℤ) * (e - (B + d)) := by
    have p1 : 0 ≤ 88 * B + 44 * (d : ℤ) - 43 := by linarith
    have p2 : 0 ≤ 87 * B + 43 * (d : ℤ) - 43 := by linarith
    exact mul_le_mul h1 (by linarith) p2 (by linarith)
  have h3 : (88 * B + 44 * d - 43) * (87 * B + 43 * d - 43) ≤ (B + d) * (B * (B - 1)) := by
    nlinarith [he, h2]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    push_cast at h3 hlim
    have hB2 : B ≤ 7656 := by linarith
    have k1 : 0 ≤ (B - 1) * (7656 - B) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ B * ((B - 1) * (7656 - B)) := mul_nonneg (by linarith) k1
    nlinarith [h3, k2]
  · have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hB2 : B ≤ 7656 := by linarith
    have k1 : 0 ≤ B * (B * (15313 - 2 * B - d)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k2 : 0 ≤ B * ((d - 1) * (7656 - B)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k3 : 0 ≤ (d - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have k4 : 0 ≤ (B - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h3, k1, k2, k3, k4]


variable {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
theorem main (hq : 1 ≤ q) (hI : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hS : Snd I q C) (hsz : C.size ≤ 15312) :
    (Acc I C).card ≤ 44 * C.size := by
  classical
  obtain ⟨S, hScard, hdet⟩ := dep (N + N) C.gates hlen {C.output}
  have hfun : ∀ x : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C x =
      (run C.gates (List.ofFn x)).getD C.output false := fun x => rfl
  have agree : ∀ x y : Fin (N + N) → Bool, (∀ v : Fin (N + N), (v : ℕ) ∈ S → x v = y v) →
      PEqualNP.MetaComplexity.circuitFun (N + N) C x =
        PEqualNP.MetaComplexity.circuitFun (N + N) C y := by
    intro x y h
    rw [hfun, hfun]
    refine hdet _ _ (by simp) (by simp) (fun i hi => ?_) _ (by simp)
    by_cases hin : i < N + N
    · rw [ofFn_getD x ⟨i, hin⟩, ofFn_getD y ⟨i, hin⟩]
      exact h ⟨i, hin⟩ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  set X : Finset (Fin N) := Finset.univ.filter fun p => (p : ℕ) ∈ S with hX
  set Y : Finset (Fin N) := Finset.univ.filter fun l => N + (l : ℕ) ∈ S with hY
  have hXY : X.card + Y.card ≤ C.size + 1 := by
    have e1 : (X.image fun p : Fin N => (p : ℕ)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have e2 : (Y.image fun l : Fin N => N + (l : ℕ)).card = Y.card :=
      Finset.card_image_of_injective _ fun a b h => Fin.ext (by simpa using h)
    have hdis : Disjoint (X.image fun p : Fin N => (p : ℕ)) (Y.image fun l : Fin N => N + (l : ℕ)) := by
      rw [Finset.disjoint_left]
      rintro i hi hj
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨l, -, h⟩ := Finset.mem_image.1 hj
      have := p.2
      omega
    have hsub : (X.image fun p : Fin N => (p : ℕ)) ∪ (Y.image fun l : Fin N => N + (l : ℕ)) ⊆ S := by
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hp).2
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hl).2
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis, e1, e2] at h
    simp only [Finset.card_singleton] at hScard
    exact h.trans hScard
  have hmem : ∀ e ∈ Acc I C, e.1 ∈ X ∧ e.2 ∈ Y := by
    intro e he
    obtain ⟨-, -, ht⟩ := Finset.mem_filter.1 he
    constructor
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.natAdd N e.2)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.castAdd N e.1 := fun hc => hn (by rw [hc] at hv; simpa using hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_left hne, Or.inr⟩
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      have h := single_false I hq hS (Fin.castAdd N e.1)
      rw [← agree (fun x => decide (x = Fin.castAdd N e.1 ∨ x = Fin.natAdd N e.2)) _ ?_, ht] at h
      · cases h
      · intro v hv
        have hne : v ≠ Fin.natAdd N e.2 := fun hc => hn (by rw [hc] at hv; exact hv)
        exact decide_eq_decide.2 ⟨fun h => h.resolve_right hne, Or.inl⟩
  have hc4 : ∀ a a' : Fin N, ∀ b b' : Fin N, a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ Acc I C ∧ (a, b') ∈ Acc I C ∧ (a', b) ∈ Acc I C ∧ (a', b') ∈ Acc I C) := by
    rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
    have g1 := (Finset.mem_filter.1 h1).2.1
    have g2 := (Finset.mem_filter.1 h2).2.1
    have g3 := (Finset.mem_filter.1 h3).2.1
    have g4 := (Finset.mem_filter.1 h4).2.1
    exact hb ((hI a a' ha).unique ⟨g1, g3⟩ ⟨g2, g4⟩)
  rcases (Acc I C).eq_empty_or_nonempty with he | ⟨e0, he0⟩
  · rw [he]; simp
  have hXp : 1 ≤ X.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).1⟩
  have hYp : 1 ≤ Y.card := Finset.card_pos.2 ⟨_, (hmem e0 he0).2⟩
  have f1 : ((X ×ˢ Y).filter fun p => p ∈ Acc I C) = Acc I C := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨fun h => h.2, fun h => ⟨hmem p h, h⟩⟩
  rcases le_total Y.card X.card with hle | hle
  · have h := c4sq (Fin N) (Fin N) (Acc I C) hc4 X Y
    rw [f1] at h
    exact bound44 X.card Y.card C.size _ hsz hXY hYp hle h
  · have h := c4sq (Fin N) (Fin N) ((Acc I C).image Prod.swap) (by
      rintro a a' b b' ha hb ⟨h1, h2, h3, h4⟩
      have sw : ∀ p q : Fin N, (p, q) ∈ (Acc I C).image Prod.swap → (q, p) ∈ Acc I C := by
        intro p q h
        obtain ⟨r, hr, hrs⟩ := Finset.mem_image.1 h
        have : r = (q, p) := by rw [← Prod.swap_swap r, hrs]; rfl
        rwa [← this]
      exact hc4 b b' a a' hb ha ⟨sw _ _ h1, sw _ _ h3, sw _ _ h2, sw _ _ h4⟩) Y X
    have f2 : ((Y ×ˢ X).filter fun p => p ∈ (Acc I C).image Prod.swap) =
        (Acc I C).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 h
      exact ⟨(hmem r hr).2, (hmem r hr).1⟩
    rw [f2, Finset.card_image_of_injective _ Prod.swap_injective] at h
    exact bound44 Y.card X.card C.size _ hsz (by omega) hXp hle h

end PlaneSmall

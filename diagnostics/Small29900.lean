import PEqualNP.Outside.L_meta_9091
import PEqualNP.Outside.L_meta_4451
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


namespace PlanePartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9091.GraphProof PEqualNP.Outside.L_meta_9091.Extra
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
theorem budget (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card+B.card ≤ C.gates.length+1
  omega


lemma strict_budget {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : GraphEval C G)
    (X : Finset (Fin n)) (hdegree : ∀ v ∈ X, ∃ u, G.Adj v u) (ho : C.output ∈ living n C)
    (h3 : ∃ b ∈ living n C, Branch n C b ∧ 3 ≤ (readers n C b).card) :
    open Classical in X.card + ((living n C).filter (Branch n C)).card ≤ C.size := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  obtain ⟨b0, hb0W, hb0_br, hb0_3⟩ := h3
  have hb0B : b0 ∈ B := Finset.mem_filter.mpr ⟨hb0W, hb0_br⟩
  have sub : X.image Fin.val ⊆ W.filter (fun a => a < n) := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u,hu⟩ := hdegree v hv
    exact Finset.mem_filter.mpr ⟨mem_living.mpr ⟨by have := v.isLt; omega,input_live he hu⟩,v.isLt⟩
  have card := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at card
  have partition := Finset.card_filter_add_card_filter_not (s:=W) (fun a => a<n)
  have hW : X.card + S.card ≤ W.card := by
    change (W.filter (fun a => a<n)).card + S.card = W.card at partition
    omega
  have hR : R.card + 1 = W.card := Finset.card_erase_add_one ho
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a - n)
    · intro a ha
      have h : a < n + C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a - n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a - n = b - n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hb0_ne : b0 ≠ C.output := fun h => hoNone (h ▸ (Finset.mem_filter.mp hb0B).2)
  have hlow : R.card + B.card + 1 ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) = R.card := by
      calc _ = ∑ a ∈ W, (if a ≠ C.output then 1 else 0 : ℕ) :=
            Finset.sum_congr rfl (fun a _ => by by_cases h : a = C.output <;> simp [h])
        _ = R.card := by rw [← Finset.sum_filter]; simp [R, Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]; simp [B]
    have hb0W' : b0 ∈ W := hb0W
    have e1 : (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) = 1 := by
      rw [Finset.sum_ite_eq', ite_eq_left hb0W']
    calc R.card + B.card + 1
      _ = (∑ a ∈ W, (if a = C.output then 0 else 1 : ℕ)) +
          (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) +
          (∑ a ∈ W, (if a = b0 then 1 else 0 : ℕ)) := by rw [eR, eB, e1]
      _ = ∑ a ∈ W, ((if a = C.output then 0 else 1) + (if Branch n C a then 1 else 0) + (if a = b0 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ ≤ ∑ a ∈ W, (readers n C a).card := by
        apply Finset.sum_le_sum
        intro a ha
        have hl := (mem_living.1 ha).2
        by_cases hab0 : a = b0
        · subst hab0
          have hbr : Branch n C a := (Finset.mem_filter.mp hb0B).2
          simp only [hb0_ne, ↓reduceIte, hbr]
          omega
        · by_cases heq : a = C.output
          · subst a; simp [hoNone, hab0]
          · by_cases hb : Branch n C a
            · have hb' : 2 ≤ (readers n C a).card := hb
              simpa [heq, hb, hab0] using hb'
            · simpa [heq, hb, hab0] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm : (∑ a ∈ W, (readers n C a).card) =
      ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2 * S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j < n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j < n then 0 else 2 : ℕ)) = 2 * S.card := by
      simp [S, Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change X.card + B.card ≤ C.gates.length
  omega


theorem injective_on (hC : Monotone2 C) (he : GraphEval C G)
    {v w : Fin n} (htwins : v ≠ w → ¬ G.Adj v w → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) (hv : Eligible C v) (hw : Eligible C w)
    (h : firstBranch C v hv = firstBranch C w hw) : v = w := by
  classical
  by_contra hne
  let b := firstBranch C v hv
  have hw_b : firstBranch C w hw = b := h.symm
  have hvtrue : val C (point {v}) b = true :=
    (carries_iff hC).1 (firstBranch_spec v hv).2.1 |>.1
  have hwtrue : val C (point {w}) b = true := by
    rw [← hw_b]
    exact (carries_iff hC).1 (firstBranch_spec w hw).2.1 |>.1
  by_cases hadj : G.Adj v w
  · have hbig : val C (point (insert w ({v} : Finset (Fin n)))) b = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) b hvtrue
    have eq := value_at_branch hw
      (x := point {v}) (y := point (insert w ({v} : Finset (Fin n))))
      (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hvtrue,hbig])
    have hy : val C (point (insert w ({v} : Finset (Fin n)))) C.output = true :=
      (point_pair he w v).2 (G.adj_symm hadj)
    rw [point_single_quiet he v,hy] at eq
    contradiction
  obtain ⟨u,hu⟩ := htwins hne hadj
  have hx : val C (point {v,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hvtrue
  have hy : val C (point {w,u}) b = true := acts_mono hC
    (point_mono (by simp)) b hwtrue
  have hxyz : val C (point (insert w ({v,u} : Finset (Fin n)))) b = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) b hx
  have hEq : (insert w ({v,u} : Finset (Fin n))) = insert v {w,u} :=
    Finset.insert_comm _ _ _
  have e1 := value_at_branch hw
    (x := point {v,u}) (y := point (insert w ({v,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [hw_b,hx,hxyz])
  have e2 := value_at_branch hv
    (x := point {w,u}) (y := point (insert v ({w,u} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm) (by rw [← hEq]; exact hy.trans hxyz.symm)
  have e : val C (point {v,u}) C.output = val C (point {w,u}) C.output :=
    e1.trans (by rw [hEq,e2])
  apply hu
  rw [← point_pair he v u, ← point_pair he w u, e]


set_option maxHeartbeats 4000000 in
theorem strict_cover
    (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (other : ∀ v ∈ X, ∀ w, ∃ u, G.Adj v u ∧ u ≠ w)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (eval : GraphEval C G) :
    ∃ S ⊆ X, (∀ v w, G.Adj v w → v ∈ S ∨ w ∈ S) ∧
      X.card + S.card ≤ C.size + 1 ∧
      (X.card + S.card ≤ C.size ∨ ∀ w ∈ S, ∀ v1 v2 v3,
        v1 ≠ v2 → v1 ≠ v3 → v2 ≠ v3 →
        G.Adj w v1 → G.Adj w v2 → G.Adj w v3 → v1 ∈ S ∨ v2 ∈ S ∨ v3 ∈ S) := by
  classical
  let S := X.filter (Eligible C)
  have hS (v) : v ∈ S ↔ v ∈ X ∧ Eligible C v := by simp [S]
  have degree (v) (hv : v ∈ X) : ∃ w, G.Adj v w := by
    obtain ⟨w,hw,_⟩ := other v hv v
    exact ⟨w,hw⟩
  have twins (v) (hv : v ∈ X) (w) (ne : v ≠ w) (_ : ¬G.Adj v w) :
      ∃ u, ¬(G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a,va⟩ := degree v hv
    obtain ⟨b,vb,ba⟩ := other v hv a
    by_cases wa : G.Adj w a
    · by_cases wb : G.Adj w b
      · exact (square v w a b ne ba.symm va vb wa wb).elim
      · exact ⟨b,fun h => wb (h.mp vb)⟩
    · exact ⟨a,fun h => wa (h.mp va)⟩
  have hits (v w) (vw : G.Adj v w) : v ∈ S ∨ w ∈ S := by
    obtain ⟨a,va,aw⟩ := other v (inX vw) w
    obtain ⟨b,wb,bv⟩ := other w (inX vw.symm) v
    have ab : ¬G.Adj a b := fun e => square v b w a bv.symm aw.symm vw va wb.symm e.symm
    exact (covers_edge hC eval vw va aw wb bv (Or.inr ab)).imp
      (fun h => (hS v).mpr ⟨inX vw,h⟩) (fun h => (hS w).mpr ⟨inX vw.symm,h⟩)
  obtain ⟨a0,b0,ab0⟩ := edge
  have hlt_out := (edge_at_output eval ab0).2
  have houtput : C.output ∈ living n C := mem_living.mpr ⟨hlt_out,ReflTransGen.refl⟩
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f, hu]
  have hf_maps : ∀ u ∈ S, f u ∈ B := by
    intro u hu
    have hs := ((hS u).mp hu).2
    have hb := firstBranch_spec u hs
    have hw := (next_le hb.1).trans_lt hlt_out
    rw [hf u hs]
    exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hw, hb.1⟩, hb.2.2⟩
  have hf_inj : Set.InjOn f S := by
    intro u hu v hv same
    have hsu := ((hS u).mp hu).2
    have hsv := ((hS v).mp hv).2
    rw [hf u hsu, hf v hsv] at same
    exact injective_on hC eval (twins u ((hS u).mp hu).1 v) hsu hsv same
  have hcap : S.card ≤ B.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
  have hbud_raw := budget hC eval X degree houtput
  have hB_card_eq : B.card = (open Classical in ((living n C).filter (Branch n C)).card) := by
    congr 1
  have hbud : X.card + B.card ≤ C.size + 1 := by rw [hB_card_eq]; exact hbud_raw
  refine ⟨S,Finset.filter_subset _ _,hits,by omega,?_⟩
  by_cases good : X.card + S.card ≤ C.size
  · exact Or.inl good
  apply Or.inr
  intro w hwS v1 v2 v3 h12 h13 h23 hw1 hw2 hw3
  by_contra! no
  obtain ⟨hv1,hv2,hv3⟩ := no
  have hBE : B.card = S.card := by omega
  have hB_img : S.image f = B := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
      exact hf_maps u hu
    · rw [Finset.card_image_of_injOn hf_inj, hBE]
  have hB_deg2 : ∀ b ∈ B, (readers n C b).card = 2 := by
    intro b hb
    have hge2 : 2 ≤ (readers n C b).card := (Finset.mem_filter.mp hb).2
    by_contra hne2
    have hge3 : 3 ≤ (readers n C b).card := by omega
    have hstr_raw := strict_budget hC eval X degree houtput
      ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2, hge3⟩
    have hstr : X.card + B.card ≤ C.size := by rw [hB_card_eq]; exact hstr_raw
    omega
  have hwEl : Eligible C w := ((hS w).mp hwS).2
  have hmeet : ∀ v : Fin n, G.Adj w v →
      ∃ m a b g, C.gates[m - n]? = some g ∧ n ≤ m ∧
        LNext n C a m ∧ LNext n C b m ∧
        Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
        (∀ i ∈ g.inputs, i = a ∨ i = b) ∧ ¬ Carries C w m := by
    intro v hwv
    obtain ⟨p, g, a, b, hg, _, _, ha, hb, hva, hwa, hwb, hvb, h2, hwm⟩ := meeting_gate hC eval (G.adj_symm hwv)
    refine ⟨n + p, a, b, g, by simpa using hg, by omega, ha, hb, hva, hwa, hwb, hvb, h2, ?_⟩
    rw [carries_iff hC]
    simp [hwm]
  obtain ⟨m1, a1, b1, g1, hg1, hm1ge, ha1, hb1, hv1a1, hwa1, hwb1, _, h2g1, hwm1⟩ := hmeet v1 hw1
  obtain ⟨m2, a2, b2, g2, hg2, hm2ge, ha2, hb2, hv2a2, hwa2, hwb2, _, h2g2, hwm2⟩ := hmeet v2 hw2
  obtain ⟨m3, a3, b3, g3, hg3, hm3ge, ha3, hb3, hv3a3, hwa3, hwb3, _, h2g3, hwm3⟩ := hmeet v3 hw3
  have hm_ne : ∀ (u1 u2 : Fin n) (m a b c : ℕ) (g : Gate),
      u1 ∉ S → u1 ≠ u2 → G.Adj w u1 → G.Adj w u2 →
      C.gates[m - n]? = some g → n ≤ m →
      LNext n C a m → LNext n C c m →
      Carries C u1 a → ¬ Carries C w a → Carries C w b →
      Carries C u2 c → ¬ Carries C w c →
      (∀ i ∈ g.inputs, i = a ∨ i = b) → False := by
    intro u1 u2 m a b c g u1out hu12 hwu1 hwu2 hgm hmge ham hcm hu1a hwa hwb hu2c hwc h2g
    have hc_in : c ∈ g.inputs := by
      obtain ⟨⟨_, p', g', hg', hm', hmem⟩, _⟩ := hcm
      have hp' : p' = m - n := by omega
      subst hp'
      rw [hgm] at hg'; cases hg'
      exact hmem
    have hca : c = a := by
      rcases h2g c hc_in with rfl | rfl
      · rfl
      · exact (hwc hwb).elim
    rw [hca] at hu2c
    have hu1_not : ¬ Eligible C u1 := fun h => u1out ((hS u1).mpr ⟨inX hwu1.symm,h⟩)
    obtain ⟨w', hu1w', hw'ne⟩ := other u1 (inX hwu1.symm) w
    have hnot_u2w' : ¬ G.Adj u2 w' := fun h =>
      square u1 u2 w w' hu12 hw'ne.symm hwu1.symm hu1w' hwu2.symm h
    let x := point ({u2, w'} : Finset (Fin n))
    let y := point (insert u1 ({u2, w'} : Finset (Fin n)))
    have hax : val C x a = true :=
      acts_mono hC (point_mono (by simp)) a ((carries_iff hC).mp hu2c).1
    have hay : val C y a = true :=
      acts_mono hC (point_mono (Finset.subset_insert _ _)) a hax
    have hpath := singleton_path (live_before ham.1 ham.2) hu1a
    have huniq : ∀ k j j', k < a → Carries C u1 k → LNext n C k j → LNext n C k j' → j = j' :=
      fun k j j' _ => no_eligible_unique hu1_not k j j'
    have hxy_out : val C x C.output = val C y C.output := by
      by_contra hdiff
      rcases influence hpath huniq (fun _ hi => (point_insert hi).symm) ReflTransGen.refl hdiff with bad | bad
      · exact (Nat.not_lt_of_ge (next_le (live_before ham.1 ham.2))) bad.1
      · exact bad.2 (hax.trans hay.symm)
    have hx0 : val C x C.output = false := point_pair_quiet eval hnot_u2w'
    have hy1 : val C y C.output = true := point_contains_edge hC eval (u := u1) (v := w')
      (by simp) (by simp) hu1w'
    exact Bool.false_ne_true (hx0.symm.trans (hxy_out.trans hy1))
  have hm12 : m1 ≠ m2 := fun h => hm_ne v1 v2 m1 a1 b1 a2 g1 hv1 h12 hw1 hw2 hg1 hm1ge ha1 (h ▸ ha2) hv1a1 hwa1 hwb1 hv2a2 hwa2 h2g1
  have hm13 : m1 ≠ m3 := fun h => hm_ne v1 v3 m1 a1 b1 a3 g1 hv1 h13 hw1 hw3 hg1 hm1ge ha1 (h ▸ ha3) hv1a1 hwa1 hwb1 hv3a3 hwa3 h2g1
  have hm23 : m2 ≠ m3 := fun h => hm_ne v2 v3 m2 a2 b2 a3 g2 hv2 h23 hw2 hw3 hg2 hm2ge ha2 (h ▸ ha3) hv2a2 hwa2 hwb2 hv3a3 hwa3 h2g2
  let bw := firstBranch C w hwEl
  have hbw_spec := firstBranch_spec w hwEl
  have hbw_path : Trace n C (Carries C w) w.val bw := singleton_path hbw_spec.1 hbw_spec.2.1
  have hstep_from_bw : ∀ (m b : ℕ), LNext n C b m → Carries C w b → ¬ Carries C w m →
      ∃ r ∈ readers n C bw, Trace n C (Carries C w) r m := by
    intro m b hbm hwb hwm
    have hPm : Trace n C (Carries C w) w.val m :=
      (singleton_path (live_before hbm.1 hbm.2) hwb).tail ⟨hwb, hbm⟩
    rcases align hbw_path (firstBranch_unique w hwEl) m hPm with bad | htail
    · exact (hwm bad.2).elim
    · rcases htail.cases_head with heq | ⟨r, hr, hrest⟩
      · exact (hwm (heq ▸ hbw_spec.2.1)).elim
      · exact ⟨r, mem_readers.mpr hr.2, hrest⟩
  obtain ⟨r1, hr1, hQ1⟩ := hstep_from_bw m1 b1 hb1 hwb1 hwm1
  obtain ⟨r2, hr2, hQ2⟩ := hstep_from_bw m2 b2 hb2 hwb2 hwm2
  obtain ⟨r3, hr3, hQ3⟩ := hstep_from_bw m3 b3 hb3 hwb3 hwm3
  have hbwB : bw ∈ B := by
    have h1 := hf_maps w hwS
    rwa [hf w hwEl] at h1
  have hcard2 : (readers n C bw).card = 2 := hB_deg2 bw hbwB
  have hpig : r1 = r2 ∨ r1 = r3 ∨ r2 = r3 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨h12', h13', h23'⟩ := hnot
    have hsub : ({r1, r2, r3} : Finset ℕ) ⊆ readers n C bw := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({r1, r2, r3} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [h12', h13']), Finset.card_pair h23']
    have hle := Finset.card_le_card hsub
    omega
  have hget_z : ∃ z, bw < z ∧ Live n C z ∧ Carries C w z ∧ Branch n C z := by
    rcases hpig with heq | heq | heq
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ2 hm12 hwm1 hwm2
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ1 hQ3 hm13 hwm1 hwm3
      exact ⟨z, (mem_readers.mp hr1).1.1.trans_le hzle, hzl, hzc, hzb⟩
    · subst heq
      obtain ⟨z, hzle, hzl, hzc, hzb⟩ := trace_split_branch hQ2 hQ3 hm23 hwm2 hwm3
      exact ⟨z, (mem_readers.mp hr2).1.1.trans_le hzle, hzl, hzc, hzb⟩
  obtain ⟨z, hbw_lt_z, hzlive, hzcw, hzb⟩ := hget_z
  have hzB : z ∈ B :=
    Finset.mem_filter.mpr ⟨mem_living.mpr ⟨(next_le hzlive).trans_lt hlt_out, hzlive⟩, hzb⟩
  rw [← hB_img] at hzB
  obtain ⟨u, huS, hfu⟩ := Finset.mem_image.mp hzB
  have huEl : Eligible C u := ((hS u).mp huS).2
  rw [hf u huEl] at hfu
  have huw_ne : u ≠ w := by
    intro h; subst h
    have : firstBranch C u huEl = bw := rfl
    omega
  obtain ⟨a, hua⟩ := degree u ((hS u).mp huS).1
  obtain ⟨b, hub, hba⟩ := other u ((hS u).mp huS).1 a
  have hex_vprime : ∃ v', G.Adj u v' ∧ ¬ G.Adj w v' := by
    by_cases hwa : G.Adj w a
    · by_cases hwb : G.Adj w b
      · exact (square u w a b huw_ne hba.symm hua hub hwa hwb).elim
      · exact ⟨b, hub, hwb⟩
    · exact ⟨a, hua, hwa⟩
  obtain ⟨v', huv', hnot_wv'⟩ := hex_vprime
  have hzw : val C (point {w}) z = true := ((carries_iff hC).mp hzcw).1
  have hz1 : val C (point ({w, v'} : Finset (Fin n))) z = true :=
    acts_mono hC (point_mono (by simp)) z hzw
  have hz2 : val C (point (insert u ({w, v'} : Finset (Fin n)))) z = true :=
    acts_mono hC (point_mono (Finset.subset_insert _ _)) z hz1
  have heq_out := value_at_branch huEl
    (x := point ({w, v'} : Finset (Fin n)))
    (y := point (insert u ({w, v'} : Finset (Fin n))))
    (fun _ hi => (point_insert hi).symm)
    (by rw [hfu, hz1, hz2])
  have hx0 : val C (point ({w, v'} : Finset (Fin n))) C.output = false :=
    point_pair_quiet eval hnot_wv'
  have hy1 : val C (point (insert u ({w, v'} : Finset (Fin n)))) C.output = true :=
    point_contains_edge hC eval (u := u) (v := v') (by simp) (by simp) huv'
  exact Bool.false_ne_true (hx0.symm.trans (heq_out.trans hy1))

end PlanePartial

namespace PlanePartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9091.GraphProof

theorem sparse_charge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (X : Finset (Fin n))
    (inX : ∀ {v w}, G.Adj v w → v ∈ X)
    (deg : ∀ v ∈ X, 3 ≤ (G.neighborSet v).ncard)
    (square : ∀ (v w a b : Fin n), v ≠ w → a ≠ b →
      G.Adj v a → G.Adj v b → G.Adj w a → G.Adj w b → False)
    (edge : ∃ a b, G.Adj a b)
    (hC : Monotone2 C) (eval : GraphEval C G) :
    ∃ S ⊆ X, (∀ v w, G.Adj v w → v ∈ S ∨ w ∈ S) ∧
      X.card + S.card ≤ C.size + 1 ∧
      (X.card + S.card ≤ C.size ∨ X.card < 2*S.card) := by
  classical
  have other (v) (hv : v ∈ X) (w) : ∃ u, G.Adj v u ∧ u ≠ w := by
    have size := deg v hv
    rw [Set.ncard_eq_toFinset_card'] at size
    by_contra! bad
    have sub : (G.neighborSet v).toFinset ⊆ {w} := by
      intro u hu
      exact Finset.mem_singleton.mpr (bad u (by simpa using hu))
    have h := Finset.card_le_card sub
    simp only [Finset.card_singleton] at h
    omega
  obtain ⟨S,sX,hit,base,rest⟩ := strict_cover G C X inX other square edge hC eval
  refine ⟨S,sX,hit,base,?_⟩
  rcases rest with done | two
  · exact Or.inl done
  right
  let Y := X \ S
  have lo (v) (vy : v ∈ Y) : 3 ≤ (S.filter fun w => G.Adj v w).card := by
    have sub : (G.neighborSet v).toFinset ⊆ S.filter fun w => G.Adj v w := by
      intro w hw
      have vw : G.Adj v w := by simpa using hw
      exact Finset.mem_filter.mpr ⟨(hit v w vw).resolve_left (Finset.mem_sdiff.mp vy).2,vw⟩
    have size := deg v (Finset.mem_sdiff.mp vy).1
    rw [Set.ncard_eq_toFinset_card'] at size
    exact size.trans (Finset.card_le_card sub)
  have hi (w) (ws : w ∈ S) : (Y.filter fun v => G.Adj w v).card ≤ 2 := by
    let D := Y.filter fun v => G.Adj w v
    by_contra! bad
    change 2 < D.card at bad
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hu]; omega : 0 < (D.erase u).card)
    obtain ⟨z,hz⟩ := Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem hv,Finset.card_erase_of_mem hu]; omega : 0 < ((D.erase u).erase v).card)
    obtain ⟨vu,vd⟩ := Finset.mem_erase.mp hv
    obtain ⟨zv,zu'⟩ := Finset.mem_erase.mp hz
    obtain ⟨zu,zd⟩ := Finset.mem_erase.mp zu'
    have meet := two w ws u v z vu.symm zu.symm zv.symm (Finset.mem_filter.mp hu).2
      (Finset.mem_filter.mp vd).2 (Finset.mem_filter.mp zd).2
    rcases meet with m|m|m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hu).1).2 m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp vd).1).2 m
    · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp zd).1).2 m
  have swap : (∑ v ∈ Y, (S.filter fun w => G.Adj v w).card) =
      ∑ w ∈ S, (Y.filter fun v => G.Adj w v).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro v _
    by_cases e : G.Adj v w
    · simp [e,e.symm]
    · have e' : ¬G.Adj w v := fun f => e f.symm
      simp [e,e']
  have D := (Finset.sum_le_sum lo).trans (swap.le.trans (Finset.sum_le_sum hi))
  simp only [Finset.sum_const,smul_eq_mul] at D
  have part := Finset.card_sdiff_add_card_eq_card sX
  change Y.card + S.card = X.card at part
  obtain ⟨a,b,ab⟩ := edge
  have pos := Finset.card_pos.mpr ⟨a,inX ab⟩
  omega

theorem cap_math (a b m x y s A : ℕ)
    (xa : m ≤ a*x) (yb : m ≤ b*y) (ca : m ≤ max a b * A)
    (mpos : 0 < m) (size : x+y+A ≤ s+1)
    (strict : x+y+A ≤ s ∨ x+y < 2*A)
    (criterion : a ≤ 44 ∨ b ≤ 44 ∨ a*b ≤ 44*(a+b+min a b)) : m ≤ 44*s := by
  have xp : 0 < x := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at xa
    simp only [Nat.mul_zero,Nat.zero_mul] at xa
    omega
  have yp : 0 < y := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at yb
    simp only [Nat.mul_zero,Nat.zero_mul] at yb
    omega
  have ap : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at xa
    simp only [Nat.mul_zero,Nat.zero_mul] at xa
    omega
  have bp : 0 < b := by
    apply Nat.pos_of_ne_zero
    intro zero
    rw [zero] at yb
    simp only [Nat.mul_zero,Nat.zero_mul] at yb
    omega
  rcases criterion with ha|hb|prod
  · exact xa.trans ((Nat.mul_le_mul_right _ ha).trans (Nat.mul_le_mul_left _ (by omega)))
  · exact yb.trans ((Nat.mul_le_mul_right _ hb).trans (Nat.mul_le_mul_left _ (by omega)))
  have add (u v P L K : ℕ) (uv : u ≤ v) (up : 0<u) (vp : 0<v) (h : u*v ≤ 44*(u+v+u))
      (l : m ≤ u*P) (r : m ≤ v*L) (k : m ≤ v*K) (total : P+L+K ≤ s) : m ≤ 44*s := by
    have s₁ := Nat.mul_le_mul_left m h
    have s₂ := Nat.mul_le_mul_left v l
    have s₃ := Nat.mul_le_mul_left u r
    have s₄ := Nat.mul_le_mul_left u k
    have bound : m*(u*v) ≤ (44*(P+L+K))*(u*v) := by nlinarith only [s₁,s₂,s₃,s₄]
    exact (Nat.le_of_mul_le_mul_right bound (Nat.mul_pos up vp)).trans (Nat.mul_le_mul_left _ total)
  have f (u v P L : ℕ) (uv : u ≤ v) (up : 0<u) (vp : 0<v) (h : u*v ≤ 44*(u+v+u))
      (l : m ≤ u*P) (r : m ≤ v*L) (k : m ≤ v*A) (sz : P+L+A ≤ s+1)
      (st : P+L+A ≤ s ∨ P+L < 2*A) : m ≤ 44*s := by
    rcases st with good|large
    · exact add u v P L A uv up vp h l r k good
    by_cases pl : P ≤ L
    · have pA : P < A := by omega
      exact add u v P L P uv up vp h l r (l.trans (Nat.mul_le_mul_right P uv)) (by omega)
    · have lA : L < A := by omega
      exact add u v P L L uv up vp h l r r (by omega)
  rcases le_total a b with ab|ba
  · exact f a b x y ab ap bp (by simpa [min_eq_left ab] using prod) xa yb
      (by simpa [max_eq_right ab] using ca) size strict
  · exact f b a y x ba bp ap (by simpa only [Nat.mul_comm b a,min_eq_right ba, Nat.add_comm b a] using prod)
      yb xa (by simpa [max_eq_left ba] using ca) (by omega) (by rcases strict with h|h <;> omega)

end PlanePartial

namespace PlanePartial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_9091.GraphProof
open PEqualNP.Outside.L_meta_9091.Plane
open PEqualNP.Outside.L_meta_9091

open Finset
private theorem incidenceSquare {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) := by
  classical
  let neighbors (l : Fin N) := P.filter fun p => (p, l) ∈ E
  have count : E.card = ∑ l ∈ L, (neighbors l).card := by
    rw [← Finset.card_sigma]
    apply Finset.card_nbij' (fun e => ⟨e.2, e.1⟩) (fun e => (e.2, e.1))
    · intro e he
      exact mem_sigma.mpr ⟨(ends e he).2, mem_filter.mpr ⟨(ends e he).1, he⟩⟩
    · exact fun e he => (mem_filter.mp (mem_sigma.mp he).2).2
    · exact fun _ _ => rfl
    · exact fun _ _ => rfl
  let triples := L.sigma fun l => (neighbors l).offDiag
  have pairs_le : triples.card ≤ P.offDiag.card := by
    apply Finset.card_le_card_of_injOn (fun t => t.2)
    · intro t ht
      obtain ⟨ha, hb, hab⟩ := mem_offDiag.mp (mem_sigma.mp ht).2
      exact mem_offDiag.mpr ⟨(mem_filter.mp ha).1, (mem_filter.mp hb).1, hab⟩
    · intro ⟨u, a, b⟩ hu ⟨v, c, d⟩ hv heq
      change (a, b) = (c, d) at heq
      cases heq
      obtain ⟨hau, hbu, hab⟩ := mem_offDiag.mp (mem_sigma.mp hu).2
      obtain ⟨hav, hbv, _⟩ := mem_offDiag.mp (mem_sigma.mp hv).2
      cases unique a b u v hab (mem_filter.mp hau).2 (mem_filter.mp hbu).2
        (mem_filter.mp hav).2 (mem_filter.mp hbv).2
      rfl
  have squares : (∑ l ∈ L, (neighbors l).card ^ 2) = triples.card + E.card := by
    rw [count]
    simp only [triples, card_sigma, offDiag_card, ← sum_add_distrib]
    exact sum_congr rfl fun l _ => by rw [Nat.sub_add_cancel (Nat.le_mul_self _), pow_two]
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq L (fun _ => 1 : Fin N → ℕ)
    (fun l => (neighbors l).card)
  simp only [one_mul, one_pow, sum_const, Nat.nsmul_eq_mul, mul_one, ← count, squares] at cauchy
  rw [pow_two] at cauchy
  rw [offDiag_card, ← Nat.mul_sub_one] at pairs_le
  exact cauchy.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right pairs_le _))

private theorem incidenceBounds {N : ℕ} (E : Finset (Fin N × Fin N)) (P L : Finset (Fin N))
    (ends : ∀ e ∈ E, e.1 ∈ P ∧ e.2 ∈ L)
    (unique : ∀ (a b u v : Fin N), a ≠ b →
      (a, u) ∈ E → (b, u) ∈ E → (a, v) ∈ E → (b, v) ∈ E → u = v) :
    E.card ≤ P.card * L.card ∧
    E.card * E.card ≤ L.card * (P.card * (P.card - 1) + E.card) ∧
    E.card * E.card ≤ P.card * (L.card * (L.card - 1) + E.card) := by
  refine ⟨?_, incidenceSquare E P L ends unique, ?_⟩
  · rw [← card_product]
    exact card_le_card fun e he => mem_product.mpr (ends e he)
  · let rev := E.map (Equiv.prodComm _ _).toEmbedding
    have mem_rev (a b : Fin N) : (a, b) ∈ rev ↔ (b, a) ∈ E := mem_map_equiv
    have swapEnds : ∀ e ∈ rev, e.1 ∈ L ∧ e.2 ∈ P := by
      rintro ⟨a, b⟩ he
      exact (ends _ ((mem_rev a b).mp he)).symm
    have swapUnique (a b u v : Fin N) (hab : a ≠ b) (hau : (a, u) ∈ rev)
        (hbu : (b, u) ∈ rev) (hav : (a, v) ∈ rev) (hbv : (b, v) ∈ rev) : u = v := by
      by_contra hne
      exact hab (unique u v a b hne ((mem_rev _ _).mp hau) ((mem_rev _ _).mp hav)
        ((mem_rev _ _).mp hbu) ((mem_rev _ _).mp hbv))
    simpa only [rev, card_map] using incidenceSquare rev L P swapEnds swapUnique

theorem bound55 (a b s e : ℕ) (hs : s ≤ 23980) (hab : a + b ≤ s + 1) (hb : 1 ≤ b) (hba : b ≤ a)
    (he : e ^ 2 ≤ a * (e + b * (b - 1))) : e ≤ 55 * s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hb
  have hc : 1 + c - 1 = c := by omega
  rw [hc] at he
  have h0 : 55 * (1 + c + d + c + 1) ≤ e + 54 := by omega
  zify at he h0 hab hs
  have hc0 : (0 : ℤ) ≤ c := by positivity
  have hd0 : (0 : ℤ) ≤ d := by positivity
  have hlim : 2 * (1 + (c : ℤ)) + d ≤ 23981 := by linarith
  set B : ℤ := 1 + c with hB
  have hB1 : 1 ≤ B := by linarith
  have hcB : (c : ℤ) = B - 1 := by linarith
  rw [hcB] at he h0
  have h1 : 110 * B + 55 * d - 54 ≤ (e : ℤ) := by linarith
  have h2 : (110 * B + 55 * d - 54) * (109 * B + 54 * d - 54) ≤ (e : ℤ) * (e - (B + d)) := by
    have p1 : 0 ≤ 110 * B + 55 * (d : ℤ) - 54 := by linarith
    have p2 : 0 ≤ 109 * B + 54 * (d : ℤ) - 54 := by linarith
    exact mul_le_mul h1 (by linarith) p2 (by linarith)
  have h3 : (110 * B + 55 * d - 54) * (109 * B + 54 * d - 54) ≤ (B + d) * (B * (B - 1)) := by
    nlinarith [he, h2]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    push_cast at h3 hlim
    have hB2 : B ≤ 11990 := by linarith
    have k1 : 0 ≤ (B - 1) * (11990 - B) := mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ B * ((B - 1) * (11990 - B)) := mul_nonneg (by linarith) k1
    nlinarith [h3, k2]
  · have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have hB2 : B ≤ 11990 := by linarith
    have k1 : 0 ≤ B * (B * (23981 - 2 * B - d)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k2 : 0 ≤ B * ((d - 1) * (11990 - B)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have k3 : 0 ≤ (d - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    have k4 : 0 ≤ (B - 1) * ((d : ℤ) - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [h3, k1, k2, k3, k4]

set_option maxHeartbeats 3500000 in
theorem dense_small (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (hu : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (legal : IsAO2 (N+N) C)
    (hRej : ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q →
      (¬∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) → circuitFun (N+N) C x=false) :
    let E := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧
      circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N e.1 ∨ k=Fin.natAdd N e.2))=true
    C.size ≤ 29900 →
      (∀ v : Fin (N+N), let d := (E.filter fun e => v=Fin.castAdd N e.1 ∨ v=Fin.natAdd N e.2).card
          d=0 ∨ 3 ≤ d) → E.card ≤ 44*C.size := by
  classical
  intro E small dense
  let pt : Fin N → Fin (N+N) := Fin.castAdd N
  let ln : Fin N → Fin (N+N) := Fin.natAdd N
  let J := fun p l : Fin N => (p,l) ∈ E
  let G := graph J
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  let X := P.image pt ∪ L.image ln
  let owns := fun (v : Fin (N+N)) (e : Fin N × Fin N) => v=pt e.1 ∨ v=ln e.2
  let star := fun (v : Fin (N+N)) => E.filter (owns v)
  let op := fun (v : Fin (N+N)) (e : Fin N × Fin N) => if v=pt e.1 then ln e.2 else pt e.1
  have apart (p l) : pt p ≠ ln l := left_ne_right _ _
  have pinj : Function.Injective pt := Fin.castAdd_injective N N
  have linj : Function.Injective ln := Fin.natAdd_injective N N
  have memE (p l : Fin N) : J p l ↔ I p l ∧
      circuitFun (N+N) C (fun k => decide (k=Fin.castAdd N p ∨ k=Fin.natAdd N l))=true := by
    change (p,l) ∈ Finset.univ.filter _ ↔ _
    simp
  have repr {p l : Fin N} {a b : Fin (N+N)}
      (hp : Fin.castAdd N p = a ∨ Fin.castAdd N p = b) (hl : Fin.natAdd N l=a ∨ Fin.natAdd N l=b) :
      (fun z : Fin (N + N) => decide (z = a ∨ z = b)) =
          (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) := by
    funext z
    have hne : Fin.castAdd N p ≠ Fin.natAdd N l := left_ne_right p l
    rcases hp with rfl | rfl <;> rcases hl with h2 | h2
    · exact (hne h2.symm).elim
    · subst h2; rfl
    · subst h2; simp [or_comm]
    · exact (hne h2.symm).elim
  have eval : GraphEval C G := by
    intro a b
    have hfn : point ({a, b} : Finset (Fin (N + N))) = fun z => decide (z = a ∨ z = b) := by
      funext z; simp [point]
    change circuitFun (N + N) C (point {a, b}) = true ↔ G.Adj a b
    rw [hfn]
    constructor
    · intro ht
      have old : (graph I).Adj a b := by
        by_contra hnot
        have hcnt : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } ≤ q := by
          have hle2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card ≤ 2 := by
            have hsub : Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b) ⊆
                (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)) ∪
                (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)) := by
              intro l hl
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
              exact hl
            have hc1 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a)).card ≤ 1 := by
              rw [Finset.card_le_one]
              intro l1 hl1 l2 hl2
              exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
            have hc2 : (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = b)).card ≤ 1 := by
              rw [Finset.card_le_one]
              intro l1 hl1 l2 hl2
              exact (Fin.natAdd_inj N).mp ((Finset.mem_filter.mp hl1).2.trans (Finset.mem_filter.mp hl2).2.symm)
            exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
          have hceq : Fintype.card { l : Fin N // decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true } =
              (Finset.univ.filter (fun l : Fin N => Fin.natAdd N l = a ∨ Fin.natAdd N l = b)).card := by
            rw [← Fintype.card_coe]
            apply Fintype.card_congr
            apply Equiv.subtypeEquivRight
            intro l; simp
          omega
        have hno : ¬ ∃ p l : Fin N, I p l ∧
            decide (Fin.castAdd N p = a ∨ Fin.castAdd N p = b) = true ∧
            decide (Fin.natAdd N l = a ∨ Fin.natAdd N l = b) = true := by
          rintro ⟨p, l, hpl, hp, hl⟩
          simp only [decide_eq_true_eq] at hp hl
          exact hnot ⟨p, l, hpl, hp, hl⟩
        have hf := hRej (fun z => decide (z = a ∨ z = b)) hcnt hno
        rw [hf] at ht
        exact Bool.false_ne_true ht
      obtain ⟨p,l,hi,hp,hl⟩ := old
      exact ⟨p,l,(memE p l).mpr ⟨hi,(repr hp hl) ▸ ht⟩,hp,hl⟩
    · rintro ⟨p,l,h,hp,hl⟩
      rw [repr hp hl]
      exact ((memE p l).mp h).2
  have asOld {v w} (e : G.Adj v w) : (graph I).Adj v w := by
    obtain ⟨p,l,hi,hp,hl⟩ := e
    exact ⟨p,l,((memE _ _).mp hi).1,hp,hl⟩
  have square (v w c d) (vw : v ≠ w) (cd : c ≠ d)
      (vc : G.Adj v c) (vd : G.Adj v d) (wc : G.Adj w c) (wd : G.Adj w d) : False :=
    no_square I hu v w c d vw cd (asOld vc) (asOld vd) (asOld wc) (asOld wd)
  have leftX (e : Fin N × Fin N) (he : e ∈ E) : pt e.1 ∈ X :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩,rfl⟩)
  have rightX (e : Fin N × Fin N) (he : e ∈ E) : ln e.2 ∈ X :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩,rfl⟩)
  have inX {v w} (edge : G.Adj v w) : v ∈ X := by
    obtain ⟨p,l,hi,hp,hl⟩ := edge
    rcases hp with pV|pW
    · exact pV ▸ leftX (p,l) hi
    · rcases hl with lV|lW
      · exact lV ▸ rightX (p,l) hi
      · exact (apart p l (pW.trans lW.symm)).elim
  have sides (v) (e : Fin N × Fin N) (o : owns v e) :
      (v = pt e.1 ∧ op v e = ln e.2) ∨ (v = ln e.2 ∧ op v e = pt e.1) := by
    rcases o with hp|hl
    · exact Or.inl ⟨hp,if_pos hp⟩
    · exact Or.inr ⟨hl,if_neg (fun hp => apart _ _ (hp.symm.trans hl))⟩
  have opInj (v) : Set.InjOn (op v) (star v) := by
    intro e he f hf eq
    rcases sides v e (Finset.mem_filter.mp he).2 with ⟨ve,oe⟩|⟨ve,oe⟩ <;>
      rcases sides v f (Finset.mem_filter.mp hf).2 with ⟨vf,of'⟩|⟨vf,of'⟩
    · exact Prod.ext (pinj (ve.symm.trans vf)) (linj (oe.symm.trans (eq.trans of')))
    · exact (apart _ _ (ve.symm.trans vf)).elim
    · exact (apart _ _ (vf.symm.trans ve)).elim
    · exact Prod.ext (pinj (oe.symm.trans (eq.trans of'))) (linj (ve.symm.trans vf))
  have deg (v) (vx : v ∈ X) : 3 ≤ (G.neighborSet v).ncard := by
    have witness : (star v).Nonempty := by
      rcases Finset.mem_union.mp vx with h|h <;> obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
        exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inl rfl⟩⟩
      · obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
        exact ⟨e,Finset.mem_filter.mpr ⟨he,Or.inr rfl⟩⟩
    have d : 3 ≤ (star v).card := (dense v).resolve_left (Nat.ne_of_gt (Finset.card_pos.mpr witness))
    rw [Set.ncard_eq_toFinset_card']
    apply d.trans
    apply Finset.card_le_card_of_injOn (op v) _ (opInj v)
    intro e he
    have je := (Finset.mem_filter.mp he).1
    rcases sides v e (Finset.mem_filter.mp he).2 with ⟨ve,oe⟩|⟨ve,oe⟩
    · rw [oe,ve]
      exact Set.mem_toFinset.mpr ((adj_lr J _ _).mpr je)
    · rw [oe,ve]
      exact Set.mem_toFinset.mpr ((adj_rl J _ _).mpr je)
  by_cases no : E = ∅
  · simp [no]
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr no
  have hC : Monotone2 C := fun g hg => ⟨legal.1 g hg,(legal.2.2 g hg).le⟩
  obtain ⟨S,sX,cover,base,strict⟩ := sparse_charge G C X inX deg square
    ⟨pt e.1,ln e.2,(adj_lr J _ _).mpr he⟩ hC eval
  have dis : Disjoint (P.image pt) (L.image ln) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨p,_,pV⟩ := Finset.mem_image.mp hv
    obtain ⟨l,_,lV⟩ := Finset.mem_image.mp hw
    exact apart _ _ (pV.trans lV.symm)
  have cardX : X.card = P.card + L.card := by
    rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ pinj,Finset.card_image_of_injective _ linj]
  have mb := Finset.card_pos.mpr ⟨e,he⟩
  have pp : 0 < P.card := Finset.card_pos.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  have lp : 0 < L.card := Finset.card_pos.mpr ⟨_,Finset.mem_image.mpr ⟨e,he,rfl⟩⟩
  have B := incidenceBounds E P L (fun z hz => ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩)
    (fun i j u v ij iu ju iv jv => (hu i j ij).unique
      ⟨((memE i u).mp iu).1,((memE j u).mp ju).1⟩ ⟨((memE i v).mp iv).1,((memE j v).mp jv).1⟩)
  by_cases few : 5*X.card ≤ 4*C.size
  · have smallX : X.card ≤ 23980 := by omega
    have m55 : E.card ≤ 55*X.card := by
      rcases le_total L.card P.card with le|le
      · apply bound55 P.card L.card X.card _ smallX (by omega) lp le
        simpa [pow_two,Nat.add_comm] using B.2.2
      · apply bound55 L.card P.card X.card _ smallX (by omega) pp le
        simpa [pow_two,Nat.add_comm] using B.2.1
    omega
  let H := (S ×ˢ X).filter fun z => G.Adj z.1 z.2
  let dest (z : Fin N × Fin N) : Fin (N+N) × Fin (N+N) :=
    if pt z.1 ∈ S then (pt z.1,ln z.2) else (ln z.2,pt z.1)
  have before : E.card ≤ H.card := by
    apply Finset.card_le_card_of_injOn dest
    · intro z h
      have edge : G.Adj (pt z.1) (ln z.2) := (adj_lr J _ _).mpr h
      by_cases l : pt z.1 ∈ S
      · simpa only [dest,if_pos l] using (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨l,rightX z h⟩,edge⟩ : (pt z.1,ln z.2) ∈ H)
      · have r := (cover _ _ edge).resolve_left l
        simpa only [dest,if_neg l] using (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨r,leftX z h⟩,edge.symm⟩ : (ln z.2,pt z.1) ∈ H)
    · intro z hz u hu eq
      by_cases zh : pt z.1 ∈ S <;> by_cases uh : pt u.1 ∈ S <;> simp only [dest,zh,uh,if_true,if_false] at eq
      · exact Prod.ext (pinj (congrArg Prod.fst eq)) (linj (congrArg Prod.snd eq))
      · exact (apart _ _ (congrArg Prod.fst eq)).elim
      · exact (apart _ _ (congrArg Prod.snd eq)).elim
      · exact Prod.ext (pinj (congrArg Prod.snd eq)) (linj (congrArg Prod.fst eq))
  have incidence := incidenceSquare H S X (fun z hz => Finset.mem_product.mp (Finset.mem_filter.mp hz).1)
    (fun a b u v ab au bu av bv => by
      by_contra uv
      exact square a b u v ab uv (Finset.mem_filter.mp au).2 (Finset.mem_filter.mp av).2
        (Finset.mem_filter.mp bu).2 (Finset.mem_filter.mp bv).2)
  have sp : 0 < S.card := by
    rcases cover _ _ ((adj_lr J e.1 e.2).mpr he) with h|h
    · exact Finset.card_pos.mpr ⟨_,h⟩
    · exact Finset.card_pos.mpr ⟨_,h⟩
  have XS : X.card ≤ C.size := by omega
  by_cases mini : C.size ≤ 15312
  · apply PlaneSmall.main I (by omega) hu C (fun g hg => (legal.2.2 g hg).le) hRej mini
  have cap : S.card - 1 ≤ 5980 := by omega
  have k1 := Nat.mul_le_mul_left S.card cap
  have k2 : S.card*(S.card-1) ≤ 1200*C.size := by omega
  have upp := (Nat.mul_le_mul_left X.card (Nat.add_le_add_right k2 H.card)).trans (Nat.mul_le_mul_right _ XS)
  have key := incidence.trans upp
  by_contra! bad
  have sp0 : (0:ℤ) < C.size := by exact_mod_cast (show 0<C.size by omega)
  have natPos : 44*C.size ≤ H.card := by omega
  have positive : 0 ≤ (H.card : ℤ)-44*C.size := by zify at natPos; linarith
  have a₁ : 0 ≤ (H.card : ℤ)-C.size := by linarith
  have a₂ := mul_nonneg positive a₁
  have a₃ := mul_nonneg (show (0:ℤ) ≤ C.size by positivity) positive
  zify at key
  nlinarith only [a₂,a₃,key,sq_pos_of_pos sp0]

end PlanePartial

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PlanePartial.small29900 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → x5.size ≤ 29900 → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq order degree unique legal sound hs
  let pt : Fin N → Fin (N+N) := Fin.castAdd N
  let ln : Fin N → Fin (N+N) := Fin.natAdd N
  let owns (v : Fin (N+N)) (e : Fin N × Fin N) := v = pt e.1 ∨ v = ln e.2
  let pair (e : Fin N × Fin N) (v : Fin (N+N)) := decide (owns v e)
  let E (D : Circuit) := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true
  let incident (D : Circuit) (v : Fin (N+N)) := (E D).filter (owns v)
  let Sound (D : Circuit) := ∀ x : Fin (N+N) → Bool,
    Fintype.card {l : Fin N // x (ln l) = true} ≤ q →
    (¬ ∃ p l, I p l ∧ x (pt p) = true ∧ x (ln l) = true) →
    circuitFun (N+N) D x = false
  have apart (p l : Fin N) : pt p ≠ ln l := by
    intro equal
    have h := congrArg Fin.val equal
    change p.val = N+l.val at h
    omega
  have inj (k l : Fin N) (e : ln k = ln l) : k = l := by
    apply Fin.ext
    have h := congrArg Fin.val e
    change N+k.val = N+l.val at h
    omega
  have memE (D : Circuit) (e : Fin N × Fin N) :
      e ∈ E D ↔ I e.1 e.2 ∧ circuitFun (N+N) D (pair e) = true := by simp [E]
  have offPoint (D : Circuit) (neg : Sound D) (p : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = pt p)) = false := by
    apply neg
    · simp [fun l => (apart p l).symm]
    · rintro ⟨r,l,_,_,bad⟩
      exact (apart p l) (of_decide_eq_true bad).symm
  have offLine (D : Circuit) (neg : Sound D) (l : Fin N) :
      circuitFun (N+N) D (fun i => decide (i = ln l)) = false := by
    apply neg
    · rw [Fintype.card_subtype]
      have sub : (Finset.univ.filter fun k : Fin N => decide (ln k = ln l) = true) ⊆ {l} := by
        intro k hk
        exact Finset.mem_singleton.mpr (inj k l (of_decide_eq_true (Finset.mem_filter.mp hk).2))
      have h := Finset.card_le_card sub
      simp only [Finset.card_singleton] at h
      exact h.trans (by omega)
    · rintro ⟨p,k,_,bad,_⟩
      exact apart p l (of_decide_eq_true bad)
  have bound (k : ℕ) : ∀ D : Circuit, D.size = k → IsAO2 (N+N) D → Sound D → D.size ≤ 29900 →
      (E D).card ≤ 44 * D.size := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro D hk ao neg small
      by_cases core : ∀ v, (incident D v).card = 0 ∨ 44 < (incident D v).card
      · apply PlanePartial.dense_small q N I D (by omega) unique ao neg small
        intro v
        rcases core v with zero|many
        · exact Or.inl zero
        · exact Or.inr (by change 3 ≤ (incident D v).card; omega)
      push Not at core
      obtain ⟨v, present, cheap⟩ := core
      obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero present)
      obtain ⟨member, endpoint⟩ := Finset.mem_filter.mp he
      have accepted := ((memE D e).mp member).2
      have smaller : ∃ D' : Circuit, IsAO2 (N+N) D' ∧ D'.size < D.size ∧
          (∀ x, circuitFun (N+N) D' x = true → circuitFun (N+N) D x = true) ∧
          ∀ x : Fin (N+N) → Bool, x v = false → circuitFun (N+N) D' x = circuitFun (N+N) D x := by
        change v = pt e.1 ∨ v = ln e.2 at endpoint
        rcases endpoint with rfl | rfl
        · exact PEqualNP.Outside.L_meta_4451 (N+N) D (pt e.1) (ln e.2) ao (apart _ _)
            (offPoint D neg _) (offLine D neg _) accepted
        · apply PEqualNP.Outside.L_meta_4451 (N+N) D (ln e.2) (pt e.1) ao (apart _ _).symm
            (offLine D neg _) (offPoint D neg _)
          simpa only [pair,owns,or_comm] using accepted
      obtain ⟨D',valid,save,below,same⟩ := smaller
      have keepsSound : Sound D' := by
        intro x hx noEdges
        cases e : circuitFun (N+N) D' x with
        | false => rfl
        | true => exact False.elim (Bool.noConfusion ((below x e).symm.trans (neg x hx noEdges)))
      have sub : E D ⊆ E D' ∪ incident D v := by
        intro a ha
        by_cases hv : owns v a
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha,hv⟩)
        · obtain ⟨flag,hit⟩ := (memE D a).mp ha
          have noBit : pair a v = false := by simp [pair,hv]
          exact Finset.mem_union_left _ ((memE D' a).mpr ⟨flag,(same (pair a) noBit).trans hit⟩)
      have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
      have prev := ih D'.size (by omega) D' rfl valid keepsSound (by omega)
      omega
  have h := bound C.size C rfl legal sound hs
  simpa only [Fintype.card_subtype] using h

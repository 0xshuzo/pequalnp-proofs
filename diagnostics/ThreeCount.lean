import PEqualNP.Defs

namespace Three2685

variable {p l : ℕ} (E : Finset (Fin p × Fin l))

def countRect (A : Finset (Fin p)) (B : Finset (Fin l)) :=
  (A ×ˢ B).filter (fun e => e ∈ E)

def noFour : Prop := ∀ a a' b b', a ≠ a' → b ≠ b' →
  ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E)

theorem extra (d : ℕ) : d ≤ 1 + d.choose 2 := by
  induction d with
  | zero => decide
  | succ d ih =>
    cases d with
    | zero => decide
    | succ d =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

theorem singles {α β : Type} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (S : β → Finset α)
    (sub : ∀ b ∈ B, S b ⊆ A)
    (unique : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → ∀ x ∈ S b, ∀ y ∈ S b,
      x ∈ S c → y ∈ S c → x = y) :
    (∑ b ∈ B, (S b).card) ≤ B.card + A.card.choose 2 := by
  classical
  let pairs := fun b => (S b).powersetCard 2
  have disj : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → Disjoint (pairs b) (pairs c) := by
    intro b hb c hc hne
    refine Finset.disjoint_left.mpr ?_
    intro z zb zc
    obtain ⟨sb,k⟩ := Finset.mem_powersetCard.mp zb
    obtain ⟨sc,_⟩ := Finset.mem_powersetCard.mp zc
    obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp (show 1 < z.card by omega)
    exact ne (unique b hb c hc hne u (sb hu) v (sb hv) (sc hu) (sc hv))
  have packed : B.biUnion pairs ⊆ A.powersetCard 2 := by
    intro z hz
    obtain ⟨b,hb,hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hz,hk⟩ := Finset.mem_powersetCard.mp hz
    exact Finset.mem_powersetCard.mpr ⟨hz.trans (sub b hb), hk⟩
  have bound := Finset.card_le_card packed
  rw [Finset.card_biUnion disj,Finset.card_powersetCard] at bound
  calc
    (∑ b ∈ B, (S b).card) ≤ ∑ b ∈ B, (1 + (pairs b).card) := by
      apply Finset.sum_le_sum
      intro b _
      simpa [pairs,Finset.card_powersetCard] using extra (S b).card
    _ = B.card + ∑ b ∈ B, (pairs b).card := by simp [Finset.sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left bound _

theorem right_bound (A : Finset (Fin p)) (B : Finset (Fin l)) (h4 : noFour E) :
    (countRect E A B).card ≤ B.card + A.card.choose 2 := by
  let S := fun b => A.filter (fun a => (a,b) ∈ E)
  have hsum : (countRect E A B).card = ∑ b ∈ B, (S b).card := by
    rw [countRect, Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.card_filter]
  rw [hsum]
  apply singles A B S (fun _ _ => Finset.filter_subset _ _)
  intro b _ c _ ne x xb y yb xc yc
  by_contra xy
  exact h4 x y b c xy ne ⟨(Finset.mem_filter.mp xb).2,(Finset.mem_filter.mp xc).2,
    (Finset.mem_filter.mp yb).2,(Finset.mem_filter.mp yc).2⟩

theorem left_bound (A : Finset (Fin p)) (B : Finset (Fin l)) (h4 : noFour E) :
    (countRect E A B).card ≤ A.card + B.card.choose 2 := by
  let S := fun a => B.filter (fun b => (a,b) ∈ E)
  have hsum : (countRect E A B).card = ∑ a ∈ A, (S a).card := by
    rw [countRect, Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.card_filter]
  rw [hsum]
  apply singles B A S (fun _ _ => Finset.filter_subset _ _)
  intro a _ c _ ne x xa y ya xc yc
  by_contra xy
  exact h4 a c x y ne xy ⟨(Finset.mem_filter.mp xa).2,(Finset.mem_filter.mp ya).2,
    (Finset.mem_filter.mp xc).2,(Finset.mem_filter.mp yc).2⟩

theorem three (a b : ℕ) (h : a+b≤3) : a*b + a.choose 2 + b.choose 2 ≤ a+b := by
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> first | decide | omega

theorem sparse_rect (A : Finset (Fin p)) (B : Finset (Fin l)) (h4 : noFour E)
    (hc : ∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) (small : A.card+B.card≤3)
    (X : Finset (Fin p)) (Y : Finset (Fin l)) :
    (countRect E X Y).card ≤ X.card + Y.card := by
  classical
  let U := X ∩ A
  let V := Y ∩ B
  have uX : U ⊆ X := Finset.inter_subset_left
  have uA : U ⊆ A := Finset.inter_subset_right
  have vY : V ⊆ Y := Finset.inter_subset_left
  have vB : V ⊆ B := Finset.inter_subset_right
  have pack : countRect E X Y ⊆ (U ×ˢ V) ∪ countRect E U (Y \ V) ∪ countRect E (X \ U) V := by
    rintro ⟨x,y⟩ he
    obtain ⟨mem,e⟩ := Finset.mem_filter.mp he
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp mem
    by_cases hu : x∈U
    · by_cases hv : y∈V
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hu,hv⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hu,Finset.mem_sdiff.mpr ⟨hy,hv⟩⟩,e⟩))
    · have hA : x∉A := fun h => hu (Finset.mem_inter.mpr ⟨hx,h⟩)
      have hv : y ∈ V := Finset.mem_inter.mpr ⟨hy,(hc (x,y) e).resolve_left hA⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_sdiff.mpr ⟨hx,hu⟩,hv⟩,e⟩)
  have bound := (Finset.card_le_card pack).trans (Finset.card_union_le _ _)
  have inner := Finset.card_union_le (U ×ˢ V) (countRect E U (Y \ V))
  have r := right_bound E U (Y \ V) h4
  have lft := left_bound E (X \ U) V h4
  rw [Finset.card_product] at inner
  rw [Finset.card_sdiff_of_subset vY] at r
  rw [Finset.card_sdiff_of_subset uX] at lft
  have t := three U.card V.card (by have := Finset.card_le_card uA; have := Finset.card_le_card vB; omega)
  have := Finset.card_le_card uX
  have := Finset.card_le_card vY
  omega

end Three2685

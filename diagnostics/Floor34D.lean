import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17744

open PEqualNP.HeptadCover

lemma sL_card : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide

lemma sL_inter_eq_one : ∀ l1 l2 : Fin 13, l1 ≠ l2 → (singerLines3 l1 ∩ singerLines3 l2).card = 1 := by
  decide

lemma unique_line_of_ne :
    ∀ a b : Fin 13, a ≠ b → ∃ l : Fin 13, a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧
      ∀ l' : Fin 13, a ∈ singerLines3 l' → b ∈ singerLines3 l' → l' = l := by
  decide

lemma card_union_three_lines (l1 l2 l3 : Fin 13)
    (h12 : l1 ≠ l2) (h13 : l1 ≠ l3) (h23 : l2 ≠ l3)
    (hnc : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3)) :
    (singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3).card = 9 := by
  have c1 := sL_card l1
  have c2 := sL_card l2
  have c3 := sL_card l3
  have i12 := sL_inter_eq_one l1 l2 h12
  have i13 := sL_inter_eq_one l1 l3 h13
  have i23 := sL_inter_eq_one l2 l3 h23
  have h12u : (singerLines3 l1 ∪ singerLines3 l2).card = 7 := by
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    omega
  have hdisj : Disjoint (singerLines3 l1 ∩ singerLines3 l3) (singerLines3 l2 ∩ singerLines3 l3) := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_inter] at hp1 hp2
    exact hnc p ⟨hp1.1, hp2.1, hp1.2⟩
  have hi123 : ((singerLines3 l1 ∪ singerLines3 l2) ∩ singerLines3 l3).card = 2 := by
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj, i13, i23]
  have := Finset.card_union_add_card_inter (singerLines3 l1 ∪ singerLines3 l2) (singerLines3 l3)
  omega

lemma card_biUnion_lines_le (x2 : Finset (Fin 13))
    (hcard : x2.card ≤ 3)
    (hnc : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) :
    (x2.biUnion singerLines3).card ≤ 9 := by
  by_cases h0 : x2.card = 0
  · rw [Finset.card_eq_zero.mp h0]; simp
  by_cases h1 : x2.card = 1
  · obtain ⟨l1, rfl⟩ := Finset.card_eq_one.mp h1
    simp [sL_card]
  by_cases h2 : x2.card = 2
  · obtain ⟨l1, l2, hne, rfl⟩ := Finset.card_eq_two.mp h2
    have hbi : ({l1, l2} : Finset (Fin 13)).biUnion singerLines3 = singerLines3 l1 ∪ singerLines3 l2 := by
      ext p; simp
    rw [hbi]
    have := Finset.card_union_add_card_inter (singerLines3 l1) (singerLines3 l2)
    have := sL_card l1; have := sL_card l2; have := sL_inter_eq_one l1 l2 hne
    omega
  · have h3 : x2.card = 3 := by omega
    obtain ⟨l1, l2, l3, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp h3
    have hbi : ({l1, l2, l3} : Finset (Fin 13)).biUnion singerLines3 =
        singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3 := by
      ext p; simp [or_assoc]
    rw [hbi]
    have hnc3 : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hsub : ({l1, l2, l3} : Finset (Fin 13)) ⊆
          ({l1, l2, l3} : Finset (Fin 13)).filter (fun l => p ∈ singerLines3 l) := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hl ⊢
        rcases hl with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, hp1⟩
        · exact ⟨Or.inr (Or.inl rfl), hp2⟩
        · exact ⟨Or.inr (Or.inr rfl), hp3⟩
      have hc := Finset.card_le_card hsub
      have h3c : ({l1, l2, l3} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
      have hle2 := hnc p
      omega
    rw [card_union_three_lines l1 l2 l3 h12 h13 h23 hnc3]

lemma mem_missLines_iff (X : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 X ↔ ∀ p ∈ X, p ∉ singerLines3 l := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  exact ⟨fun h p hp hpl => h hpl hp, fun h p hpl hp => h p hp hpl⟩

lemma extend_one (x1 x2 : Finset (Fin 13))
    (h1 : x1.card ≤ 3) (h2 : x2.card ≤ 3)
    (hcol : ∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2)
    (hcon : ∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2)
    (hmiss : x2 ⊆ missLines singerLines3 x1) :
    ∃ p : Fin 13, p ∉ x1 ∧
      (∀ l : Fin 13, (insert p x1 ∩ singerLines3 l).card ≤ 2) ∧
      x2 ⊆ missLines singerLines3 (insert p x1) := by
  let U := x2.biUnion singerLines3
  have hU9 : U.card ≤ 9 := card_biUnion_lines_le x2 h2 hcon
  have hU_miss : ∀ p : Fin 13, p ∉ U → x2 ⊆ missLines singerLines3 (insert p x1) := by
    intro p hpU l hl
    rw [mem_missLines_iff]
    intro q hq
    rw [Finset.mem_insert] at hq
    rcases hq with rfl | hqx1
    · intro hpl
      exact hpU (Finset.mem_biUnion.mpr ⟨l, hl, hpl⟩)
    · exact (mem_missLines_iff x1 l).mp (hmiss hl) q hqx1
  by_cases hc0 : x1.card = 0
  · have hx1 : x1 = ∅ := Finset.card_eq_zero.mp hc0
    subst hx1
    have hlt : U.card < (Finset.univ : Finset (Fin 13)).card := by simp; omega
    obtain ⟨p, _, hpU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨p, by simp, ?_, hU_miss p hpU⟩
    intro l
    change ({p} ∩ singerLines3 l).card ≤ 2
    have hle : ({p} ∩ singerLines3 l).card ≤ ({p} : Finset (Fin 13)).card := Finset.card_le_card Finset.inter_subset_left
    rw [Finset.card_singleton] at hle
    omega
  by_cases hc1 : x1.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
    have hlt : (insert a U).card < (Finset.univ : Finset (Fin 13)).card := by
      have := Finset.card_insert_le a U; simp; omega
    obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, not_or] at hp
    refine ⟨p, by simp [hp.1], ?_, hU_miss p hp.2⟩
    intro l
    have hle : (insert p {a} ∩ singerLines3 l).card ≤ (insert p {a} : Finset (Fin 13)).card :=
      Finset.card_le_card Finset.inter_subset_left
    have hle2 : (insert p {a} : Finset (Fin 13)).card ≤ 2 := by
      have := Finset.card_insert_le p ({a} : Finset (Fin 13)); simp at this; omega
    omega
  by_cases hc2 : x1.card = 2
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc2
    obtain ⟨lab, halab, hblab, hlab_uniq⟩ := unique_line_of_ne a b hab
    let F := singerLines3 lab ∪ U
    have hFlt : F.card < (Finset.univ : Finset (Fin 13)).card := by
      by_cases hx2e : x2 = ∅
      · have hUe : U = ∅ := by simp [U, hx2e]
        simp [F, hUe, sL_card]
      · obtain ⟨l0, hl0⟩ := Finset.nonempty_iff_ne_empty.mpr hx2e
        have hl0_ne : l0 ≠ lab := by
          intro heq; subst heq
          exact (mem_missLines_iff {a, b} l0).mp (hmiss hl0) a (by simp) halab
        have hi : (singerLines3 lab ∩ singerLines3 l0).card = 1 := sL_inter_eq_one lab l0 hl0_ne.symm
        have hsub : singerLines3 lab ∩ singerLines3 l0 ⊆ singerLines3 lab ∩ U := by
          intro q hq
          simp only [Finset.mem_inter] at hq ⊢
          exact ⟨hq.1, Finset.mem_biUnion.mpr ⟨l0, hl0, hq.2⟩⟩
        have hiU : 1 ≤ (singerLines3 lab ∩ U).card := by
          have := Finset.card_le_card hsub; omega
        have huc := Finset.card_union_add_card_inter (singerLines3 lab) U
        have hlc := sL_card lab
        change (singerLines3 lab ∪ U).card < (Finset.univ : Finset (Fin 13)).card
        rw [Finset.card_univ, Fintype.card_fin]
        omega
    obtain ⟨p, _, hpF⟩ := Finset.exists_mem_notMem_of_card_lt_card hFlt
    simp only [F, Finset.mem_union, not_or] at hpF
    have hpa : p ≠ a := fun h => hpF.1 (h ▸ halab)
    have hpb : p ≠ b := fun h => hpF.1 (h ▸ hblab)
    refine ⟨p, by simp [hpa, hpb], ?_, hU_miss p hpF.2⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne : l ≠ lab := fun h => hpF.1 (h ▸ hpl)
      have hnotboth : ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l) := fun ⟨ha, hb⟩ => hlne (hlab_uniq l ha hb)
      have hsub : insert p {a, b} ∩ singerLines3 l ⊆ insert p ({a, b} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr ⟨Or.inl rfl, hq.2⟩
        · exact Or.inr ⟨Or.inr rfl, hq.2⟩
      have hc1' : ({a, b} ∩ singerLines3 l).card ≤ 1 := by
        by_cases ha : a ∈ singerLines3 l
        · have hb : b ∉ singerLines3 l := fun hb => hnotboth ⟨ha, hb⟩
          have heq : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l = {a} := by
            ext q; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hq⟩
              · rfl
              · exact (hb hq).elim
            · rintro rfl; exact ⟨Or.inl rfl, ha⟩
          rw [heq]; simp
        · have hsubb : ({a, b} : Finset (Fin 13)) ∩ singerLines3 l ⊆ {b} := by
            intro q hq
            simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
            rcases hq.1 with rfl | rfl
            · exact (ha hq.2).elim
            · rfl
          exact Nat.le_trans (Finset.card_le_card hsubb) (by simp)
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b} ∩ singerLines3 l = {a, b} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l
  · have hc3 : x1.card = 3 := by omega
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc3
    obtain ⟨l1, ha1, hb1, h1uniq⟩ := unique_line_of_ne a b hab
    obtain ⟨l2, hb2, hc2', h2uniq⟩ := unique_line_of_ne b c hbc
    obtain ⟨l3, ha3, hc3', h3uniq⟩ := unique_line_of_ne a c hac
    have hnotcol : ∀ l : Fin 13, ¬(a ∈ singerLines3 l ∧ b ∈ singerLines3 l ∧ c ∈ singerLines3 l) := by
      intro l ⟨ha, hb, hc⟩
      have hsub : ({a, b, c} : Finset (Fin 13)) ⊆ ({a, b, c} : Finset (Fin 13)) ∩ singerLines3 l := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq with rfl | rfl | rfl
        · exact ⟨Or.inl rfl, ha⟩
        · exact ⟨Or.inr (Or.inl rfl), hb⟩
        · exact ⟨Or.inr (Or.inr rfl), hc⟩
      have hle := hcol l
      have h3c : ({a, b, c} : Finset (Fin 13)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
      have := Finset.card_le_card hsub
      omega
    have hl12 : l1 ≠ l2 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc2'⟩
    have hl13 : l1 ≠ l3 := fun h => hnotcol l1 ⟨ha1, hb1, h ▸ hc3'⟩
    have hl23 : l2 ≠ l3 := fun h => hnotcol l2 ⟨h ▸ ha3, hb2, hc2'⟩
    have hnc_tri : ∀ p : Fin 13, ¬(p ∈ singerLines3 l1 ∧ p ∈ singerLines3 l2 ∧ p ∈ singerLines3 l3) := by
      intro p ⟨hp1, hp2, hp3⟩
      have hpb : p = b := by
        by_contra hne
        exact hl12 ((h1uniq l2 (by
          -- wait: b is in both l1 and l2; unique point of l1 cap l2 is b!
          exfalso
          have hsub : ({p, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact Finset.mem_inter.mpr ⟨hp1, hp2⟩
            · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc
          omega) hb2).symm)
      subst hpb
      exact hnotcol l3 ⟨ha3, hp3, hc3'⟩
    let T := singerLines3 l1 ∪ singerLines3 l2 ∪ singerLines3 l3
    have hTcard : T.card = 9 := card_union_three_lines l1 l2 l3 hl12 hl13 hl23 hnc_tri
    let R := Finset.univ \ T
    have hRcard : R.card = 4 := by
      dsimp only [R]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
    have hline_R : ∀ l ∈ x2, (R ∩ singerLines3 l).card ≤ 1 := by
      intro l hl
      have ha_not : a ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) a (by simp)
      have hb_not : b ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) b (by simp)
      have hc_not : c ∉ singerLines3 l := (mem_missLines_iff _ l).mp (hmiss hl) c (by simp)
      have hll1 : l ≠ l1 := fun h => ha_not (h ▸ ha1)
      have hll2 : l ≠ l2 := fun h => hb_not (h ▸ hb2)
      have hll3 : l ≠ l3 := fun h => hc_not (h ▸ hc3')
      obtain ⟨p1, hp1⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l1 hll1]; omega)
      obtain ⟨p2, hp2⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l2 hll2]; omega)
      obtain ⟨p3, hp3⟩ := Finset.card_pos.mp (by rw [sL_inter_eq_one l l3 hll3]; omega)
      simp only [Finset.mem_inter] at hp1 hp2 hp3
      have hp12 : p1 ≠ p2 := by
        intro heq; subst heq
        have hsub : ({p1, b} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l2 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp2.2⟩
          · exact Finset.mem_inter.mpr ⟨hb1, hb2⟩
        have hne : p1 ≠ b := fun h => hb_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l2 hl12] at hc; omega
      have hp13 : p1 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p1, a} : Finset (Fin 13)) ⊆ singerLines3 l1 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp1.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨ha1, ha3⟩
        have hne : p1 ≠ a := fun h => ha_not (h ▸ hp1.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l1 l3 hl13] at hc; omega
      have hp23 : p2 ≠ p3 := by
        intro heq; subst heq
        have hsub : ({p2, c} : Finset (Fin 13)) ⊆ singerLines3 l2 ∩ singerLines3 l3 := by
          intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · exact Finset.mem_inter.mpr ⟨hp2.2, hp3.2⟩
          · exact Finset.mem_inter.mpr ⟨hc2', hc3'⟩
        have hne : p2 ≠ c := fun h => hc_not (h ▸ hp2.1)
        have hc := Finset.card_le_card hsub
        rw [Finset.card_pair hne, sL_inter_eq_one l2 l3 hl23] at hc; omega
      have hsubT : ({p1, p2, p3} : Finset (Fin 13)) ⊆ T ∩ singerLines3 l := by
        intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hp1.2), hp1.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hp2.2), hp2.1⟩
        · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hp3.2, hp3.1⟩
      have h3in : 3 ≤ (T ∩ singerLines3 l).card := by
        have h3c : ({p1, p2, p3} : Finset (Fin 13)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hp12, hp13]),
            Finset.card_insert_of_notMem (by simp [hp23]), Finset.card_singleton]
        have := Finset.card_le_card hsubT; omega
      have hdisjRT : Disjoint (R ∩ singerLines3 l) (T ∩ singerLines3 l) := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        simp only [R, Finset.mem_inter, Finset.mem_sdiff] at hq1 hq2
        exact hq1.1.2 hq2.1
      have hunion_sub : (R ∩ singerLines3 l) ∪ (T ∩ singerLines3 l) ⊆ singerLines3 l :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hle4 := Finset.card_le_card hunion_sub
      rw [Finset.card_union_of_disjoint hdisjRT, sL_card l] at hle4
      omega
    have hRU_le : (R ∩ U).card ≤ 3 := by
      have hsub : R ∩ U ⊆ x2.biUnion (fun l => R ∩ singerLines3 l) := by
        intro q hq
        simp only [U, Finset.mem_inter, Finset.mem_biUnion] at hq ⊢
        rcases hq.2 with ⟨l, hl, hql⟩
        exact ⟨l, hl, hq.1, hql⟩
      calc (R ∩ U).card
          ≤ (x2.biUnion (fun l => R ∩ singerLines3 l)).card := Finset.card_le_card hsub
        _ ≤ ∑ l ∈ x2, (R ∩ singerLines3 l).card := Finset.card_biUnion_le
        _ ≤ ∑ _l ∈ x2, 1 := Finset.sum_le_sum hline_R
        _ = x2.card := by simp
        _ ≤ 3 := h2
    have hlt : (R ∩ U).card < R.card := by omega
    obtain ⟨p, hpR, hpnotRU⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hpU : p ∉ U := fun h => hpnotRU (Finset.mem_inter.mpr ⟨hpR, h⟩)
    have hpT : p ∉ T := (Finset.mem_sdiff.mp hpR).2
    have hpa : p ≠ a := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ ha1))
    have hpb : p ≠ b := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_left _ hb1))
    have hpc : p ≠ c := fun h => hpT (h ▸ Finset.mem_union_left _ (Finset.mem_union_right _ hc2'))
    refine ⟨p, by simp [hpa, hpb, hpc], ?_, hU_miss p hpU⟩
    intro l
    by_cases hpl : p ∈ singerLines3 l
    · have hlne1 : l ≠ l1 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_left _ (h ▸ hpl)))
      have hlne2 : l ≠ l2 := fun h => hpT (Finset.mem_union_left _ (Finset.mem_union_right _ (h ▸ hpl)))
      have hlne3 : l ≠ l3 := fun h => hpT (Finset.mem_union_right _ (h ▸ hpl))
      have h1_le : ({a, b, c} ∩ singerLines3 l).card ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ ({a, b, c} ∩ singerLines3 l).card := by omega
        obtain ⟨u, v, huv, huvsub⟩ : ∃ u v, u ≠ v ∧ u ∈ ({a, b, c} ∩ singerLines3 l) ∧ v ∈ ({a, b, c} ∩ singerLines3 l) := by
          obtain ⟨S2, hS2sub, hS2card⟩ := Finset.exists_subset_card_eq hge2
          obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hS2card
          exact ⟨u, v, huv, hS2sub (by simp), hS2sub (by simp)⟩
        rcases huvsub with ⟨hu, hv⟩
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu.1 with rfl | rfl | rfl <;> rcases hv.1 with rfl | rfl | rfl
        · exact huv rfl
        · exact hlne1 (h1uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hu.2 hv.2)
        · exact hlne1 (h1uniq l hv.2 hu.2)
        · exact huv rfl
        · exact hlne2 (h2uniq l hu.2 hv.2)
        · exact hlne3 (h3uniq l hv.2 hu.2)
        · exact hlne2 (h2uniq l hv.2 hu.2)
        · exact huv rfl
      have hsub : insert p {a, b, c} ∩ singerLines3 l ⊆ insert p ({a, b, c} ∩ singerLines3 l) := by
        intro q hq
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hq ⊢
        rcases hq.1 with rfl | hq'
        · exact Or.inl rfl
        · exact Or.inr ⟨hq', hq.2⟩
      have := Finset.card_le_card hsub
      have := Finset.card_insert_le p ({a, b, c} ∩ singerLines3 l)
      omega
    · have heq : insert p {a, b, c} ∩ singerLines3 l = {a, b, c} ∩ singerLines3 l := by
        ext q; simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hq, hql⟩
          · exact (hpl hql).elim
          · exact ⟨hq, hql⟩
        · rintro ⟨hq, hql⟩; exact ⟨Or.inr hq, hql⟩
      rw [heq]
      exact hcol l

lemma extend_to_quad :
    ∀ k : ℕ, ∀ x1 x2 : Finset (Fin 13),
      4 - x1.card = k → x1.card ≤ 4 → x2.card ≤ 3 →
      (∀ l : Fin 13, (x1 ∩ singerLines3 l).card ≤ 2) →
      (∀ p : Fin 13, (x2.filter (fun l => p ∈ singerLines3 l)).card ≤ 2) →
      x2 ⊆ missLines singerLines3 x1 →
      ∃ Q ∈ quadrangles singerLines3, x1 ⊆ Q ∧ x2 ⊆ missLines singerLines3 Q := by
  intro k
  induction k with
  | zero =>
    intro x1 x2 hk h1 _ hcol _ hmiss
    have h4 : x1.card = 4 := by omega
    refine ⟨x1, ?_, Finset.Subset.refl x1, hmiss⟩
    simp only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    exact ⟨h4, hcol⟩
  | succ k ih =>
    intro x1 x2 hk h1 h2 hcol hcon hmiss
    have hle3 : x1.card ≤ 3 := by omega
    obtain ⟨p, hpnot, hcol', hmiss'⟩ := extend_one x1 x2 hle3 h2 hcol hcon hmiss
    have hcard' : (insert p x1).card = x1.card + 1 := Finset.card_insert_of_notMem hpnot
    obtain ⟨Q, hQ, hsubQ, hmissQ⟩ := ih (insert p x1) x2 (by omega) (by omega) h2 hcol' hcon hmiss'
    exact ⟨Q, hQ, Finset.Subset.trans (Finset.subset_insert p x1) hsubQ, hmissQ⟩

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.HeptadCover PEqualNP.GenericRejection

abbrev I := Fin 13
abbrev lines := singerLines3

def faults (p l : I) (C : Circuit) :=
  (quadrangles lines).filter fun Q =>
    C.eval (incidenceInput (Q.erase p) ((missLines lines Q).erase l)) = true

theorem incidenceUp (C : Circuit) (mc : Monotone2 C)
    {A B A' B' : Finset I} (aa : A ⊆ A') (bb : B ⊆ B') :
    C.eval (incidenceInput A B) = true → C.eval (incidenceInput A' B') = true := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append,← List.ofFn_fin_append]
  apply cmono C mc
  intro j
  induction j using Fin.addCases with
  | left i => simpa only [Fin.append, Fin.addCases_left, Fin.addCases_right] using (show decide (i ∈ A) ≤ decide (i ∈ A') by
                          by_cases h : i ∈ A
                          · simp [h,aa h]
                          · simp [h])
  | right i => simpa only [Fin.append, Fin.addCases_left, Fin.addCases_right] using (show decide (i ∈ B) ≤ decide (i ∈ B') by
                          by_cases h : i ∈ B
                          · simp [h,bb h]
                          · simp [h])

theorem small_exact (p l : I) (C D : Circuit) (same : C.gates=D.gates) (mc : Monotone2 C)
    (pos : ∀ a b : I, a ≠ p → b ≠ l → a ∈ lines b →
      ∀ F ∈ [C,D], F.eval (incidenceInput {a} {b})=true)
    (dis : Disjoint (faults p l C) (faults p l D))
    (A B : Finset I) (pa : p ∉ A) (lb : l ∉ B)
    (ac : A.card ≤ 4) (bc : B.card ≤ 3)
    (noThree : ∀ k, (A ∩ lines k).card ≤ 2)
    (noPencil : ∀ a, (B.filter (fun k => a ∈ lines k)).card ≤ 2) :
    (C.eval (incidenceInput A B)=true ∧ D.eval (incidenceInput A B)=true) ↔
      ∃ a ∈ A, ∃ b ∈ B, a ∈ lines b := by
  have md : Monotone2 D := fun g hg => mc g (same.symm ▸ hg)
  constructor
  · rintro ⟨hc,hd⟩
    by_contra hn
    have ob : B ⊆ missLines lines A := by
      intro b hb
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.disjoint_left.mpr ?_⟩
      intro a hab ha
      exact hn ⟨a,ha,b,hb,hab⟩
    obtain ⟨Q,hQ,asub,bsub⟩ := extend_to_quad (4-A.card) A B rfl ac bc noThree noPencil ob
    have aext : A ⊆ Q.erase p := fun a ha => Finset.mem_erase.mpr
      ⟨fun eq => pa (eq ▸ ha),asub ha⟩
    have bext : B ⊆ (missLines lines Q).erase l := fun b hb => Finset.mem_erase.mpr
      ⟨fun eq => lb (eq ▸ hb),bsub hb⟩
    exact Finset.disjoint_left.mp dis (Finset.mem_filter.mpr ⟨hQ,incidenceUp C mc aext bext hc⟩)
      (Finset.mem_filter.mpr ⟨hQ,incidenceUp D md aext bext hd⟩)
  · rintro ⟨a,ha,b,hb,hab⟩
    have h := pos a b (fun e => pa (e ▸ ha)) (fun e => lb (e ▸ hb)) hab
    have aa : {a} ⊆ A := Finset.singleton_subset_iff.mpr ha
    have bb : {b} ⊆ B := Finset.singleton_subset_iff.mpr hb
    exact ⟨incidenceUp C mc aa bb (h C (by simp)),incidenceUp D md aa bb (h D (by simp))⟩

abbrev W := Bool × I
def pointOf (w : W) : Finset I := if w.1 then ∅ else {w.2}
def lineOf (w : W) : Finset I := if w.1 then {w.2} else ∅
def free (p l : I) (w : W) := if w.1 then w.2 ≠ l else w.2 ≠ p
instance (p l : I) (w : W) : Decidable (free p l w) := by unfold free; split <;> infer_instance
def link (u v : W) : Prop := if u.1 = v.1 then False else
  if u.1 then v.2 ∈ lines u.2 else u.2 ∈ lines v.2
instance (u v : W) : Decidable (link u v) := by unfold link; split <;> first | split <;> infer_instance | infer_instance
def one (C : Circuit) (u : W) := C.eval (incidenceInput (pointOf u) (lineOf u))
def two (C : Circuit) (u v : W) := C.eval (incidenceInput
    (pointOf u ∪ pointOf v) (lineOf u ∪ lineOf v))
def testsAt (p l : I) (C : Circuit) (u : W) := ∃ w, free p l w ∧ link u w ∧
  one C w = false ∧ two C u w = true

theorem link_logic (u v : W) :
    (∃ a ∈ pointOf u ∪ pointOf v, ∃ b ∈ lineOf u ∪ lineOf v, a ∈ lines b) ↔ link u v := by
  rcases u with ⟨t,u⟩
  rcases v with ⟨s,v⟩
  cases t <;> cases s <;> simp [pointOf,lineOf,link]

theorem frees (p l : I) (w : W) (h : free p l w) :
    p ∉ pointOf w ∧ l ∉ lineOf w := by
  rcases w with ⟨t,i⟩
  cases t <;> simp_all [free,pointOf,lineOf,ne_comm]

theorem twoBound (u v : W) :
    (pointOf u ∪ pointOf v).card ≤ 2 ∧ (lineOf u ∪ lineOf v).card ≤ 2 := by
  have h (w : W) : (pointOf w).card ≤ 1 ∧ (lineOf w).card ≤ 1 := by
    rcases w with ⟨t,i⟩; cases t <;> simp [pointOf,lineOf]
  exact ⟨(Finset.card_union_le _ _).trans (Nat.add_le_add (h u).1 (h v).1),
    (Finset.card_union_le _ _).trans (Nat.add_le_add (h u).2 (h v).2)⟩

def avoid (h a b c : I) : I × I :=
  (if h = a then b else a, if h = a ∨ h = b then c else b)

theorem avoidTwo : ∀ h a : I, ∀ t : Bool,
    let b := if t then a+1 else a-1
    let c := if t then a+3 else a-3
    let z := avoid h a b c
    z.1 ≠ z.2 ∧ z.1 ≠ h ∧ z.2 ≠ h ∧
    (if t then z.1 ∈ lines a ∧ z.2 ∈ lines a else a ∈ lines z.1 ∧ a ∈ lines z.2) := by
  decide +kernel

theorem twoNeighbors : ∀ p l : I, ∀ u : W, free p l u →
    ∃ a b : W, a ≠ b ∧ free p l a ∧ free p l b ∧ link u a ∧ link u b := by
  rintro p l ⟨t,x⟩ _
  cases t
  · let z := avoid l x (x-1) (x-3)
    have h : z.1 ≠ z.2 ∧ z.1 ≠ l ∧ z.2 ≠ l ∧ x ∈ lines z.1 ∧ x ∈ lines z.2 := avoidTwo l x false
    exact ⟨(true,z.1),(true,z.2),fun e => h.1 (congrArg Prod.snd e),h.2.1,h.2.2.1,h.2.2.2⟩
  · let z := avoid p x (x+1) (x+3)
    have h : z.1 ≠ z.2 ∧ z.1 ≠ p ∧ z.2 ≠ p ∧ z.1 ∈ lines x ∧ z.2 ∈ lines x := avoidTwo p x true
    exact ⟨(false,z.1),(false,z.2),fun e => h.1 (congrArg Prod.snd e),h.2.1,h.2.2.1,h.2.2.2⟩

theorem noBox (a b c d : W) (hab : a ≠ b) (hcd : c ≠ d)
    (h : link a c ∧ link b c ∧ link a d ∧ link b d) : False := by
  have rect (u v i j : I) (uv : u ≠ v) (ij : i ≠ j)
      (ui : u ∈ lines i) (vi : v ∈ lines i) (uj : u ∈ lines j) (vj : v ∈ lines j) : False := by
    obtain ⟨k,_,_,hx⟩ := unique_line_of_ne u v uv
    exact ij ((hx i ui vi).trans (hx j uj vj).symm)
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  rcases c with ⟨c,k⟩
  rcases d with ⟨d,m⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [link]
  all_goals first
    | exact rect i j k m hab hcd h.1 h.2.1 h.2.2.1 h.2.2.2
    | exact rect k m i j hcd hab h.1 h.2.2.1 h.2.1 h.2.2.2

theorem all_inputs_one_tap (p l : I) (C D : Circuit) (same : C.gates=D.gates) (mc : Monotone2 C)
    (pos : ∀ a b : I, a ≠ p → b ≠ l → a ∈ lines b →
      ∀ F ∈ [C,D], F.eval (incidenceInput {a} {b})=true)
    (dis : Disjoint (faults p l C) (faults p l D)) :
    (∀ u, free p l u → testsAt p l C u) ∨ (∀ u, free p l u → testsAt p l D u) := by
  classical
  have md : Monotone2 D := fun g hg => mc g (same.symm ▸ hg)
  have pair (u v : W) (hu : free p l u) (hv : free p l v) :
      (two C u v = true ∧ two D u v = true) ↔ link u v := by
    rw [← link_logic]
    obtain ⟨pu,lu⟩ := frees p l u hu
    obtain ⟨pv,lv⟩ := frees p l v hv
    obtain ⟨pc,lc⟩ := twoBound u v
    apply small_exact p l C D same mc pos dis
    · simpa using And.intro pu pv
    · simpa using And.intro lu lv
    · omega
    · omega
    · intro k; exact (Finset.card_le_card Finset.inter_subset_left).trans pc
    · intro k; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans lc
  by_contra h
  push_neg at h
  obtain ⟨⟨u,hu,bu⟩,⟨v,hv,bv⟩⟩ := h
  have forced (F : Circuit) (w x : W) (hf : ¬testsAt p l F w) (hx : free p l x)
      (hit : link w x) (yes : two F w x = true) : one F x = true := by
    cases ho : one F x
    · exact (hf ⟨x,hx,hit,ho,yes⟩).elim
    · rfl
  have cross (r s : W) (hr : free p l r) (hs : free p l s) (ur : link u r) (vs : link v s) : link r s := by
    have f := forced C u r bu hr ur ((pair u r hu hr).2 ur).1
    have g := forced D v s bv hs vs ((pair v s hv hs).2 vs).2
    apply (pair r s hr hs).1
    exact ⟨incidenceUp C mc Finset.subset_union_left Finset.subset_union_left f,
      incidenceUp D md Finset.subset_union_right Finset.subset_union_right g⟩
  obtain ⟨a,b,ab,ha,hb,ua,ub⟩ := twoNeighbors p l u hu
  obtain ⟨c,d,cd,hc,hd,vc,vd⟩ := twoNeighbors p l v hv
  exact noBox a b c d ab cd ⟨cross a c ha hc ua vc,cross b c hb hc ub vc,
    cross a d ha hd ua vd,cross b d hb hd ub vd⟩

section Reindex
variable {m n : Nat}

def liftIn (r : Fin n → Option (Fin m)) (x : Fin m → Bool) (w : Fin n) :=
  (r w).elim false x

def ref (r : Fin n → Option (Fin m)) (bound v : Nat) : Nat :=
  if h : v < n then (r ⟨v,h⟩).elim (m+bound+1) Fin.val else m+(v-n)

def rewriteGate (rr : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map rr⟩

def reindex (r : Fin n → Option (Fin m)) (C : Circuit) : Circuit :=
  let rr := ref r C.size
  ⟨C.gates.map (rewriteGate rr),rr C.output⟩

theorem ref_next (r : Fin n → Option (Fin m)) (cap k : Nat) (hk : k ≤ cap) (i : Nat) :
    ref r cap i = m+k ↔ i=n+k := by
  by_cases h : i<n
  · simp only [ref,dif_pos h]
    cases e : r ⟨i,h⟩ with
    | none => simp only [Option.elim_none]; omega
    | some j => simp only [Option.elim_some]; have := j.isLt; omega
  · simp only [ref,dif_neg h]; omega

theorem snoc_off (w : List Bool) (b : Bool) (i : Nat) (hn : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases lt : i<w.length
  · exact getD_snoc_lt w b i lt
  · rw [getD_snoc_gt w b i (by omega), List.getD_eq_default _ _ (by omega)]

theorem fold_ref (r : Fin n → Option (Fin m)) (cap : Nat) (gs : List Gate) (A B : List Bool)
    (k : Nat) (ha : A.length=n+k) (hb : B.length=m+k)
    (hlen : k+gs.length≤cap) (eq : ∀ i,A.getD i false = B.getD (ref r cap i) false) :
    ∀ i,(wf gs A).getD i false =
      (wf (gs.map (rewriteGate (ref r cap))) B).getD (ref r cap i) false := by
  induction gs generalizing k A B with
  | nil => exact eq
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => A.getD i false))
    have hg : (rewriteGate (ref r cap) g).op.eval ((rewriteGate (ref r cap) g).inputs.map
        (fun i => B.getD i false)) = v := by
      simp only [rewriteGate,List.map_map,Function.comp_def,v,eq]
    simp only [List.map_cons,wf,List.foldl_cons] at ⊢
    change ∀ i, (wf gs (A++[v])).getD i false = (wf (gs.map (rewriteGate (ref r cap)))
      (B++[(rewriteGate (ref r cap) g).op.eval ((rewriteGate (ref r cap) g).inputs.map
        fun j => B.getD j false)])).getD (ref r cap i) false
    rw [hg]
    apply ih (A++[v]) (B++[v]) (k+1) (by simp [ha]; omega) (by simp [hb]; omega)
      (by simp at hlen; omega)
    intro i
    have hit := ref_next r cap k (by simp at hlen; omega) i
    by_cases hi : i=n+k
    · have hi' : i=A.length := hi.trans ha.symm
      have hj : ref r cap i=B.length := (hit.mpr hi).trans hb.symm
      rw [hi',getD_snoc_eq]
      rw [← hi',hj,getD_snoc_eq]
    · rw [snoc_off _ _ _ (by omega),snoc_off _ _ _ (fun e => hi (hit.mp (e.trans hb))),eq]

theorem reindex_eval (r : Fin n → Option (Fin m)) (C : Circuit) (x : Fin m → Bool) :
    (reindex r C).eval (List.ofFn x) = C.eval (List.ofFn (liftIn r x)) := by
  symm
  apply fold_ref r C.size C.gates _ _ 0 (by simp) (by simp) (by simp [Circuit.size])
  intro i
  by_cases hi : i<n
  · simp only [ref,dif_pos hi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hi,Option.getD_some,liftIn]
    cases h : r ⟨i,hi⟩ with
    | some j => simp [j.isLt]
    | none =>
      have hb : ¬ m + C.size + 1 < m := by omega
      simp [Option.elim,h,hb]
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp [ref,hi])]
theorem reindex_mono (r : Fin n → Option (Fin m)) (C : Circuit) (mc : Monotone2 C) :
    Monotone2 (reindex r C) := by
  intro g hg
  obtain ⟨h,hm,rfl⟩ := List.mem_map.mp hg
  simpa [rewriteGate] using mc h hm
end Reindex
-- The general incidence lower bound is due to Zamua, PR #6620.
-- Here it applies to the AND-output case of L-meta-4510.
-- The branch count adapts L-meta-1483 to circuits tested only on pairs.
-- The incidence count uses the argument of L-meta-1955 for every positive order.
namespace LB

section WireValues

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

def Next (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ p g, C.gates[p]? = some g ∧ b = n+p ∧ a ∈ g.inputs

def Live (n : ℕ) (C : Circuit) (i : ℕ) : Prop :=
  ReflTransGen (Next n C) i C.output

def LNext (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := Next n C a b ∧ Live n C b

def Trace (n : ℕ) (C : Circuit) (P : ℕ → Prop) (i j : ℕ) : Prop :=
  ReflTransGen (fun a b => P a ∧ LNext n C a b) i j

theorem next_le {n : ℕ} {C : Circuit} {a b : ℕ} (h : ReflTransGen (Next n C) a b) :
    a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.1.le

theorem trace_le {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.2.1.1.le

theorem live_before {n : ℕ} {C : Circuit} {a b : ℕ} (hn : Next n C a b) (h : Live n C b) :
    Live n C a := (ReflTransGen.single hn).trans h

theorem trace_start {n : ℕ} {C : Circuit} {P : ℕ → Prop} {a b : ℕ}
    (h : Trace n C P a b) (hb : P b) : P a := by
  rcases h.cases_head with rfl | ⟨_, hs, _⟩
  · exact hb
  · exact hs.1

theorem align {n : ℕ} {C : Circuit} {P Q : ℕ → Prop} {v b : ℕ}
    (p : Trace n C P v b)
    (unique : ∀ a j j', a < b → P a → LNext n C a j → LNext n C a j' → j = j') :
    ∀ d, Trace n C Q v d → (d < b ∧ P d) ∨ Trace n C Q b d := by
  induction p using ReflTransGen.head_induction_on with
  | refl =>
    intro d q
    exact Or.inr q
  | head hp pt ih =>
    intro d q
    have hlt := hp.2.1.1.trans_le (trace_le pt)
    rcases q.cases_head with rfl | ⟨j, hq, qt⟩
    · exact Or.inl ⟨hlt, hp.1⟩
    · have e := unique _ _ _ hlt hp.1 hp.2 hq.2
      subst j
      exact ih _ qt

theorem difference {n : ℕ} (C : Circuit) (x y : Fin n → Bool) :
    ∀ j, Live n C j → val C x j ≠ val C y j →
      ∃ i : Fin n, x i ≠ y i ∧ Trace n C (fun a => val C x a ≠ val C y a) i.val j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hd
    by_cases hin : j < n
    · let i : Fin n := ⟨j,hin⟩
      exact ⟨i, by simpa only [← val_input C x i, ← val_input C y i] using hd, .refl⟩
    have hb : j < n+C.gates.length := by
      by_contra! he
      exact hd ((val_beyond C x he).trans (val_beyond C y he).symm)
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hdiff : ∃ i ∈ g.inputs, i < n+p ∧ val C x i ≠ val C y i := by
      by_contra! hn
      apply hd
      rw [val_gate C x hg, val_gate C y hg]
      apply congrArg _
      apply List.map_congr_left
      intro i hi
      by_cases hj : i < n+p
      · simp [operand, hj, hn i hi hj]
      · simp [operand, hj]
    obtain ⟨a, ha, hlt, ha'⟩ := hdiff
    have hs : Next n C a (n+p) := ⟨hlt,p,g,hg,rfl,ha⟩
    obtain ⟨i, hi, hpath⟩ := ih a hlt (live_before hs hj) ha'
    exact ⟨i, hi, hpath.tail ⟨ha',hs,hj⟩⟩

end WireValues

section Monotonicity

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def point (s : Finset (Fin n)) (i : Fin n) : Bool := decide (i ∈ s)

theorem point_mono {s t : Finset (Fin n)} (h : s ⊆ t) :
    ∀ i, point s i = true → point t i = true := by
  intro i hi
  simpa only [point, decide_eq_true_eq] using h (by simpa only [point, decide_eq_true_eq] using hi)

theorem point_insert {s : Finset (Fin n)} {v u : Fin n} (h : u ≠ v) :
    point (insert v s) u = point s u := by simp [point, h]

def Carries (C : Circuit) (v : Fin n) (a : ℕ) : Prop :=
  val C (point {v}) a ≠ val C (point (∅ : Finset (Fin n))) a

theorem carries_iff (hC : Monotone2 C) {v : Fin n} {a : ℕ} :
    Carries C v a ↔
      val C (point {v}) a = true ∧ val C (point (∅ : Finset (Fin n))) a = false := by
  have hm := acts_mono hC (point_mono (Finset.empty_subset {v})) a
  unfold Carries
  cases ha : val C (point {v}) a <;>
    cases hb : val C (point (∅ : Finset (Fin n))) a <;> simp_all

theorem singleton_path {v : Fin n} {a : ℕ} (ha : Live n C a) (hd : Carries C v a) :
    Trace n C (Carries C v) v.val a := by
  obtain ⟨i, hi, hpath⟩ := difference C (point {v}) (point ∅) a ha hd
  have e : i = v := by
    by_contra h
    exact hi (by simp [point, h])
  exact e ▸ hpath

theorem influence {v : Fin n} {P : ℕ → Prop} {b j : ℕ} {x y : Fin n → Bool}
    (path : Trace n C P v.val b)
    (unique : ∀ a k k', a < b → P a → LNext n C a k → LNext n C a k' → k = k')
    (agrees : ∀ i, i ≠ v → x i = y i) (hj : Live n C j) (hd : val C x j ≠ val C y j) :
    (j < b ∧ P j) ∨ (b ≤ j ∧ val C x b ≠ val C y b) := by
  obtain ⟨i, hi, trace⟩ := difference C x y j hj hd
  have e : i = v := by
    by_contra h
    exact hi (agrees i h)
  subst i
  rcases align path unique j trace with ha | hb
  · exact Or.inl ha
  · exact Or.inr ⟨trace_le hb, trace_start hb hd⟩

noncomputable def readers (n : ℕ) (C : Circuit) (a : ℕ) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (fun b => LNext n C a b)

theorem next_in_range {a b : ℕ} (h : Next n C a b) : b < n+C.gates.length := by
  obtain ⟨_,p,g,hg,rfl,_⟩ := h
  exact Nat.add_lt_add_left (List.getElem?_eq_some_iff.1 hg).1 n

theorem mem_readers {a b : ℕ} : b ∈ readers n C a ↔ LNext n C a b := by
  classical
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨next_in_range h.1, h⟩⟩

def Branch (n : ℕ) (C : Circuit) (a : ℕ) : Prop := 2 ≤ (readers n C a).card

theorem nonbranch_unique {a j j' : ℕ} (h : ¬ Branch n C a)
    (hj : LNext n C a j) (hj' : LNext n C a j') : j = j' := by
  apply Finset.card_le_one_iff.1 (show (readers n C a).card ≤ 1 from by
    unfold Branch at h; omega) (mem_readers.2 hj) (mem_readers.2 hj')

def Eligible (C : Circuit) (v : Fin n) : Prop := ∃ b, Live n C b ∧ Carries C v b ∧ Branch n C b

noncomputable def firstBranch (C : Circuit) (v : Fin n) (h : Eligible C v) : ℕ := by
  classical exact Nat.find h

theorem firstBranch_spec (v : Fin n) (h : Eligible C v) :
    Live n C (firstBranch C v h) ∧ Carries C v (firstBranch C v h) ∧ Branch n C (firstBranch C v h) := by
  classical exact Nat.find_spec h

theorem firstBranch_unique (v : Fin n) (h : Eligible C v) :
    ∀ a j j', a < firstBranch C v h → Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  classical
  intro a j j' hl hc hj hj'
  apply nonbranch_unique _ hj hj'
  intro hb
  exact (Nat.not_le_of_gt hl) (Nat.find_min' h ⟨live_before hj.1 hj.2,hc,hb⟩)

theorem no_eligible_unique {v : Fin n} (h : ¬ Eligible C v) :
    ∀ a j j', Carries C v a → LNext n C a j → LNext n C a j' → j = j' := by
  intro a j j' hc hj hj'
  exact nonbranch_unique (fun hb => h ⟨a,live_before hj.1 hj.2,hc,hb⟩) hj hj'

end Monotonicity

section EdgeTests

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

def GraphEval (C : Circuit) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w : Fin n, val C (point {v,w}) C.output = true ↔ G.Adj v w

theorem point_pair (he : GraphEval C G) (v w : Fin n) :
    val C (point {v,w}) C.output = true ↔ G.Adj v w := he v w

theorem point_pair_quiet (he : GraphEval C G) {v w : Fin n} (hn : ¬ G.Adj v w) :
    val C (point {v,w}) C.output = false := by
  rw [← Bool.not_eq_true, point_pair he]
  exact hn

theorem point_single_quiet (he : GraphEval C G) (v : Fin n) :
    val C (point {v}) C.output = false := by
  simpa using point_pair_quiet he (G.irrefl (v := v))

theorem edge_at_output (he : GraphEval C G) {v w : Fin n} (hvw : G.Adj v w) :
    n ≤ C.output ∧ C.output < n+C.gates.length := by
  have hp := (point_pair he v w).2 hvw
  constructor
  · by_contra! hl
    let i : Fin n := ⟨C.output,hl⟩
    have hv := point_single_quiet he i
    rw [show C.output = i.val from rfl,val_input] at hv
    simp [point] at hv
  · by_contra! hgt
    rw [val_beyond C _ hgt] at hp
    contradiction

theorem two_inputs {l : List ℕ} {a b : ℕ} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b)
    (hl : l.length ≤ 2) :
    ∀ i ∈ l, i = a ∨ i = b := by
  have hsub : ({a,b} : Finset ℕ) ⊆ l.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
  have hcard : l.toFinset.card ≤ ({a,b} : Finset ℕ).card := by
    simpa [hne] using l.toFinset_card_le.trans hl
  have hEq := Finset.eq_of_subset_of_card_le hsub hcard
  intro i hi
  have hm : i ∈ ({a,b} : Finset ℕ) := hEq.symm ▸ (List.mem_toFinset.mpr hi)
  simpa using hm

theorem carries_separate (hC : Monotone2 C) {v w : Fin n} {a : ℕ}
    (h1 : val C (point {v}) a = true) (h0 : val C (point {w}) a = false) :
    Carries C v a ∧ ¬ Carries C w a := by
  have hb : val C (point (∅ : Finset (Fin n))) a = false := by
    rw [← Bool.not_eq_true]
    intro hc
    have hh := acts_mono hC (point_mono (Finset.empty_subset {w})) a hc
    rw [h0] at hh
    contradiction
  rw [carries_iff hC,carries_iff hC]
  simp [h1,h0,hb]

theorem meeting_gate (hC : Monotone2 C) (he : GraphEval C G) {v w : Fin n}
    (hvw : G.Adj v w) :
    ∃ p g a b, C.gates[p]? = some g ∧ g.op = GateOp.and ∧ Live n C (n+p) ∧
      LNext n C a (n+p) ∧ LNext n C b (n+p) ∧
      Carries C v a ∧ ¬ Carries C w a ∧ Carries C w b ∧ ¬ Carries C v b ∧
      (∀ i ∈ g.inputs, i = a ∨ i = b) := by
  classical
  let P (i : ℕ) := Live n C i ∧ val C (point {v,w}) i = true ∧
    val C (point {v}) i = false ∧ val C (point {w}) i = false
  have hex : ∃ i, P i :=
    ⟨C.output, .refl, (point_pair he v w).2 hvw, point_single_quiet he v, point_single_quiet he w⟩
  let j := Nat.find hex
  have hj : P j := Nat.find_spec hex
  have earlier (i : ℕ) (hlt : i < j) (hl : Live n C i)
      (htrue : val C (point {v,w}) i = true) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    by_contra! h
    have h' : P i := ⟨hl, htrue, by simpa using h.1, by simpa using h.2⟩
    exact (Nat.not_le_of_gt hlt) (Nat.find_min' hex h')
  have hge : n ≤ j := by
    by_contra! hh
    let i : Fin n := ⟨j,hh⟩
    obtain ⟨_,ht,hv,hw⟩ := hj
    rw [show j = i.val from rfl,val_input] at ht hv hw
    simp only [point,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with h | h
    · simp [point,h] at hv
    · simp [point,h] at hw
  have hlt : j < n+C.gates.length := by
    by_contra! hh
    have ht := hj.2.1
    rw [val_beyond C _ hh] at ht
    contradiction
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have ep : n+p = j := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hl := hC g (List.mem_of_getElem? hg)
  have hh : Live n C (n+p) := ep ▸ hj.1
  have hs1 : val C (point {v,w}) (n+p) = true := ep ▸ hj.2.1
  have hs2 : val C (point {v}) (n+p) = false := ep ▸ hj.2.2.1
  have hs3 : val C (point {w}) (n+p) = false := ep ▸ hj.2.2.2
  have reads (i : ℕ) (hi : i < n+p) (hm : i ∈ g.inputs) : LNext n C i (n+p) :=
    ⟨⟨hi,p,g,hg,rfl,hm⟩,hh⟩
  have hAnd : g.op = GateOp.and := by
    rcases hl.1 with h | h
    · exact h
    have hop : g.op = GateOp.or := h
    simp only [val_gate C _ hg, hop, GateOp.eval, List.any_map, Function.comp_apply, id,
      List.any_eq_true] at hs1
    obtain ⟨i,hi,ht⟩ := hs1
    have hi' : i < n+p := by
      by_contra hh'
      simp [operand,hh'] at ht
    have ht' : val C (point {v,w}) i = true := by simpa [operand,hi'] using ht
    rcases earlier i (ep ▸ hi') (live_before (reads i hi' hi).1 hh) ht' with hV | hW
    · have hs := hs2
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hV⟩).elim
    · have hs := hs3
      rw [← Bool.not_eq_true, val_gate C _ hg,hop,GateOp.eval,List.any_map,List.any_eq_true] at hs
      exact (hs ⟨i,hi,by simpa [operand,hi'] using hW⟩).elim
  have hAll : ∀ i ∈ g.inputs, operand C (point {v,w}) (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hs1
  have hFalse (x : Fin n → Bool) (hX : val C x (n+p) = false) :
      ∃ i ∈ g.inputs, operand C x (n+p) i = false := by
    by_contra! h
    have ht : val C x (n+p) = true := by
      rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
      intro i hi
      simpa using h i hi
    rw [hX] at ht
    contradiction
  obtain ⟨a,ha,hwa⟩ := hFalse _ hs3
  obtain ⟨b,hb,hvb⟩ := hFalse _ hs2
  have before (i : ℕ) (h : i ∈ g.inputs) : i < n+p := by
    by_contra hi
    have hX := hAll i h
    simp [operand,hi] at hX
  have ha' := before a ha
  have hb' := before b hb
  rw [operand,ite_eq_left ha'] at hwa
  rw [operand,ite_eq_left hb'] at hvb
  have near (i : ℕ) (h : i ∈ g.inputs) :
      val C (point {v}) i = true ∨ val C (point {w}) i = true := by
    have hi := before i h
    apply earlier i (ep ▸ hi) (live_before (reads i hi h).1 hh)
    simpa [operand,hi] using hAll i h
  have hva := (near a ha).resolve_right (by rw [hwa]; decide)
  have hwb := (near b hb).resolve_left (by rw [hvb]; decide)
  have hne : a ≠ b := fun e => Bool.noConfusion (hva.symm.trans (e ▸ hvb))
  exact ⟨p,g,a,b,hg,hAnd,hh,reads a ha' ha,reads b hb' hb,
    (carries_separate hC hva hwa).1,(carries_separate hC hva hwa).2,
    (carries_separate hC hwb hvb).1,(carries_separate hC hwb hvb).2,
    two_inputs ha hb hne hl.2⟩

theorem covers_edge (hC : Monotone2 C) (he : GraphEval C G) {v w a₀ b₀ : Fin n}
    (hvw : G.Adj v w) (ha₀ : G.Adj v a₀) (_ha₁ : a₀ ≠ w)
    (hb₀ : G.Adj w b₀) (_hb₁ : b₀ ≠ v) (hind : a₀ = b₀ ∨ ¬ G.Adj a₀ b₀) :
    Eligible C v ∨ Eligible C w := by
  by_contra! bad
  obtain ⟨p,g,a,b,hg,hAnd,hj,ha,hb,hva,hwa,hwb,hvb,hs⟩ := meeting_gate hC he hvw
  have pathV : Trace n C (Carries C v) v.val (n+p) :=
    (singleton_path (live_before ha.1 ha.2) hva).tail ⟨hva,ha⟩
  have pathW : Trace n C (Carries C w) w.val (n+p) :=
    (singleton_path (live_before hb.1 hb.2) hwb).tail ⟨hwb,hb⟩
  have uniqueV : ∀ k j j', k < n+p → Carries C v k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.1 k j j'
  have uniqueW : ∀ k j j', k < n+p → Carries C w k → LNext n C k j → LNext n C k j' → j=j' :=
    fun k j j' _ => no_eligible_unique bad.2 k j j'
  let S : Finset (Fin n) := {a₀,b₀}
  let x := point S
  let y := point (insert v S)
  let z := point (insert w S)
  have hzero : val C x C.output = false :=
    point_pair_quiet he (hind.elim (fun e => e ▸ G.irrefl (v := a₀)) id)
  have hY : val C y C.output = true := by
    apply acts_mono hC (point_mono (s := {v,a₀}) (t := insert v S) (by simp [S])) C.output
    exact (he v a₀).2 ha₀
  have hZ : val C z C.output = true := by
    apply acts_mono hC (point_mono (s := {w,b₀}) (t := insert w S) (by simp [S])) C.output
    exact (he w b₀).2 hb₀
  have jout := next_le hj
  have hvj := influence pathV uniqueV (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C y C.output from by rw [hzero,hY]; decide)
  have hwj := influence pathW uniqueW (fun _ hi => (point_insert hi).symm) ReflTransGen.refl (show val C x C.output ≠ val C z C.output from by rw [hzero,hZ]; decide)
  have hdiffV := (hvj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hdiffW := (hwj.resolve_left (fun h => (Nat.not_lt_of_ge jout) h.1)).2
  have hX : val C x (n+p) = false := by
    rw [← Bool.not_eq_true]
    intro htrue
    exact hdiffV (htrue.trans (acts_mono hC (point_mono (Finset.subset_insert _ _)) _ htrue).symm)
  have hyj : val C y (n+p) = true := by
    rw [hX] at hdiffV
    simpa using hdiffV.symm
  have hzj : val C z (n+p) = true := by
    rw [hX] at hdiffW
    simpa using hdiffW.symm
  have hAX : val C x a = val C z a := by
    by_contra h
    rcases influence pathW uniqueW (fun _ hi => (point_insert hi).symm) (live_before ha.1 ha.2) h with h' | h'
    · exact hwa h'.2
    · exact (Nat.not_le_of_gt ha.1.1) h'.1
  have hBX : val C x b = val C y b := by
    by_contra h
    rcases influence pathV uniqueV (fun _ hi => (point_insert hi).symm) (live_before hb.1 hb.2) h with h' | h'
    · exact hvb h'.2
    · exact (Nat.not_le_of_gt hb.1.1) h'.1
  have hYall : ∀ i ∈ g.inputs, operand C y (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hyj
  have hZall : ∀ i ∈ g.inputs, operand C z (n+p) i = true := by
    simpa [val_gate C _ hg,hAnd,GateOp.eval,List.all_eq_true] using hzj
  have hin (i : ℕ) : LNext n C i (n+p) → i ∈ g.inputs := by
    rintro ⟨⟨_,k,g',he',hk,hmem⟩,_⟩
    have e : k=p := by omega
    subst k
    rw [hg] at he'
    cases he'
    exact hmem
  have hxA := hZall a (hin a ha)
  have hxB := hYall b (hin b hb)
  rw [operand,ite_eq_left ha.1.1,← hAX] at hxA
  rw [operand,ite_eq_left hb.1.1,← hBX] at hxB
  have hs' : val C x (n+p) = true := by
    rw [val_gate C _ hg,hAnd,GateOp.eval,List.all_map,List.all_eq_true]
    intro i hi
    rcases hs i hi with rfl | rfl
    · simpa [Function.comp_apply,operand,ha.1.1] using hxA
    · simpa [Function.comp_apply,operand,hb.1.1] using hxB
  rw [hX] at hs'
  contradiction

end EdgeTests

section BranchCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}

theorem value_at_branch {v : Fin n} {x y : Fin n → Bool} (hv : Eligible C v)
    (agrees : ∀ i, i ≠ v → x i = y i)
    (hb : val C x (firstBranch C v hv) = val C y (firstBranch C v hv)) :
    val C x C.output = val C y C.output := by
  by_contra h
  have spec := firstBranch_spec v hv
  have path := singleton_path spec.1 spec.2.1
  rcases influence path (firstBranch_unique v hv) agrees ReflTransGen.refl h with bad | bad
  · exact (Nat.not_lt_of_ge (next_le spec.1)) bad.1
  · exact bad.2 hb

theorem branch_injective (hC : Monotone2 C) (he : GraphEval C G)
    (htwins : ∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard →
      2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u))
    {v w : Fin n} (hv : Eligible C v) (hw : Eligible C w)
    (hdv : 2 ≤ (G.neighborSet v).ncard) (hdw : 2 ≤ (G.neighborSet w).ncard)
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
  obtain ⟨u,hu⟩ := htwins v w hne hadj hdv hdw
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

noncomputable def living (n : ℕ) (C : Circuit) : Finset ℕ :=
  open Classical in (Finset.range (n+C.gates.length)).filter (Live n C)

theorem mem_living {w : ℕ} : w ∈ living n C ↔ w < n+C.gates.length ∧ Live n C w := by
  classical
  simp [living]

theorem input_live (he : GraphEval C G) {v u : Fin n} (hvu : G.Adj v u) :
    Live n C v.val := by
  have hx : val C (point {u}) C.output = false := point_single_quiet he u
  have hy : val C (point {v,u}) C.output = true := (point_pair he v u).2 hvu
  obtain ⟨i,hi,trace⟩ := difference C (point {u}) (point {v,u}) C.output ReflTransGen.refl
    (by rw [hx,hy]; decide)
  have ei : i=v := by
    by_contra h
    exact hi ((point_insert h).symm)
  subst i
  rcases trace.cases_head with h | ⟨b,hb,_⟩
  · rw [h]
    exact .refl
  · exact live_before hb.2.1 hb.2.2

theorem live_readers_nonempty {a : ℕ} (ha : Live n C a) (hneq : a ≠ C.output) :
    (readers n C a).Nonempty := by
  rcases ha.cases_head with h | ⟨b,hb,hpath⟩
  · exact (hneq h).elim
  · exact ⟨b,mem_readers.2 ⟨hb,hpath⟩⟩

theorem readers_filter (a : ℕ) :
    open Classical in readers n C a = (living n C).filter (fun b => LNext n C a b) := by
  classical
  ext b
  simp only [mem_readers,Finset.mem_filter,mem_living]
  exact ⟨fun h => ⟨⟨next_in_range h.1,h.2⟩,h⟩, And.right⟩

theorem incoming_bound {j : ℕ} (hC : Monotone2 C) (hj : j ∈ living n C) :
    open Classical in ((living n C).filter fun i => LNext n C i j).card ≤ if j<n then 0 else 2 := by
  classical
  by_cases hi : j < n
  · rw [ite_eq_left hi]
    apply Nat.le_of_eq
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.2
    intro i hm
    obtain ⟨_,⟨_,p,g,hg,hp,_⟩,_⟩ := Finset.mem_filter.mp hm
    omega
  rw [ite_eq_right hi]
  have hj' := (mem_living.1 hj).1
  let p := j-n
  have hp : p < C.gates.length := by dsimp [p]; omega
  have he : j=n+p := by dsimp [p]; omega
  let g := C.gates[p]
  have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp,rfl⟩
  have hsub : ((living n C).filter fun i => LNext n C i j) ⊆ g.inputs.toFinset := by
    intro a ha
    obtain ⟨_,⟨_,q,g',hg',hq,hm⟩,_⟩ := Finset.mem_filter.1 ha
    have ep : p=q := by omega
    subst q
    rw [hg] at hg'
    cases hg'
    exact List.mem_toFinset.2 hm
  exact (Finset.card_le_card hsub).trans (g.inputs.toFinset_card_le.trans
    (hC g (List.mem_of_getElem? hg)).2)

theorem branch_budget (hC : Monotone2 C) (he : GraphEval C G)
    (hdegree : ∀ v : Fin n, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in n + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  have hSub : Finset.range n ⊆ W := by
    intro a ha
    have hi := Finset.mem_range.1 ha
    let v : Fin n := ⟨a,hi⟩
    obtain ⟨u,hu⟩ := hdegree v
    exact mem_living.2 ⟨by omega,input_live he hu⟩
  have hW : W.card = n + S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hSub
    have e : W \ Finset.range n = S := by ext a; simp [S]
    rw [e,Finset.card_range] at h
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
  change n+B.card ≤ C.gates.length+1
  omega

end BranchCount

section CircuitBound

theorem step614 :
    ∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ v : Fin n, ∃ w : Fin n, G.Adj v w) → (∀ v w : Fin n, v ≠ w → ¬ G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ u : Fin n, ¬ (G.Adj v u ↔ G.Adj w u)) → (∀ v w : Fin n, G.Adj v w → 2 ≤ (G.neighborSet v).ncard → 2 ≤ (G.neighborSet w).ncard → ∃ a b : Fin n, G.Adj v a ∧ a ≠ w ∧ G.Adj w b ∧ b ≠ v ∧ (a = b ∨ ¬ G.Adj a b)) → (∀ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → 2 ≤ (G.neighborSet u).ncard → 2 ≤ (G.neighborSet v).ncard → u ∈ S ∨ v ∈ S) → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → GraphEval C G → n + t ≤ C.size + 1 := by
  open PEqualNP.Outside.L_meta_17744.LB in
  classical
  intro n t G C hdegree htwins hadj ht hC he
  by_cases hn : n=0
  · subst n
    have ht0 := ht ∅ (fun u => Fin.elim0 u)
    simp at ht0
    omega
  have hE : GraphEval C G := he
  let v : Fin n := ⟨0, by omega⟩
  obtain ⟨w, hve⟩ := hdegree v
  have ho := (edge_at_output hE hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hbudget := branch_budget hC hE hdegree ho'
  exact (Nat.add_le_add_left (htc.trans hcap) n).trans hbudget

end CircuitBound

section MinimumDegree
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
variable {n t : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
def NoSq (G : SimpleGraph (Fin n)) := ∀ a b c d : Fin n, a≠c → b≠d →
  ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)
theorem other_neighbor {x y : Fin n} (deg : 2 ≤ (G.neighborSet x).ncard) :
    ∃ a, G.Adj x a ∧ a ≠ y := by
  obtain ⟨a,b,ha,hb,ab⟩ := (Set.one_lt_ncard_iff (s := G.neighborSet x)).mp deg
  by_cases ay : a=y
  · exact ⟨b,hb,ay ▸ ab.symm⟩
  · exact ⟨a,ha,ay⟩

theorem min_two_bound (ns : NoSq G) (deg : ∀ x, 2 ≤ (G.neighborSet x).ncard)
    (minimal : ∀ S : Finset (Fin n), CoverPromise.IsVertexCover G S → t ≤ S.card)
    (mono : Monotone2 C) (works : GraphEval C G) : n + t ≤ C.size+1 := by
  apply step614 n t G C _ _ _ _ mono works
  · intro v
    obtain ⟨a,ha,_⟩ := other_neighbor (y := v) (deg v)
    exact ⟨a,ha⟩
  · intro v w vw _ dv _
    by_contra! twin
    obtain ⟨a,b,ha,hb,ab⟩ := (Set.one_lt_ncard_iff (s := G.neighborSet v)).mp dv
    exact ns v a w b vw ab ⟨ha,((twin a).mp ha).symm,(twin b).mp hb,hb.symm⟩
  · intro v w e dv dw
    obtain ⟨a,ha,aw⟩ := other_neighbor (y := w) dv
    obtain ⟨b,hb,bv⟩ := other_neighbor (y := v) dw
    exact ⟨a,b,ha,aw,hb,bv,Or.inr (fun ab => ns v a b w bv.symm aw ⟨ha,ab,hb.symm,e.symm⟩)⟩
  · exact fun S cv => minimal S (fun u v e => cv u v e (deg u) (deg v))

end MinimumDegree
end LB
def meet (C : Circuit) (a b : Nat) : Circuit := ⟨C.gates ++ [⟨.and,[a,b]⟩],26+C.size⟩
def wire (C : Circuit) (w : Nat) (v : List Bool) := (C.wires v).getD w false
theorem meetEval (C : Circuit) (a b : Nat) (v : List Bool) (hv : v.length=26) :
    (meet C a b).eval v = (wire C a v && wire C b v) := by
  let W := C.wires v
  let bit := wire C a v && wire C b v
  have ws : (meet C a b).wires v = W ++ [bit] := by
    change (C.gates++[_]).foldl _ v = W++[bit]
    rw [List.foldl_append]
    change W ++ [wire C a v && (wire C b v && true)] = W ++ [wire C a v && wire C b v]
    simp only [Bool.and_true]
  have len : W.length = 26+C.size := by
    change (wf C.gates v).length=26+C.size
    rw [wf_len,hv] <;> rfl
  change ((meet C a b).wires v).getD (26+C.size) false = bit
  rw [ws,←len]
  exact getD_snoc_eq _ _

abbrev R := Fin 24
def raw (i : Fin 26) : W := (Nat.ble 13 i.val, Fin.ofNat 13 (i.val%13))
def orig (p l : I) (i : R) : W :=
  (Nat.ble 12 i.val, (if Nat.ble 12 i.val then l else p) + Fin.ofNat 13 (i.val%12+1))
def back (p l : I) (i : Fin 26) : Option R :=
  let d := (raw i).2 - (if (raw i).1 then l else p)
  if d=0 then none else some (Fin.ofNat 24 ((if (raw i).1 then 12 else 0)+(d.val-1)))

def coord (w : W) : Fin 26 := Fin.ofNat 26 ((if w.1 then 13 else 0) + w.2.val)
theorem coord_raw : ∀ i : Fin 26, coord (raw i) = i := by decide +kernel
theorem raw_coord : ∀ w : W, raw (coord w) = w := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem back_orig : ∀ (p l : I) (u : R), back p l (coord (orig p l u)) = some u := by decide +kernel
def recOK (p l : I) (i : Fin 26) : Bool :=
  match back p l i with
  | some u => decide (raw i = orig p l u)
  | none => decide (¬free p l (raw i))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem recOK_true : ∀ (p l : I) (i : Fin 26), recOK p l i = true := by decide +kernel
theorem rec_orig (p l : I) (i : Fin 26) : match back p l i with
  | some u => raw i = orig p l u
  | none => ¬free p l (raw i) := by
  have h := recOK_true p l i
  cases e : back p l i <;> simpa [recOK,e] using h

theorem inverseBack (p l : I) (i : Fin 26) (u : R) : back p l i = some u ↔ raw i = orig p l u := by
  constructor
  · intro h
    have e := rec_orig p l i
    simpa [h] using e
  · intro h
    calc
      back p l i = back p l (coord (raw i)) := by rw [coord_raw]
      _ = some u := by rw [h,back_orig]
theorem origInj (p l : I) (u v : R) (h : orig p l u = orig p l v) : u = v := by
  have e := congrArg (fun w => back p l (coord w)) h
  simpa only [back_orig, Option.some.injEq] using e

set_option maxHeartbeats 0 in
theorem origFree : ∀ p l : I, ∀ u : R, free p l (orig p l u) := by decide +kernel

def leftPoint (i : Fin 12) : R := ⟨i.val,by omega⟩
def rightLine (i : Fin 12) : R := ⟨12+i.val,by omega⟩
theorem disjointMatch : ∀ i j : Fin 12, i ≠ j →
    leftPoint i ≠ leftPoint j ∧ leftPoint i ≠ rightLine j ∧
    rightLine i ≠ leftPoint j ∧ rightLine i ≠ rightLine j := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem matchHit : ∀ p l : I, p ∈ lines l → ∀ i : Fin 12,
    link (orig p l (leftPoint i)) (orig p l (rightLine i)) := by decide +kernel

theorem symLink : ∀ u v : W, link u v → link v u := by decide +kernel
def resGraph (p l : I) : SimpleGraph R where
  Adj u v := link (orig p l u) (orig p l v)
  symm := ⟨fun _ _ h => symLink _ _ h⟩
  loopless := ⟨fun u => by simp [link]⟩

theorem enumerateFree (p l : I) (w : W) (h : free p l w) : ∃ u : R, orig p l u = w := by
  have e := rec_orig p l (coord w)
  cases b : back p l (coord w) with
  | none =>
    have bad : ¬free p l w := by simpa [b,raw_coord] using e
    exact (bad h).elim
  | some u =>
    have eu : w = orig p l u := by simpa [b,raw_coord] using e
    exact ⟨u, eu.symm⟩

theorem twoNear (p l : I) (x : R) : ∃ y z : R, y ≠ z ∧
    link (orig p l x) (orig p l y) ∧ link (orig p l x) (orig p l z) := by
  obtain ⟨a,b,ab,ha,hb,xa,xb⟩ := twoNeighbors p l (orig p l x) (origFree p l x)
  obtain ⟨u,hu⟩ := enumerateFree p l a ha
  obtain ⟨v,hv⟩ := enumerateFree p l b hb
  refine ⟨u,v,?_,by simpa only [hu] using xa,by simpa only [hv] using xb⟩
  intro eq
  exact ab (hu.symm.trans ((congrArg (orig p l) eq).trans hv))

theorem geomFloor (p l : I) (flag : p∈lines l) (E : Circuit) (hm : Monotone2 E)
    (he : LB.GraphEval E (resGraph p l)) : 36 ≤ E.size+1 := by
  apply LB.min_two_bound (t:=12) (G:=resGraph p l) _ _ _ hm he
  · intro a b c d ac bd h
    have u : orig p l a ≠ orig p l c := fun e => ac (origInj p l _ _ e)
    have v : orig p l b ≠ orig p l d := fun e => bd (origInj p l _ _ e)
    exact noBox _ _ _ _ u v ⟨h.1,symLink _ _ h.2.1,symLink _ _ h.2.2.2,h.2.2.1⟩
  · intro x
    obtain ⟨y,z,yz,hy,hz⟩ := twoNear p l x
    exact (Set.one_lt_ncard_iff (s:=(resGraph p l).neighborSet x)).mpr ⟨y,z,hy,hz,yz⟩
  · intro S cover
    let pick (i : Fin 12) : R := if leftPoint i ∈ S then leftPoint i else rightLine i
    have chosen (i : Fin 12) : pick i ∈ S := by
      by_cases h : leftPoint i ∈ S
      · simpa [pick,h] using h
      · simpa [pick,h] using (cover _ _ (matchHit p l flag i)).resolve_left h
    have injective : Function.Injective pick := by
      intro i j eq
      by_contra ne
      obtain ⟨hll,hlr,hrl,hrr⟩ := disjointMatch i j ne
      by_cases hi : leftPoint i ∈ S <;> by_cases hj : leftPoint j ∈ S <;>
        simp only [pick,hi,hj,ite_true,ite_false] at eq
      · exact hll eq
      · exact hlr eq
      · exact hrl eq
      · exact hrr eq
    let f (i : Fin 12) : {w // w ∈ S} := ⟨pick i,chosen i⟩
    simpa using Fintype.card_le_of_injective f (fun i j e => injective (congrArg Subtype.val e))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem rawPoint : ∀ (a b : W) (i : Fin 26), decide (raw i=a ∨ raw i=b) =
    Fin.append (fun p : I => decide (p ∈ pointOf a ∪ pointOf b))
      (fun l : I => decide (l ∈ lineOf a ∪ lineOf b)) i := by decide +kernel

theorem pointInput (p l : I) (u v : R) :
    List.ofFn (liftIn (back p l) (LB.point {u,v})) =
      incidenceInput (pointOf (orig p l u) ∪ pointOf (orig p l v))
        (lineOf (orig p l u) ∪ lineOf (orig p l v)) := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  rw [←rawPoint]
  cases h : back p l i with
  | none =>
    have hu : raw i ≠ orig p l u := fun e => by have := (inverseBack p l i u).2 e; simp [h] at this
    have hv : raw i ≠ orig p l v := fun e => by have := (inverseBack p l i v).2 e; simp [h] at this
    simp [liftIn,h,hu,hv]
  | some w =>
    have hu := inverseBack p l i u
    have hv := inverseBack p l i v
    simp only [h,Option.some.injEq] at hu hv
    simp [liftIn,h,LB.point,hu,hv]

theorem unconditional34 (p l : I) (C D : Circuit) (flag : p ∈ lines l) (same : C.gates=D.gates) (mc : Monotone2 C)
    (pos : ∀ a b : I, a ≠ p → b ≠ l → a ∈ lines b →
      ∀ F ∈ [C,D], F.eval (incidenceInput {a} {b})=true)
    (dis : Disjoint (faults p l C) (faults p l D)) : 34 ≤ C.size := by
  let J := meet C C.output D.output
  let E := reindex (back p l) J
  have mj : Monotone2 J := by
    intro g hg
    rcases List.mem_append.mp hg with hh | hh
    · exact mc g hh
    · obtain rfl := List.mem_singleton.mp hh
      exact ⟨Or.inl rfl,by change 2 ≤ 2; exact le_rfl⟩
  have md : Monotone2 D := fun g hg => mc g (same.symm ▸ hg)
  have ed (xs) : wire C D.output xs = D.eval xs := by
    change (wf C.gates xs).getD D.output false = (wf D.gates xs).getD D.output false
    rw [same]
  have hex : LB.GraphEval E (resGraph p l) := by
    intro u v
    change (reindex (back p l) J).eval (List.ofFn (LB.point {u,v})) = true ↔ link (orig p l u) (orig p l v)
    rw [reindex_eval,pointInput,meetEval _ _ _ _ (by simp [incidenceInput]),ed,Bool.and_eq_true]
    rw [← link_logic]
    obtain ⟨pu,lu⟩ := frees p l _ (origFree p l u)
    obtain ⟨pv,lv⟩ := frees p l _ (origFree p l v)
    obtain ⟨pc,lc⟩ := twoBound (orig p l u) (orig p l v)
    apply small_exact p l C D same mc pos dis
    · simpa using And.intro pu pv
    · simpa using And.intro lu lv
    · omega
    · omega
    · intro k; exact (Finset.card_le_card Finset.inter_subset_left).trans pc
    · intro k; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans lc
  have num := geomFloor p l flag E (reindex_mono (back p l) J mj) hex
  have sz : E.size = C.size+1 := by simp [E,J,reindex,meet,Circuit.size]
  omega

end PEqualNP.Outside.L_meta_17744

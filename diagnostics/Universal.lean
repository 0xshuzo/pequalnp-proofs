import Mathlib

namespace SmallCover2585
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

theorem pairCount (N : Y → Finset X) (R : Finset Y) (C : Finset X)
    (wide : ∀ y∈R, 2 ≤ (N y).card) (inside : ∀ y∈R,N y ⊆ C)
    (linear : ∀ u v, u≠v → (N u∩N v).card ≤ 1) : R.card ≤ C.card.choose 2 := by
  classical
  let f (y : Y) := if h : 2 ≤ (N y).card then
    Classical.choose (Finset.exists_subset_card_eq h) else ∅
  have info (y : Y) (hy : y∈R) : f y ⊆ N y ∧ (f y).card = 2 := by
    have w := wide y hy
    simpa only [f,dif_pos w] using (Classical.choose_spec (Finset.exists_subset_card_eq w))
  rw [←Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn f
  · intro y hy
    exact Finset.mem_powersetCard.mpr ⟨(info y hy).1.trans (inside y hy),(info y hy).2⟩
  · intro a ha b hb eq
    by_contra ne
    have sub : f a ⊆ N a∩N b :=
      Finset.subset_inter (info a ha).1 (by rw [eq];exact (info b hb).1)
    have bound := (Finset.card_le_card sub).trans (linear a b ne)
    rw [(info a ha).2] at bound
    omega

theorem trimAny {k : ℕ} [Fintype Y] (N : Y→Finset (Fin k))
    (linear : ∀ a b,a≠b → (N a∩N b).card ≤ 1)
    (f₀ : Fin k→Y) (injective : Function.Injective f₀) (incident : ∀ i,i∈N (f₀ i))
    : ∃ (f : Fin k→Y) (R : Finset Y) (r j : ℕ), Function.Injective f ∧
      (∀ i,i∈N (f i) ∧ f i∈R) ∧ (∀ y,y∉R → (N y).card ≤ 1) ∧
      r ≤ k ∧ j ≤ r.choose 2 ∧ j+r ≤ k.choose 2 ∧ k+R.card ≤ 2*k+j := by
  classical
  let H := Finset.univ.filter (fun y : Y => 2 ≤ (N y).card)
  let occupied (f : Fin k→Y) := Finset.univ.filter (fun i => f i∈H)
  let valid := Finset.univ.filter (fun f : Fin k→Y => Function.Injective f ∧ ∀ i,i∈N (f i))
  have start : f₀∈valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _,injective,incident⟩
  obtain ⟨f,hf,best⟩ := valid.exists_max_image (fun f => (occupied f).card) ⟨f₀,start⟩
  obtain ⟨inj,adj⟩ := (Finset.mem_filter.mp hf).2
  let D := Finset.univ.image f
  let J := H \ D
  let A := occupied f
  have loc (y : Y) (hy : y∈J) : N y⊆A := by
    obtain ⟨wide,miss⟩ := Finset.mem_sdiff.mp hy
    intro i hi
    by_contra off
    have low : f i∉H := fun u => off (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u⟩)
    have fresh (j : Fin k) : f j ≠ y := fun e => miss (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e⟩)
    let g := Function.update f i y
    have validG : g∈valid := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
      · intro a b he
        by_cases ai : a=i <;> by_cases bi : b=i
        · exact ai.trans bi.symm
        · subst a
          exact False.elim (fresh b (by simpa [g,Function.update_of_ne bi] using he.symm))
        · subst b
          exact False.elim (fresh a (by simpa [g,Function.update_of_ne ai] using he))
        · exact inj (by simpa only [g,Function.update_of_ne ai,Function.update_of_ne bi] using he)
      · intro j
        by_cases ji : j=i
        · subst j;simpa [g] using hi
        · simpa [g,Function.update_of_ne ji] using adj j
    have sg : insert i A ⊆ occupied g := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|a
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [g] using wide⟩
      · have ji : j≠i := fun e => off (e ▸ a)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
          simpa [g,Function.update_of_ne ji] using (Finset.mem_filter.mp a).2⟩
    have stric := Finset.card_le_card sg
    rw [Finset.card_insert_of_notMem off] at stric
    have bd := best g validG
    change (occupied g).card ≤ A.card at bd
    omega
  have wH (y : Y) (hy : y∈H) : 2 ≤ (N y).card := (Finset.mem_filter.mp hy).2
  have j1 := pairCount N J A (fun y hy => wH y (Finset.mem_sdiff.mp hy).1) loc linear
  have j2 := pairCount N H (Finset.univ : Finset (Fin k)) wH (fun _ _ => Finset.subset_univ _) linear
  simp only [Finset.card_univ,Fintype.card_fin] at j2
  have dcard : D.card=k := by
    rw [show D=Finset.univ.image f from rfl,Finset.card_image_of_injective _ inj]
    simp
  have aLe : A.card ≤ k := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      (Finset.card_le_univ A : A.card ≤ Fintype.card (Fin k))
  have imageA : A.image f=H∩D := by
    ext y
    constructor
    · rintro h
      obtain ⟨i,ha,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp ha).2,Finset.mem_image_of_mem f (Finset.mem_univ i)⟩
    · intro h
      obtain ⟨hr,hd⟩ := Finset.mem_inter.mp h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image_of_mem f (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
  have idcard : (H∩D).card=A.card := by rw [←imageA,Finset.card_image_of_injective _ inj]
  have partition : J.card+A.card=H.card := by
    rw [←idcard,show J=H\D from rfl]
    exact Finset.card_sdiff_add_card_inter H D
  refine ⟨f,D∪J,A.card,J.card,inj,fun i=>⟨adj i,Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_univ i))⟩,?_,aLe,j1,partition.le.trans j2,?_⟩
  · intro y hy
    by_contra! big
    have hH : y∈H := Finset.mem_filter.mpr ⟨Finset.mem_univ _,big⟩
    by_cases hd : y∈D
    · exact hy (Finset.mem_union_left _ hd)
    · exact hy (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hH,hd⟩))
  · have sz := Finset.card_union_le D J
    omega

end SmallCover2585

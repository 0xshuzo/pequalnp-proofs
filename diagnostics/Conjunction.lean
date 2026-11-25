import PEqualNP.Defs

open PEqualNP.GenericRejection PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace PlaneTransversal2583

theorem overlap {N : ℕ} (S : Fin N → Finset (Fin N))
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    {l m : Fin N} (hne : l ≠ m) : (S l ∩ S m).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro p hp r hr
  by_contra e
  obtain ⟨u, _, hu⟩ := join p r e
  exact hne ((hu l ⟨(Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hr).1⟩).trans
    (hu m ⟨(Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hr).2⟩).symm)

theorem privateCount {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y : Finset (Fin N)) {l : Fin N} (hl : l ∉ Y) :
    q+1 ≤ Y.card + (S l ∩ zeroSet S Y).card := by
  classical
  let cap := Y.biUnion fun m => S l ∩ S m
  have hc : cap.card ≤ Y.card := by
    simpa [cap] using Finset.card_biUnion_le_card_mul Y (fun m => S l ∩ S m) 1
      (fun m hm => overlap S join (fun h => hl (h ▸ hm)))
  have incl : S l ⊆ cap ∪ (S l ∩ zeroSet S Y) := by
    intro p hp
    by_cases h : ∃ m ∈ Y, p ∈ S m
    · obtain ⟨m, hm, hpm⟩ := h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hp,hpm⟩⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hp' => h ⟨m,hm,hp'⟩⟩
  have hb := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  rw [weight] at hb
  omega

def hit {N : ℕ} (S : Fin N → Finset (Fin N)) (X Y : Finset (Fin N)) : Prop :=
  ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l

theorem avoid {q N : ℕ} (S : Fin N → Finset (Fin N)) (weight : ∀ l, (S l).card = q+1)
    (pencil : ∀ p : Fin N, (Finset.univ.filter (fun l => p∈S l)).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (U V : Finset (Fin N)) (hu : U.card ≤ q) (hv : V.card ≤ q) :
    ∃ X Y, ¬hit S X Y ∧
      (∀ p ∈ U, hit S (insert p X) Y) ∧ (∀ l ∈ V, hit S X (insert l Y)) := by
  classical
  have sel (p : Fin N) : ∃ l, p∈S l ∧ l∉V := by
    by_contra! no
    have sub : (Finset.univ.filter (fun l => p∈S l)) ⊆ V := by
      intro l hl
      exact no l (Finset.mem_filter.mp hl).2
    have bound := Finset.card_le_card sub
    rw [pencil] at bound
    omega
  choose f hf using sel
  let Y := U.image f
  let X := zeroSet S Y
  have small : Y.card≤q := (Finset.card_image_le).trans hu
  have dis (p) (hp : p∈X) (l) (hl : l∈Y) : p∉S l := (Finset.mem_filter.mp hp).2 l hl
  refine ⟨X, Y, ?_, ?_, ?_⟩
  · rintro ⟨p,hp,l,hl,hi⟩
    exact dis p hp l hl hi
  · intro p hp
    exact ⟨p,Finset.mem_insert_self _ _,f p,Finset.mem_image_of_mem _ hp,(hf p).1⟩
  · intro l hl
    have off : l∉Y := by
      intro h
      obtain ⟨p,_,h⟩ := Finset.mem_image.mp h
      apply (hf p).2
      simpa only [h] using hl
    have bound := privateCount S weight join Y off
    have hn : 0 < (S l ∩ X).card := by
      change 0 < (S l ∩ zeroSet S Y).card
      omega
    obtain ⟨p,hp⟩ := Finset.card_pos.mp hn
    exact ⟨p, (Finset.mem_inter.mp hp).2, l, Finset.mem_insert_self _ _, (Finset.mem_inter.mp hp).1⟩

theorem noSmallConjunction {q N m n : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (pencil : ∀ p : Fin N, (Finset.univ.filter (fun l => p∈S l)).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (A : Fin m → Finset (Fin N) → Finset (Fin N) → Prop)
    (B : Fin n → Finset (Fin N) → Finset (Fin N) → Prop)
    (u : Fin m → Fin N) (v : Fin n → Fin N)
    (blindA : ∀ i X Y, A i (insert (u i) X) Y ↔ A i X Y)
    (blindB : ∀ j X Y, B j X (insert (v j) Y) ↔ B j X Y)
    (exactF : ∀ X Y, ((∀ i, A i X Y) ∧ (∀ j, B j X Y)) ↔ hit S X Y) :
    q+2 ≤ m+n := by
  classical
  by_contra! size
  have bad (X Y : Finset (Fin N)) (no : ¬hit S X Y)
      (aa : ∀ i, hit S (insert (u i) X) Y) (bb : ∀ j, hit S X (insert (v j) Y)) : False := by
    apply no
    apply (exactF X Y).mp
    refine ⟨?_,?_⟩
    · exact fun i => (blindA i X Y).mp (((exactF _ _).mpr (aa i)).1 i)
    · exact fun j => (blindB j X Y).mp (((exactF _ _).mpr (bb j)).2 j)
  by_cases hm : m=0
  · subst m
    apply bad Finset.univ ∅
    · rintro ⟨_,_,_,hl,_⟩
      simpa using hl
    · intro i; exact i.elim0
    · intro j
      have hp : 0 < (S (v j)).card := by rw [weight]; omega
      obtain ⟨p,hi⟩ := Finset.card_pos.mp hp
      exact ⟨p, Finset.mem_univ _, v j, Finset.mem_insert_self _ _, hi⟩
  by_cases hn : n=0
  · subst n
    apply bad ∅ Finset.univ
    · rintro ⟨p,hp,_⟩
      simpa using hp
    · intro i
      have hl : 0 < (Finset.univ.filter (fun l => u i∈S l)).card := by rw [pencil]; omega
      obtain ⟨l,hi⟩ := Finset.card_pos.mp hl
      exact ⟨u i,Finset.mem_insert_self _ _,l,Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · intro i; exact i.elim0
  let U := Finset.univ.image u
  let V := Finset.univ.image v
  have hu : U.card≤m := (Finset.card_image_le).trans (by simp)
  have hv : V.card≤n := (Finset.card_image_le).trans (by simp)
  obtain ⟨X,Y,no,aa,bb⟩ := avoid S weight pencil join U V (by omega) (by omega)
  exact bad X Y no (fun i => aa _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    (fun j => bb _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))

theorem pencilConjunction {N : ℕ} (S : Fin N → Finset (Fin N)) (p : Fin N)
    (X Y : Finset (Fin N)) :
    hit S X Y ↔ hit S (insert p X) Y ∧ ∀ l, p∈S l → hit S X (insert l Y) := by
  constructor
  · rintro ⟨r,hr,l,hl,inc⟩
    exact ⟨⟨r,Finset.mem_insert_of_mem hr,l,hl,inc⟩,
      fun j _ => ⟨r,hr,l,Finset.mem_insert_of_mem hl,inc⟩⟩
  · rintro ⟨⟨r,hr,l,hl,inc⟩,all⟩
    rcases Finset.mem_insert.mp hr with h|h
    · subst r
      simpa only [Finset.insert_eq_of_mem hl] using all l inc
    · exact ⟨r,h,l,hl,inc⟩

end PlaneTransversal2583

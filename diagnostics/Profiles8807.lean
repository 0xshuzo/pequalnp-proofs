import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8807.Profiles
open Finset
def covered {n k} (P : Fin k → Finset (Fin n)) (I : Fin n → Finset (Fin k)) (l : Fin n) :=
  (I l).biUnion P
theorem two_points {n} {S : Fin n → Finset (Fin n)}
    (unique : ∀ p r, p≠r → ∃! l,p∈S l ∧ r∈S l) {l t} {X : Finset (Fin n)}
    (rich : 1<X.card) (a : X⊆S l) (b : X⊆S t) : l=t := by
  obtain ⟨p,hp,r,hr,pq⟩ := one_lt_card.mp rich
  exact (unique p r pq).unique ⟨a hp,a hr⟩ ⟨b hp,b hr⟩

theorem profiles {n k : Nat} (S : Fin n → Finset (Fin n))
    (unique : ∀ p r, p≠r → ∃! l,p∈S l ∧ r∈S l) (K : Finset (Fin n))
    (P : Fin k → Finset (Fin n)) (I : Fin n → Finset (Fin k))
    (many : ∀ l∈K, 1<(covered P I l).card) (sound : ∀ l∈K, covered P I l⊆S l) :
    ∃ s≤k, K.card ≤ (k-s)+s.choose 2 := by
  classical
  let T : Finset (Fin k) := univ.filter (fun i => (P i).card=1)
  let H := K.filter (fun l => ∃ i∈I l, 1<(P i).card)
  have hs : H⊆K := filter_subset _ _
  have sub {l i} (hl : l∈K) (hi : i∈I l) : P i⊆S l :=
    fun _ hp => sound l hl (mem_biUnion.mpr ⟨i,hi,hp⟩)
  have big : H.card ≤ k-T.card := by
    choose! id ok using (fun l (hl : l∈H) => (mem_filter.mp hl).2)
    have count : H.card ≤ (univ\T).card := by
      apply card_le_card_of_injOn id
      · intro l hl
        refine mem_sdiff.mpr ⟨mem_univ _,?_⟩
        intro mem
        have small : (P (id l)).card=1 := (mem_filter.mp mem).2
        have rich := (ok l hl).2
        omega
      · intro l hl t ht eq
        apply two_points unique (ok l hl).2 (sub (hs hl) (ok l hl).1)
        simpa only [eq] using sub (hs ht) (ok t ht).1
    simpa using count
  have findPair (l) (hl : l∈K\H) : ∃ U : Finset (Fin k), U⊆T ∧ U.card=2 ∧
      U⊆I l ∧ 1<(U.biUnion P).card := by
    obtain ⟨hk,notbig⟩ := mem_sdiff.mp hl
    have small (i) (hi : i∈I l) : (P i).card≤1 :=
      Nat.le_of_not_gt (fun gt => notbig (mem_filter.mpr ⟨hk,i,hi,gt⟩))
    obtain ⟨p,hp,r,hr,pr⟩ := one_lt_card.mp (many l hk)
    obtain ⟨a,ha,pa⟩ := mem_biUnion.mp hp
    obtain ⟨b,hb,rb⟩ := mem_biUnion.mp hr
    have ab : a≠b := by
      rintro rfl
      exact pr (card_le_one.mp (small a ha) p pa r rb)
    have aT : a∈T := mem_filter.mpr ⟨mem_univ _,Nat.le_antisymm (small a ha) (card_pos.mpr ⟨p,pa⟩)⟩
    have bT : b∈T := mem_filter.mpr ⟨mem_univ _,Nat.le_antisymm (small b hb) (card_pos.mpr ⟨r,rb⟩)⟩
    refine ⟨{a,b},by simp [aT,bT],by simp [ab],by simp [ha,hb],?_⟩
    exact one_lt_card.mpr ⟨p,mem_biUnion.mpr ⟨a,by simp,pa⟩,r,mem_biUnion.mpr ⟨b,by simp,rb⟩,pr⟩
  choose! f good using findPair
  have light : (K\H).card≤(T.powersetCard 2).card := by
    apply card_le_card_of_injOn f
    · intro l hl
      exact mem_powersetCard.mpr ⟨(good l hl).1,(good l hl).2.1⟩
    · intro l hl t ht eq
      have part (u) (hu : u∈K\H) : (f u).biUnion P⊆S u := by
        intro v hv
        obtain ⟨i,hi,vi⟩ := mem_biUnion.mp hv
        exact sub (mem_sdiff.mp hu).1 ((good u hu).2.2.1 hi) vi
      apply two_points unique (good l hl).2.2.2 (part l hl)
      simpa only [eq] using part t ht
  rw [card_powersetCard] at light
  have sum := card_sdiff_add_card_eq_card hs
  refine ⟨T.card,by simpa using card_le_card (subset_univ T),by omega⟩

theorem fifteen {n k} (S : Fin n → Finset (Fin n))
    (unique : ∀ p r, p≠r → ∃! l,p∈S l ∧ r∈S l) (K : Finset (Fin n)) (big : 100<K.card)
    (P : Fin k → Finset (Fin n)) (I : Fin n → Finset (Fin k))
    (many : ∀ l∈K, 1<(covered P I l).card) (sound : ∀ l∈K, covered P I l⊆S l) : 15≤k := by
  obtain ⟨s,sk,pay⟩ := profiles S unique K P I many sound
  by_contra! small
  have hi : s≤14 := by omega
  have blk : ∀ i : Fin 15, 14-i.val+i.val.choose 2≤100 := by decide +kernel
  have lim := blk ⟨s,by omega⟩
  change 14-s+s.choose 2≤100 at lim
  omega
end PEqualNP.Outside.L_meta_8807.Profiles

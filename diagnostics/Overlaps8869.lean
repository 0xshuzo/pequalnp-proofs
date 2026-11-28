import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8869.Overlap
open Finset
open Finset in
theorem colors {n} (f : Nat → Fin n × Fin n) (S : Finset Nat) :
    ∃ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) ∧
      n≤S.card+(univ.image c).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨id,by simp,by simp⟩
  | @insert j S hj ih =>
    obtain ⟨c,ok,cnt⟩ := ih
    let a := c (f j).1
    let b := c (f j).2
    let up := fun z : Fin n => if z=a then b else z
    let d := up ∘ c
    refine ⟨d,?_,?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl|hh
      · change up a=up b
        simp [up]
      · exact congrArg up (ok k hh)
    · have sub : univ.image c ⊆ insert a (univ.image d) := by
        intro t ht
        obtain ⟨u,_,rfl⟩ := mem_image.mp ht
        by_cases eq : c u=a
        · exact mem_insert.mpr (.inl eq)
        · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_univ _,by simp [d,up,eq]⟩)
      have h := (card_le_card sub).trans (card_insert_le _ _)
      rw [card_insert_of_notMem hj]
      omega

open Finset in
theorem graph_count {n : ℕ} (S : Finset ℕ) (f : ℕ → Fin n × Fin n) (X : Finset (Fin n))
    (hX : ∀ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) →
      ∀ u ∈ X, ∀ v ∈ X, c u=c v) : X.card≤S.card+1 := by
  classical
  rcases X.eq_empty_or_nonempty with rfl|⟨v,hv⟩
  · simp
  obtain ⟨c,ok,hc⟩ := colors f S
  have sub : univ.image c⊆insert (c v) ((univ\X).image c) := by
    intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    by_cases hu : u∈X
    · exact mem_insert.mpr (.inl (hX c ok u hu v hv))
    · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_sdiff.mpr ⟨mem_univ _,hu⟩,rfl⟩)
  have hc' := (card_le_card sub).trans (card_insert_le _ _)
  have imgs : ((univ\X).image c).card≤(univ\X).card := card_image_le
  have add := card_sdiff_add_card_eq_card (subset_univ X)
  simp only [card_univ,Fintype.card_fin] at add
  omega

theorem overlap_cost {n s : Nat} (V : Nat → Finset (Fin n)) (a b : Nat → Nat)
    (raw : ∀ w<n,(V w).card≤1) (back : ∀ j<s,a j<n+j ∧ b j<n+j)
    (cont : ∀ j<s,V (n+j)⊆ V (a j) ∪ V (b j)) (w : Nat) (valid : w<n+s) :
    (V w).card + ((range s).filter (fun j => ((V (a j)) ∩ (V (b j))).Nonempty)).card ≤ s+1 := by
  classical
  let common (j : Nat) := ((V (a j)) ∩ (V (b j))).Nonempty
  let F := (range s).filter (fun j => ¬common j)
  have card : F.card+((range s).filter common).card=s := by
    rw [Nat.add_comm]
    simpa only [card_range] using card_filter_add_card_filter_not (s:=range s) common
  by_cases hv : (V w).Nonempty
  · obtain ⟨defaultValue,_⟩ := hv
    let repr (v : Nat) := if h : (V v).Nonempty then h.choose else defaultValue
    have repr_mem {v : Nat} (h : (V v).Nonempty) : repr v∈V v := by simpa [repr,h] using h.choose_spec
    let tag (j : Nat) := (repr (a j),repr (b j))
    have lower := graph_count F tag (V w) (by
      intro color glue
      have reach (v : Nat) : v<n+s → ∀ i∈V v,∀ k∈V v,color i=color k := by
        induction v using Nat.strong_induction_on with
        | ind v ih =>
          intro lim i hi k hk
          by_cases early : v<n
          · rw [Finset.card_le_one.mp (raw v early) _ hi _ hk]
          · obtain ⟨j,rfl⟩ : ∃ j,v=n+j := ⟨v-n,by omega⟩
            have js : j<s := by omega
            obtain ⟨la,lb⟩ := back j js
            have left := ih (a j) la (by omega)
            have right := ih (b j) lb (by omega)
            have across (i : Fin n) (ia : i∈V (a j)) (k : Fin n) (kb : k∈V (b j)) : color i=color k := by
              by_cases overlap : common j
              · obtain ⟨z,hz⟩ := overlap
                obtain ⟨za,zb⟩ := mem_inter.mp hz
                exact (left i ia z za).trans (right z zb k kb)
              · have joint := glue j (mem_filter.mpr ⟨mem_range.mpr js,overlap⟩)
                exact (left i ia _ (repr_mem ⟨i,ia⟩)).trans (joint.trans (right _ (repr_mem ⟨k,kb⟩) k kb))
            rcases mem_union.mp (cont j js hi) with ia|ib <;> rcases mem_union.mp (cont j js hk) with ka|kb
            · exact left _ ia _ ka
            · exact across _ ia _ kb
            · exact (across _ ka _ ib).symm
            · exact right _ ib _ kb
      exact reach w valid)
    change (V w).card+((range s).filter common).card≤s+1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hv,card_empty,zero_add]
    change ((range s).filter common).card≤s+1
    omega

end PEqualNP.Outside.L_meta_8869.Overlap

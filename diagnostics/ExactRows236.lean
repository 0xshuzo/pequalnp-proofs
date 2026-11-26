import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8998Flats
open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection
abbrev Pt := Fin 13
abbrev S (l : Pt) : Finset Pt := {l,l+1,l+3,l+9}
abbrev pencil (p : Pt) : Finset Pt := Finset.univ.filter fun l => p ∈ S l
abbrev Sub := Finset Pt

def polar (T : Pt → Sub) (X : Sub) : Sub := Finset.univ.filter fun j => Disjoint (T j) X
@[simp] theorem polar_mem {T : Pt → Sub} {X : Sub} {j : Pt} : j ∈ polar T X ↔ Disjoint (T j) X := by simp [polar]

theorem extend_left (T : Pt → Sub) (hk : ∀ k : Pt, ∀ q ∈ T k, ∀ p : Pt,
    p ∉ T k ∨ p = q → ∃ m : Pt, p ∈ T m ∧ ∀ r ∈ T k, r ∈ T m → r = q)
    (common : ∀ k m : Pt, ∃ p, p ∈ T k ∧ p ∈ T m)
    {X Y : Sub} (hf : IsFalseInput T X Y) (k : Pt) (hX : X ⊆ T k) :
    ∃ X' Y' : Sub, X ⊆ X' ∧ Y ⊆ Y' ∧ IsMaximalFalse T X' Y' ∧ ¬IsGeneric T 0 X' Y' := by
  classical
  have lef : Y ⊆ polar T X := fun j hj => polar_mem.mpr (hf j hj)
  by_cases he : X = T k
  · have emp : Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      obtain ⟨p,hk,hm⟩ := common k l
      exact Finset.disjoint_left.mp (hf l hl) hm (he ▸ hk)
    refine ⟨Finset.univ, ∅, Finset.subset_univ _, emp ▸ le_rfl, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro l hl; simp at hl
    · intro p hp; simp at hp
    · intro l hl bad
      obtain ⟨p, _, hm⟩ := common l l
      exact Finset.disjoint_left.mp (bad l (Finset.mem_insert_self ..)) hm (Finset.mem_univ _)
    · intro gen
      exact gen.2.2.2 0 (fun l hl => by simp at hl)
  · obtain ⟨q,hq,hout⟩ : ∃q∈T k,q∉X := by
      by_contra! h
      exact he (Finset.Subset.antisymm hX h)
    refine ⟨X,polar T X, le_rfl, lef, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro l hl; exact polar_mem.mp hl
    · intro p hp bad
      have pick : ∃ q ∈ T k, q ∉ X ∧ (p ∉ T k ∨ p=q) := by
        by_cases h : p ∈ T k
        · exact ⟨p,h,hp,Or.inr rfl⟩
        · exact ⟨q,hq,hout,Or.inl h⟩
      obtain ⟨t,ht,hout',hc⟩ := pick
      obtain ⟨m,hm,only⟩ := hk k t ht p hc
      have hmiss : m ∈ polar T X := polar_mem.mpr (Finset.disjoint_left.mpr fun r hr hx =>
        hout' ((only r (hX hx) hr) ▸ hx))
      exact Finset.disjoint_left.mp (bad m hmiss) hm (Finset.mem_insert_self ..)
    · intro l hl bad
      exact hl (polar_mem.mpr (bad l (Finset.mem_insert_self ..)))
    · intro gen; exact gen.2.2.1 k hX

theorem plane_sep : ∀ k : Pt, ∀ q ∈ S k, ∀ p : Pt,
    p ∉ S k ∨ p = q → ∃ m : Pt, p ∈ S m ∧ ∀ r ∈ S k, r ∈ S m → r = q := by decide +kernel
theorem pencil_sep : ∀ k : Pt, ∀ q ∈ pencil k, ∀ p : Pt,
    p ∉ pencil k ∨ p = q → ∃ m : Pt, p ∈ pencil m ∧ ∀ r ∈ pencil k, r ∈ pencil m → r = q := by decide +kernel
theorem common_plane : ∀ k m : Pt, ∃ p, p ∈ S k ∧ p ∈ S m := by decide +kernel
theorem common_pencil : ∀ k m : Pt, ∃ p, p ∈ pencil k ∧ p ∈ pencil m := by decide +kernel

theorem dual_false {X Y : Sub} : IsFalseInput S X Y ↔ IsFalseInput pencil Y X := by
  simp only [IsFalseInput, Finset.disjoint_left, pencil, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h p hp l hi hl; exact h l hl hi hp
  · intro h l hl p hi hp; exact h p hp hi hl

theorem dual_max {X Y : Sub} : IsMaximalFalse S X Y ↔ IsMaximalFalse pencil Y X := by
  constructor
  · rintro ⟨f,a,b⟩; exact ⟨dual_false.mp f,fun l h g => b l h (dual_false.mpr g),fun p h g => a p h (dual_false.mpr g)⟩
  · rintro ⟨f,a,b⟩; exact ⟨dual_false.mpr f,fun p h g => b p h (dual_false.mp g),fun l h g => a l h (dual_false.mp g)⟩

theorem dual_generic {X Y : Sub} : IsGeneric S 0 X Y ↔ IsGeneric pencil 0 Y X := by
  simp only [IsGeneric, InNoLine, InNoPencil, Nat.zero_le, true_and, pencil,
    Finset.subset_iff, Finset.mem_filter, Finset.mem_univ]
  aesop

theorem extend_degenerate {X Y : Sub} (hf : IsFalseInput S X Y)
    (h : (∃ k, X ⊆ S k) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l) :
    ∃ X' Y' : Sub, X ⊆ X' ∧ Y ⊆ Y' ∧ IsMaximalFalse S X' Y' ∧ ¬IsGeneric S 0 X' Y' := by
  rcases h with ⟨k, hk⟩ | ⟨p, hp⟩
  · exact extend_left S plane_sep common_plane hf k hk
  · have sub : Y ⊆ pencil p := fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp l hl⟩
    obtain ⟨Y',X',sy,sx,hm,hn⟩ := extend_left pencil pencil_sep common_pencil (dual_false.mp hf) p sub
    exact ⟨X',Y',sx,sy,dual_max.mpr hm,fun g => hn (dual_generic.mp g)⟩

abbrev Rows := Finset (Sub × Sub)

def leftSeeds : Finset Sub := Finset.univ.biUnion fun k : Pt => (S k).powerset.erase (S k)
def rightSeeds : Finset Sub := Finset.univ.biUnion fun p : Pt => (pencil p).powerset.erase (pencil p)
def negRows : Rows := (leftSeeds.image fun X => (X,polar S X)) ∪
  (rightSeeds.image fun Y => (polar pencil Y,Y))

theorem max_columns {T : Pt → Sub} {X Y : Sub} (h : IsMaximalFalse T X Y) : Y = polar T X := by
  apply Finset.Subset.antisymm
  · exact fun l hl => polar_mem.mpr (h.1 l hl)
  · intro l hl
    by_contra miss
    apply h.2.2 l miss
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl|old
    · exact polar_mem.mp hl
    · exact h.1 m old

theorem proper {T : Pt → Sub} {X Y : Sub} (meet : ∀ k m : Pt, ∃ p, p ∈ T k ∧ p ∈ T m)
    (small : ∀ k, T k ≠ Finset.univ) (maximal : IsMaximalFalse T X Y) (k : Pt) : X ≠ T k := by
  rintro rfl
  have empty : Y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    obtain ⟨p,hp,hlp⟩ := meet k l
    exact Finset.disjoint_left.mp (maximal.1 l hl) hlp hp
  subst Y
  apply small k
  apply Finset.eq_univ_of_forall
  intro p
  by_contra hp
  exact maximal.2.1 p hp (by intro l hl; simp at hl)

theorem max_in_table {X Y : Sub} (h : IsMaximalFalse S X Y) (n : ¬ IsGeneric S 0 X Y) :
    (X,Y) ∈ negRows := by
  have split : (∃ k, X ⊆ S k) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l := by
    by_contra miss
    exact n ⟨Nat.zero_le _,Nat.zero_le _,fun l s => miss (Or.inl ⟨l,s⟩),fun p s => miss (Or.inr ⟨p,s⟩)⟩
  rcases split with ⟨k,hk⟩ | ⟨p,hp⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨X, Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,?_⟩, ?_⟩
    · exact Finset.mem_erase.mpr ⟨proper common_plane (by decide +kernel) h k, Finset.mem_powerset.mpr hk⟩
    · rw [←max_columns h]
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨Y, Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,?_⟩, ?_⟩
    · exact Finset.mem_erase.mpr ⟨proper common_pencil (by decide +kernel) (dual_max.mp h) p,
        Finset.mem_powerset.mpr (fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp l hl⟩)⟩
    · rw [←max_columns (dual_max.mp h)]

theorem table_sufficient {C : Circuit}
    (hc : ∀ r ∈ negRows, C.eval (incidenceInput r.1 r.2) = false)
    {X Y : Sub} (m : IsMaximalFalse S X Y) (d : ¬IsGeneric S 0 X Y) :
    C.eval (incidenceInput X Y) = false := hc _ (max_in_table m d)


theorem proper_max (T : Pt → Sub) (hk : ∀ k : Pt, ∀ q ∈ T k, ∀ p : Pt,
    p ∉ T k ∨ p = q → ∃ m : Pt, p ∈ T m ∧ ∀ r ∈ T k, r ∈ T m → r = q)
    {X : Sub} (k : Pt) (hX : X ⊆ T k) (he : X ≠ T k) :
    IsMaximalFalse T X (polar T X) ∧ ¬IsGeneric T 0 X (polar T X) := by
  classical
  obtain ⟨q,hq,hout⟩ : ∃q∈T k,q∉X := by
    by_contra! h
    exact he (Finset.Subset.antisymm hX h)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l hl; exact polar_mem.mp hl
  · intro p hp bad
    have pick : ∃ q ∈ T k, q ∉ X ∧ (p ∉ T k ∨ p=q) := by
      by_cases h : p ∈ T k
      · exact ⟨p,h,hp,Or.inr rfl⟩
      · exact ⟨q,hq,hout,Or.inl h⟩
    obtain ⟨t,ht,hout',hc⟩ := pick
    obtain ⟨m,hm,only⟩ := hk k t ht p hc
    have hmiss : m ∈ polar T X := polar_mem.mpr (Finset.disjoint_left.mpr fun r hr hx =>
      hout' ((only r (hX hx) hr) ▸ hx))
    exact Finset.disjoint_left.mp (bad m hmiss) hm (Finset.mem_insert_self ..)
  · intro l hl bad
    exact hl (polar_mem.mpr (bad l (Finset.mem_insert_self ..)))
  · intro gen; exact gen.2.2.1 k hX

theorem table_exact {X Y : Sub} : (X,Y) ∈ negRows ↔ IsMaximalFalse S X Y ∧ ¬IsGeneric S 0 X Y := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with a|b
    · obtain ⟨P,m,e⟩ := Finset.mem_image.mp a
      obtain ⟨k,_,c⟩ := Finset.mem_biUnion.mp m
      obtain ⟨ne,sub⟩ := Finset.mem_erase.mp c
      cases e
      exact proper_max S plane_sep k (Finset.mem_powerset.mp sub) ne
    · obtain ⟨L,m,e⟩ := Finset.mem_image.mp b
      obtain ⟨k,_,c⟩ := Finset.mem_biUnion.mp m
      obtain ⟨ne,sub⟩ := Finset.mem_erase.mp c
      cases e
      obtain ⟨hm,hn⟩ := proper_max pencil pencil_sep k (Finset.mem_powerset.mp sub) ne
      exact ⟨dual_max.mpr hm,fun g => hn (dual_generic.mp g)⟩
  · rintro ⟨hm,hn⟩; exact max_in_table hm hn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem row_count : negRows.card = 236 := by decide +kernel
end PEqualNP.Outside.L_meta_8998Flats

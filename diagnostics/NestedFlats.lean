import PEqualNP.Outside.L_meta_18294
import PEqualNP.Outside.L_meta_7165
import PEqualNP.Outside.L_meta_9089

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

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.HeptadCover
open PEqualNP.Outside.L_meta_18294.Main

abbrev good (C : Circuit) := Monotone2 C ∧ RightOnIncidentPairs S C ∧
  ∀ X Y, IsMaximalFalse S X Y → ¬IsGeneric S 0 X Y → C.eval (incidenceInput X Y) = false

theorem starReject {C : Circuit} (g : good C) {X Y : Sub} (hf : IsFalseInput S X Y)
    (hs : (∃ l, X ⊆ S l) ∨ ∃ p, ∀ l ∈ Y, p ∈ S l) : C.eval (incidenceInput X Y) = false := by
  obtain ⟨X',Y',sx,sy,hm,hn⟩ := extend_degenerate hf hs
  by_contra h
  have on := PEqualNP.Outside.L_meta_9089_aux.eval_mono C g.1 X X' Y Y' sx sy (Bool.eq_true_of_not_eq_false h)
  rw [g.2.2 _ _ hm hn] at on
  cases on

theorem singer : singerLines3 = S := by
  funext l
  have tab : ∀ l p : Pt, p ∈ singerLines3 l ↔ p ∈ S l := by decide +kernel
  exact Finset.ext (tab l)

theorem fits_iff {C : Circuit} (hm : Monotone2 C) : fits C ↔ good C := by
  rw [← goodIff C hm]
  simp only [negativeStar, singer]
  constructor
  · rintro ⟨hp,hn⟩
    refine ⟨hm,hp,?_⟩
    intro X Y hm' ng
    apply hn X Y ⟨hm'.1,?_⟩
    by_contra miss
    exact ng ⟨Nat.zero_le _,Nat.zero_le _,fun l sub => miss (Or.inl ⟨l,sub⟩),fun p sub => miss (Or.inr ⟨p,sub⟩)⟩
  · intro g
    exact ⟨g.2.1,fun X Y h => starReject g h.1 h.2⟩

theorem nested_countermodel {C : Circuit} (h : good C) (hs : C.size ≤ 63) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 26 D ∧ good D ∧ D.size ≤ C.size ∧
      2 ≤ PEqualNP.TopForm.andPairs 26 D ∧ ∀ i j, nested D i j →
        ∃ X Y, IsMaximalFalse S X Y ∧ ¬IsGeneric S 0 X Y ∧
          (D.wires (incidenceInput X Y)).getD (26+i) false = true := by
  obtain ⟨T,tm,tb,ts,te⟩ := PEqualNP.Outside.L_meta_7165 26 C h.1
  have tf : fits T := by
    intro X Y hstar
    rw [te (row X Y)]
    exact ((fits_iff h.1).mpr h) X Y hstar
  obtain ⟨D,da,df,ds,count,dirty⟩ := minimalHard tm tb tf (le_trans ts hs)
  have dm : Monotone2 D := fun g hg => ⟨by simpa using da.1 g hg, (da.2.2 g hg).le⟩
  refine ⟨D,da,(fits_iff dm).mp df,le_trans ds ts,count,?_⟩
  intro i j hn
  obtain ⟨_,⟨X,Y,hstar,off,rfl⟩,on⟩ := dirty i j hn
  have hneg := (negativeStar_iff X Y).mpr ⟨hstar,off⟩
  simp only [negativeStar,singer] at hneg
  obtain ⟨X',Y',sx,sy,mx,ng⟩ := extend_degenerate hneg.1 hneg.2
  have mono := PEqualNP.Outside.L_meta_9089_aux.eval_mono (⟨D.gates,26+i⟩ : Circuit) dm X X' Y Y' sx sy
  refine ⟨X',Y',mx,ng,mono ?_⟩
  rwa [incidenceInput_eq]
end PEqualNP.Outside.L_meta_8998Flats

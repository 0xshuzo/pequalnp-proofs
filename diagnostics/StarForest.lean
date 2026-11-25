import Mathlib
import PEqualNP.Defs

namespace ForkShare3018

open PEqualNP.TopForm

theorem starForest {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (col : Fin n → Bool) (colour : ∀ u v, G.Adj u v → col u ≠ col v)
    (square : NoFourCycle G) (s : Fin n) (sub : H ≤ G)
    (off : ∀ v, ¬H.Adj s v)
    (touch : ∀ u v, H.Adj u v → G.Adj s u ∨ G.Adj s v) :
    ∃ C D : Finset (Fin n), Disjoint C D ∧
      C ∪ D = Finset.univ.filter (fun v => ∃ u, H.Adj u v) ∧
      (∀ c ∈ C, ∃ v ∈ D, H.Adj c v) ∧
      (∀ v ∈ D, ∃! c, c ∈ C ∧ H.Adj c v) ∧
      (∀ u v, H.Adj u v → (u∈C ∧ v∈D) ∨ (v∈C ∧ u∈D)) ∧
      ((C ×ˢ D).filter (fun e => H.Adj e.1 e.2)).card + C.card =
        (Finset.univ.filter (fun v => ∃ u, H.Adj u v)).card := by
  classical
  let V := Finset.univ.filter (fun v => ∃ u, H.Adj u v)
  let C := V.filter (G.Adj s)
  let D := V \ C
  have disj : Disjoint C D := by
    exact Finset.disjoint_left.mpr fun p hp hd => (Finset.mem_sdiff.mp hd).2 hp
  have unionEq : C ∪ D = V := Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
  have hot {u v : Fin n} (h : H.Adj u v) : u ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,h.symm⟩
  have triangle {u v : Fin n} (h : H.Adj u v) :
      ¬ (G.Adj s u ∧ G.Adj s v) := by
    intro ⟨hu,hv⟩
    have a := colour s u hu
    have b := colour s v hv
    have c := colour u v (sub h)
    cases hs : col s <;> cases hx : col u <;> cases hy : col v <;> simp_all
  have orient {u v : Fin n} (h : H.Adj u v) : (u∈C ∧ v∈D) ∨ (v∈C ∧ u∈D) := by
    rcases touch _ _ h with hu | hv
    · left
      exact ⟨Finset.mem_filter.mpr ⟨hot h,hu⟩, Finset.mem_sdiff.mpr
        ⟨hot h.symm,fun cv => triangle h ⟨hu,(Finset.mem_filter.mp cv).2⟩⟩⟩
    · right
      exact ⟨Finset.mem_filter.mpr ⟨hot h.symm,hv⟩, Finset.mem_sdiff.mpr
        ⟨hot h,fun cu => triangle h ⟨(Finset.mem_filter.mp cu).2,hv⟩⟩⟩
  have partC (c) (hc : c∈C) : ∃ v∈D,H.Adj c v := by
    obtain ⟨v,edge⟩ := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    rcases orient edge.symm with h | h
    · exact ⟨v,h.2,edge.symm⟩
    · exact False.elim (Finset.disjoint_left.mp disj hc h.2)
  have partD (v) (hv : v∈D) : ∃! c, c∈C ∧ H.Adj c v := by
    obtain ⟨c,e⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
    have hc : c∈C := by
      rcases orient e with h | h
      · exact h.1
      · exact False.elim (Finset.disjoint_left.mp disj h.1 hv)
    refine ⟨c,⟨hc,e⟩,?_⟩
    intro a ha
    have sv : s ≠ v := by
      rintro rfl
      exact off c e.symm
    have bound := Finset.card_le_one.mp (square s v sv)
    apply bound a _ c _
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha.1).2,(sub ha.2).symm⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2,(sub e).symm⟩
  let E := (C ×ˢ D).filter (fun e => H.Adj e.1 e.2)
  have mapD : E.image Prod.snd = D := by
    ext v
    constructor
    · rintro hv
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).2
    · intro hv
      obtain ⟨c,⟨hc,edge⟩,_⟩ := partD v hv
      exact Finset.mem_image.mpr ⟨(c,v),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hv⟩,edge⟩,rfl⟩
  have inj : Set.InjOn Prod.snd (E : Set (Fin n × Fin n)) := by
    rintro ⟨a,v⟩ ha ⟨b,w⟩ hb eq
    change v=w at eq
    subst w
    obtain ⟨ha',ea⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb',eb⟩ := Finset.mem_filter.mp hb
    obtain ⟨c,_,uniq⟩ := partD v (Finset.mem_product.mp ha').2
    have e : a=b := (uniq a ⟨(Finset.mem_product.mp ha').1,ea⟩).trans
      (uniq b ⟨(Finset.mem_product.mp hb').1,eb⟩).symm
    simp [e]
  have eh := Finset.card_image_of_injOn inj
  rw [mapD] at eh
  refine ⟨C,D,disj,unionEq,partC,partD,fun _ _ => orient,?_⟩
  change E.card+C.card=V.card
  rw [←unionEq, Finset.card_union_of_disjoint disj, ←eh, Nat.add_comm]

end ForkShare3018

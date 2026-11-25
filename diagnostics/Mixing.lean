import Mathlib
import PEqualNP.Outside.L_meta_1766
import PEqualNP.Outside.L_meta_2695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

namespace PunctureBoundary

private lemma first_loss {α : Type*} {r : α → α → Prop} (P : α → Prop) {a b : α}
    (path : Relation.ReflTransGen r a b) (start : P a) :
    ¬ P b → ∃ u v,Relation.ReflTransGen r a u ∧ r u v ∧ P u ∧ ¬P v := by
  induction path with
  | refl => exact fun h => False.elim (h start)
  | @tail b c pre edge ih =>
    intro hc
    by_cases hb : P b
    · exact ⟨b,c,pre,edge,hb,hc⟩
    · exact ih hb

theorem locate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (w g : ℕ) (j : g∈junk G C) (reach : OrReaches n C w g)
    (nonempty : (orIn n C w).Nonempty) :
    ∃ m∈orN G C \ lam G C, (orIn n C (n+m)).Nonempty ∧ orIn n C (n+m) ⊆ orIn n C w := by
  classical
  have hand : (gateAt C g).op=GateOp.and := (Finset.mem_filter.mp j).2.1
  have nil := PEqualNP.Outside.L_meta_2695.orIn_and (n:=n) (C:=C) hand
  have bad : ¬ (orIn n C (n+g)).Nonempty := by rw [nil];simp
  obtain ⟨a,b,path,st,raw,empty⟩ := first_loss (fun w => (orIn n C w).Nonempty)
    (PEqualNP.Outside.L_meta_1766.orReaches_reach g w reach).1 nonempty bad
  obtain ⟨m,hm,ea,hop,ib,_⟩ := st
  subst a
  obtain ⟨u,hu⟩ := raw
  have subset : orIn n C (n+m) ⊆ orIn n C w := fun t ht =>
    PEqualNP.Outside.L_meta_1766.reach_mem_orIn t (path.trans (PEqualNP.Outside.L_meta_1766.mem_orIn_reach t ht))
  have safe : m∈orN G C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hm,hop,?_⟩
    intro below
    have pos : gateVal n C m (pairInput u u)=true :=
      PEqualNP.Outside.L_meta_1766.reach_var_val (pairInput u u) (n+m) u (PEqualNP.Outside.L_meta_1766.mem_orIn_reach u hu) (PEqualNP.Outside.L_meta_1766.pairInput_left u u)
    exact ((PEqualNP.Outside.L_meta_1766.graphFun_pair G u u).mp (below _ pos)).ne rfl
  refine ⟨m, Finset.mem_sdiff.mpr ⟨safe,?_⟩,⟨u,hu⟩,subset⟩
  intro lamMem
  obtain ⟨_,l,r,_⟩ := Finset.mem_filter.mp lamMem
  obtain ⟨x,y,hxy⟩ := List.length_eq_two.mp (ao.2.2 _ (PEqualNP.Outside.L_meta_1766.gateAt_mem hm))
  rw [hxy] at ib
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ib
  rcases ib with eq|eq
  · subst b
    apply empty
    simpa [opnd,hxy] using l
  · subst b
    apply empty
    simpa [opnd,hxy] using r

end PunctureBoundary

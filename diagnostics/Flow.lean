import Mathlib
import PEqualNP.Outside.L_meta_971

namespace Flow9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_971_aux

abbrev V := Fin 26

def priced (G : V → V → Prop) : Prop :=
  ∀ I : Finset V, (∀ i∈I, ∀ j∈I, ¬ G i j) →
  ∃ T U : Finset V, U.card+2*T.card≤8 ∧ (∀ i∈I, i∈U ∨ ∃ a∈T, G i a)

theorem flow {G : V → V → Prop} (hG : sem_Gr G) (cover : priced G)
    {D : Dag} (live : StrictLive 26 D) (correct : sem_Comp 26 G D) : 43≤D.length := by
  classical
  let I := ineligSet 26 D
  let H := eligSet 26 D
  have indep : ∀ i∈I,∀ j∈I,¬G i j := by
    intro i hi j hj edge
    have a : i∉H := (Finset.mem_sdiff.mp hi).2
    have b : j∉H := (Finset.mem_sdiff.mp hj).2
    exact (sem_elig_cover hG live correct edge).elim a b
  obtain ⟨T,U,small,cov⟩ := cover I indep
  obtain ⟨pos,ports⟩ := k4_assigned hG live correct
  have sub (i : V) (hi : i∈I\U) : i∈ineligSet 26 D ∧ ∃ a∈T,G i a := by
    obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hi
    exact ⟨hx,(cov i hx).resolve_left hy⟩
  obtain ⟨hit,card⟩ := k4_exits_ge ports T (I\U) sub
  have bound := Finset.card_le_card hit
  rw [card] at bound
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hG live.1 correct
  have expense := k4_budget hG live correct b hb T
  change _ + _ + H.card ≤ _ at expense
  have hsplit : I ⊆ (I\U)∪U := by
    intro i hi
    by_cases h : i∈U
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,h⟩)
  have nI := (Finset.card_le_card hsplit).trans (Finset.card_union_le (I\U) U)
  have total : I.card+H.card=26 := by
    have t := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)
    simpa [I,ineligSet,H] using t
  have surplus := surplus_identity live
  have positive := Bplus_le_total 26 D
  omega

theorem lengthOfCover {G : V → V → Prop} (hG : sem_Gr G) (cover : priced G)
    (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
      C.eval (List.ofFn x)=true ↔ sem_Edge G x) : 43≤C.size := by
  classical
  have single (i : V) : ¬ sem_Edge G (fun k => decide (k=i)) := by
    rintro ⟨u,v,edge,hu,hv⟩
    have eu : u=i := of_decide_eq_true hu
    have ev : v=i := of_decide_eq_true hv
    subst u
    subst v
    exact hG.2.1 i edge
  have extra (i : V) : ∃ j, G i j ∧ j≠i := hG.2.2.2 i i
  have hit {i j : V} (edge : G i j) :
      sem_Edge G (fun v => decide (v=i ∨ v=j)) := ⟨i,j,edge,by simp,by simp⟩
  obtain ⟨D,ld,lim,simulation⟩ := normalize_strictLive (n:=26) C hm
    (by
      intro b
      cases b
      · obtain ⟨v,edge,-⟩ := extra 0
        exact ⟨_,by rw [Ne,Bool.not_eq_false]; exact (correct _).mpr (hit edge)⟩
      · exact ⟨fun _ => false,fun e => by
          obtain ⟨u,v,_,h,_⟩ := (correct _).mp e
          contradiction⟩)
    (by
      intro i
      refine ⟨fun k => decide (k=i),fun h => single i ((correct _).mp ?_)⟩
      rw [h]
      simp)
    (by
      intro i
      obtain ⟨j,edge,diff⟩ := extra i
      refine ⟨fun k => decide (k=j),fun k => decide (k=i ∨ k=j),?_,?_⟩
      · intro k hk
        simp [hk]
      · intro same
        apply single j
        exact (correct _).mp (same.trans ((correct _).mpr (hit edge))))
  exact (flow hG cover ld (fun x => by rw [simulation x]; exact correct x)).trans lim

end Flow9742

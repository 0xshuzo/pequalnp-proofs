import Mathlib
import PEqualNP.Outside.L_meta_971
namespace Boost9742
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_971_aux
abbrev V := Fin 26

def cheap (G : V → V → Prop) (I : Finset V) : Prop :=
  ∃ T U : Finset V,U.card+2*T.card≤7 ∧ ∀ i∈I,i∈U ∨ ∃a∈T,G i a

def pencil (G : V → V → Prop) (I : Finset V) (i : V) : Prop :=
  ∃ T : Finset V,T.card≤4 ∧ (∀ v∈I,∃a∈T,G v a) ∧
    ∃ a∈T,∃ b∈T,a≠b ∧ G i a ∧ G i b

def triple (G : V → V → Prop) (I : Finset V) : Prop :=
  ∃ u a b c : V,a∈I ∧ b∈I ∧ a≠b ∧ a≠c ∧ b≠c ∧ G u a ∧ G u b ∧ G u c

def casesFor (G : V → V → Prop) (I : Finset V) : Prop :=
  cheap G I ∨ (∃ i∈I,pencil G I i) ∨ (I.card≤8 ∧ triple G I)

theorem core {G : V → V → Prop} (hG : sem_Gr G) {D : Dag}
    (live : StrictLive 26 D) (correct : sem_Comp 26 G D)
    (geo : casesFor G (ineligSet 26 D)) : 44≤D.length := by
  classical
  let I := ineligSet 26 D
  let H := eligSet 26 D
  have total : I.card+H.card=26 := by
    simpa [I,ineligSet,H] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)
  obtain ⟨pos,ports⟩ := k4_assigned hG live correct
  obtain ⟨branch,branchOk⟩ := sem_exists_pureBranch hG live.1 correct
  let exp := k4_budget hG live correct branch branchOk
  have ncost := surplus_identity live
  have plus := Bplus_le_total 26 D
  rcases geo with ⟨T,U,pr,cov⟩|⟨i,hi,T,pr,cov,a,ha,b,hb,ne,ga,gb⟩|⟨sm,u,a,b,c,ha,hb,ab,ac,bc,ua,ub,uc⟩
  · have sub (i : V) (hi : i∈I\U) : i∈ineligSet 26 D ∧ ∃ a∈T,G i a := by
      obtain ⟨hx,hy⟩ := Finset.mem_sdiff.mp hi
      exact ⟨hx,(cov i hx).resolve_left hy⟩
    obtain ⟨hit,card⟩ := k4_exits_ge ports T (I\U) sub
    have bound := Finset.card_le_card hit
    rw [card] at bound
    have hsplit : I ⊆ (I\U)∪U := by
      intro k hk
      by_cases h : k∈U
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hk,h⟩)
    have nI := (Finset.card_le_card hsplit).trans (Finset.card_union_le (I\U) U)
    have expense := exp T
    change _+_+H.card≤_ at expense
    omega
  · obtain ⟨hit,card⟩ := k4_exits_ge ports T I (fun v hv => ⟨hv,cov v hv⟩)
    have bound := Finset.card_le_card hit
    rw [card] at bound
    let w := src D (pos i)
    have got := (ports.1 i hi).2.2.1
    have am : a∈supp 26 D w ∩ T := Finset.mem_inter.mpr ⟨got a ga,ha⟩
    have bm : b∈supp 26 D w ∩ T := Finset.mem_inter.mpr ⟨got b gb,hb⟩
    have two : 2≤(supp 26 D w ∩ T).card := Finset.one_lt_card.mpr ⟨a,am,b,bm,ne⟩
    obtain ⟨j,hj,-⟩ := k4_mask_gate live.1 T w two
    have one := Finset.card_pos.mpr ⟨j,hj⟩
    have expense := exp T
    change _+_+H.card≤_ at expense
    omega
  · have thr := k4_three_cons hG live correct ports ha hb ab ac bc ua ub uc
    have expense := exp {u}
    rw [Finset.card_singleton] at expense
    change _+_+H.card≤_ at expense
    change I.card≤8 at sm
    omega

theorem small {G : V → V → Prop} {I : Finset V} (h : I.card≤7) : cheap G I := by
  exact ⟨∅,I,by simpa using h,fun i hi => Or.inl hi⟩

end Boost9742

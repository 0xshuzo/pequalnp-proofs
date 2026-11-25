import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_1491
import PEqualNP.Outside.L_meta_1766
import PEqualNP.Outside.L_meta_2695
import PEqualNP.Outside.L_meta_3760


namespace Puncture4043
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def oriented (a b : Fin 25) : Prop :=
  a.val<12 ∧ 12≤b.val ∧ (a.val+26-b.val)%13∈[0,1,3,9]
instance (a b : Fin 25) : Decidable (oriented a b) := by unfold oriented;infer_instance

def G0 : SimpleGraph (Fin 25) where
  Adj a b := oriented a b ∨ oriented b a
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide +kernel⟩

instance decG : DecidableRel G0.Adj := fun a b => inferInstanceAs (Decidable (oriented a b ∨ oriented b a))

theorem form : ∀ a b : Fin 25,G0.Adj a b ↔
    (a.val<12 ∧ 12≤b.val ∧ (a.val+26-b.val)%13∈[0,1,3,9]) ∨
    (b.val<12 ∧ 12≤a.val ∧ (b.val+26-a.val)%13∈[0,1,3,9]) := fun _ _ => Iff.rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem count_edges : G0.edgeFinset.card=48 := by decide +kernel


-- Residual incidence accounting from the L-meta-2583 computation, using the four published circuit bounds.
theorem residual_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (r : ℕ) (deg : ∀ v, G.degree v ≤ r)
    (D : Finset (Sym2 (Fin n))) (T : Finset (Fin n))
    (cover : (G.deleteEdges (D : Set _)).IsVertexCover (T : Set _)) :
    G.edgeFinset.card ≤ D.card + T.card * r := by
  classical
  let E (v : Fin n) := (G.neighborFinset v).image (fun w => s(v,w))
  have hsub : G.edgeFinset ⊆ D ∪ T.biUnion E := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he
      by_cases hd : s(a,b) ∈ D
      · exact Finset.mem_union_left _ hd
      apply Finset.mem_union_right
      have ab : G.Adj a b := G.mem_edgeFinset.mp he
      have kept : (G.deleteEdges (D : Set _)).Adj a b :=
        SimpleGraph.deleteEdges_adj.mpr ⟨ab,hd⟩
      rcases cover kept with ha | hb
      · exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image_of_mem _
          ((G.mem_neighborFinset _ _).mpr ab)⟩
      · have w : s(b,a) ∈ E b := Finset.mem_image_of_mem _ ((G.mem_neighborFinset _ _).mpr ab.symm)
        exact Finset.mem_biUnion.mpr ⟨b,hb,Sym2.eq_swap ▸ w⟩
  have hv (v : Fin n) : (E v).card ≤ r :=
    Finset.card_image_le.trans ((G.card_neighborFinset_eq_degree v).le.trans (deg v))
  calc
    G.edgeFinset.card ≤ (D ∪ T.biUnion E).card := Finset.card_le_card hsub
    _ ≤ D.card + (T.biUnion E).card := Finset.card_union_le _ _
    _ ≤ D.card + ∑ v ∈ T, (E v).card := Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ D.card + ∑ _v ∈ T, r := Nat.add_le_add_left (Finset.sum_le_sum (fun v _ => hv v)) _
    _ = D.card + T.card*r := by simp

theorem minimum_cover {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ T, IsMinCover G T := by
  classical
  let P (k : ℕ) := ∃ T : Finset (Fin n), G.IsVertexCover (T : Set _) ∧ T.card = k
  have someK : ∃ k, P k :=
    ⟨_,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_univ _),rfl⟩
  obtain ⟨T,hT,ht⟩ := Nat.find_spec someK
  refine ⟨T,hT,?_⟩
  intro S hS
  rw [ht]
  exact Nat.find_min' someK ⟨S,hS,rfl⟩

def reserve {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : ℕ :=
  2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card

theorem reserve_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (bi : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C)
    (nonempty : (Ustar G C).Nonempty) : 3 ≤ reserve G C := by
  obtain ⟨e,he⟩ := nonempty
  obtain ⟨a,ha,b,g,hg,hr⟩ :
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ g ∈ junk G C, OrReaches n C (opnd C a b) g := by
    rcases PEqualNP.Outside.L_meta_1766 n G C hL hT e he with
      ⟨u,v,_,a,ha,b,g,hg,_,hr,_⟩ | ⟨u,v,_,a,ha,g,hg,k,_,_,hr,_,_,_⟩
    · exact ⟨a,ha,1-b,g,hg,hr⟩
    · exact ⟨a,ha,0,g,hg,hr⟩
  have pos := Finset.card_pos.mpr (show (junk G C).Nonempty from ⟨g,hg⟩)
  have ne := PEqualNP.Outside.L_meta_3760 n G C s bi h4 hL
  rcases PEqualNP.Outside.L_meta_2695 n G C hL.1.2.2 a ha b g hg hr with hc | ho
  · have := Finset.card_pos.mpr (show (centreless G C).Nonempty from ⟨a,hc⟩)
    unfold reserve
    omega
  · have := Finset.card_pos.mpr ho
    unfold reserve
    omega

def point (p : Fin 12) : Fin 25 := Fin.ofNat 25 p.val
def line (d : Fin 13) (p : Fin 12) : Fin 25 := Fin.ofNat 25 (12+(p.val+14-d.val)%13)

set_option maxHeartbeats 4000000 in
theorem four : NoFourCycle G0 := by
  change ∀ a b : Fin 25,a≠b → (Finset.univ.filter (fun w => G0.Adj a w ∧ G0.Adj b w)).card≤1
  decide +kernel

theorem color : ∀ a b : Fin 25,G0.Adj a b → decide (a.val<12) ≠ decide (b.val<12) := by decide +kernel

theorem degrees : ∀ v : Fin 25, G0.degree v≤4 := by
  intro v
  rw [← G0.card_neighborFinset_eq_degree]
  exact (by decide +kernel : ∀ v : Fin 25,(G0.neighborFinset v).card≤4) v

theorem flag : ∀ d : Fin 13,d.val∈[0,1,3,9] → ∀ i : Fin 12,
    G0.Adj (point i) (line d i) ∧ (point i).val<12 ∧ 12≤(line d i).val ∧
      ((point i).val+26-(line d i).val)%13=d.val := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem disjoint_ends : ∀ (d : Fin 13) (i j : Fin 12),i≠j →
    point i≠point j ∧ point i≠line d j ∧ line d i≠point j ∧ line d i≠line d j := by decide +kernel

theorem intact (U : Finset (Sym2 (Fin 25))) (T : Finset (Fin 25))
    (cover : (G0.deleteEdges (U : Set _)).IsVertexCover (T : Set _))
    (d : Fin 13) (hd : d.val∈[0,1,3,9]) (unpaid : ∀ i : Fin 12,s(point i,line d i)∉U) : 12≤T.card := by
  let f (i : Fin 12) := if point i ∈ T then point i else line d i
  have inside (i : Fin 12) : f i∈T := by
    dsimp only [f]
    split <;> rename_i h
    · exact h
    · have e : (G0.deleteEdges (U : Set _)).Adj (point i) (line d i) :=
        SimpleGraph.deleteEdges_adj.mpr ⟨(flag d hd i).1,unpaid i⟩
      exact (cover e).resolve_left h
  have inj : ∀ i∈(Finset.univ : Finset (Fin 12)),∀ j∈(Finset.univ : Finset (Fin 12)), f i=f j → i=j := by
    intro i _ j _ eq
    by_contra ne
    obtain ⟨a,b,c,e⟩ := disjoint_ends d i j ne
    dsimp only [f] at eq
    split at eq <;> split at eq <;> contradiction
  simpa using Finset.card_le_card_of_injOn f (fun i _ => inside i) inj

theorem matchingPrice : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (D : Circuit),
      (∀ u v : Fin 25, G.Adj u v ↔
        (u.val < 12 ∧ 12 ≤ v.val ∧ (u.val+26-v.val)%13 ∈ [0,1,3,9]) ∨
        (v.val < 12 ∧ 12 ≤ u.val ∧ (v.val+26-u.val)%13 ∈ [0,1,3,9])) → IsLeastAO G D → PEqualNP.TopForm.TopForm G D → D.size≤57 →
      4≤(Ustar G D).card ∧ ((Ustar G D).card=4 → (∀ t : ℕ, t ∈ [0,1,3,9] → ∃ p l : Fin 25,
        p.val<12 ∧ 12≤l.val ∧ (p.val+26-l.val)%13=t ∧ s(p,l)∈Ustar G D)) := by
  intro G inst D shape least top short
  have hg : G=G0 := by
    ext a b
    exact (shape a b).trans (form a b).symm
  subst G
  have di : inst=decG := Subsingleton.elim _ _
  subst inst
  classical
  have ne : G0.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [count_edges];decide)
  obtain ⟨T,hT⟩ := minimum_cover (G0.deleteEdges (Ustar G0 D : Set _))
  have capacity := residual_cover G0 4 degrees (Ustar G0 D) T hT.1
  rw [count_edges] at capacity
  obtain ⟨cost,tsize⟩ := PEqualNP.Outside.L_meta_1491 25 G0 D four ne least top
  rw [count_edges] at cost
  have tc := tsize T hT
  have total : 48 + T.card + reserve G0 D ≤ D.size + (Ustar G0 D).card + 1 := by
    unfold reserve
    omega
  have r3 (positive : 0<(Ustar G0 D).card) : 3≤reserve G0 D :=
    reserve_three G0 D (fun u => decide (u.val<12)) color four least top (Finset.card_pos.mp positive)
  constructor
  · by_contra! few
    by_cases emp : (Ustar G0 D).card=0
    · omega
    · have r := r3 (by omega)
      omega
  · intro fe t ht
    have tlt : t<13 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      omega
    let d : Fin 13 := ⟨t,tlt⟩
    have r := r3 (by omega)
    have ex : ∃ i : Fin 12,s(point i,line d i)∈Ustar G0 D := by
      by_contra! absent
      have full := intact (Ustar G0 D) T hT.1 d ht absent
      omega
    obtain ⟨i,hi⟩ := ex
    exact ⟨point i,line d i,(flag d ht i).2.1,(flag d ht i).2.2.1,(flag d ht i).2.2.2,hi⟩

end Puncture4043

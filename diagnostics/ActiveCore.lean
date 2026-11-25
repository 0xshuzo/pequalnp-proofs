import Mathlib
import PEqualNP.Outside.L_meta_1483
namespace Active1739
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1483
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
theorem supported_budget (hC : Monotone2 C) (he : GraphEval C G)
    (A : Finset (Fin n)) (hdegree : ∀ v∈A, ∃ u, G.Adj v u) (ho : C.output ∈ living n C) :
    open Classical in A.card + ((living n C).filter (Branch n C)).card ≤ C.size + 1 := by
  classical
  let W := living n C
  let S := W.filter (fun a => ¬ a < n)
  let B := W.filter (Branch n C)
  let R := W.erase C.output
  let V := A.image Fin.val
  have vc : V.card=A.card := Finset.card_image_of_injective _ Fin.val_injective
  have ss : S ⊆ W := Finset.filter_subset _ _
  have hSub : V ⊆ W \ S := by
    intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u,hu⟩ := hdegree v hv
    refine Finset.mem_sdiff.mpr ⟨mem_living.mpr ⟨by have := v.isLt;omega,input_live he hu⟩,?_⟩
    intro hs
    exact (Finset.mem_filter.mp hs).2 v.isLt
  have count := Finset.card_le_card hSub
  have sum := Finset.card_sdiff_add_card_eq_card ss
  have hW : A.card+S.card≤W.card := by omega
  have hR : R.card + 1 = W.card := by
    dsimp [R]
    have h := Finset.card_erase_add_one ho
    exact h
  have hS : S.card ≤ C.gates.length := by
    rw [show C.gates.length = (Finset.range C.gates.length).card by simp]
    apply Finset.card_le_card_of_injOn (fun a => a-n)
    · intro a ha
      have h : a < n+C.gates.length := (mem_living.1 (Finset.mem_filter.1 ha).1).1
      have h0 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      apply Finset.mem_range.2
      change a-n < C.gates.length
      omega
    · intro a ha b hb hab
      have h1 : n ≤ a := Nat.le_of_not_gt (Finset.mem_filter.1 ha).2
      have h2 : n ≤ b := Nat.le_of_not_gt (Finset.mem_filter.1 hb).2
      change a-n=b-n at hab
      omega
  have hoNone : ¬ Branch n C C.output := by
    intro h
    have hgt : 0 < (readers n C C.output).card := by unfold Branch at h; omega
    obtain ⟨b,hb⟩ := Finset.card_pos.1 hgt
    have hs := mem_readers.1 hb
    exact (Nat.not_lt_of_ge (next_le hs.2)) hs.1.1
  have hlow : R.card+B.card ≤ ∑ a ∈ W, (readers n C a).card := by
    have eR : (∑ a ∈ W, (if a=C.output then 0 else 1 : ℕ)) = R.card := by
      calc
        _ = ∑ a ∈ W, (if a≠C.output then 1 else 0 : ℕ) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : a=C.output <;> simp [h]
        _ = R.card := by rw [← Finset.sum_filter]; simp [R,Finset.filter_ne']
    have eB : (∑ a ∈ W, (if Branch n C a then 1 else 0 : ℕ)) = B.card := by
      rw [← Finset.sum_filter]
      simp [B]
    rw [← eR,← eB,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    have hl := (mem_living.1 ha).2
    by_cases heq : a=C.output
    · subst a
      simp [hoNone]
    · by_cases hb : Branch n C a
      · have hb' : 2 ≤ (readers n C a).card := hb
        simpa [heq,hb] using hb'
      · simpa [heq,hb] using Nat.succ_le_of_lt (Finset.card_pos.2 (live_readers_nonempty hl heq))
  have hcomm :
      (∑ a ∈ W, (readers n C a).card) =
        ∑ j ∈ W, (W.filter fun a => LNext n C a j).card := by
    simp_rw [readers_filter,Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have hupp : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤ 2*S.card := by
    have H : (∑ j ∈ W, (W.filter fun a => LNext n C a j).card) ≤
        ∑ j ∈ W, (if j<n then 0 else 2 : ℕ) :=
      Finset.sum_le_sum fun j hj => incoming_bound hC hj
    have e : (∑ j ∈ W, (if j<n then 0 else 2 : ℕ)) = 2*S.card := by
      simp [S,Finset.sum_ite, Nat.mul_comm]
    exact H.trans_eq e
  rw [hcomm] at hlow
  change A.card+B.card ≤ C.gates.length+1
  omega


theorem coreCover (A : Finset (Fin n)) (hA : ∀ i∈A, ∃ j,G.Adj i j) (t : Nat)
    (edge : ∃ u v,G.Adj u v)
    (square : ∀ u v a b,u≠v → a≠b → G.Adj u a → G.Adj u b → G.Adj v a → G.Adj v b → False)
    (ht : ∀ S : Finset (Fin n),
      (∀ u v,G.Adj u v → 2≤(G.neighborSet u).ncard → 2≤(G.neighborSet v).ncard → u∈S ∨ v∈S) → t≤S.card)
    (hC : Monotone2 C) (hE : GraphEval C G) : A.card+t≤C.size+1 := by
  classical
  have two (u : Fin n) (d : 2≤(G.neighborSet u).ncard) :
      ∃ a b : Fin n,a≠b ∧ G.Adj u a ∧ G.Adj u b := by
    rw [SimpleGraph.ncard_neighborSet,SimpleGraph.degree] at d
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp d
    exact ⟨a,b,ne,by simpa using ha,by simpa using hb⟩
  have htwins (v w : Fin n) (ne : v≠w) (_ : ¬G.Adj v w) (dv : 2≤(G.neighborSet v).ncard)
      (_ : 2≤(G.neighborSet w).ncard) : ∃ u,¬(G.Adj v u ↔ G.Adj w u) := by
    obtain ⟨a,b,ab,ha,hb⟩ := two v dv
    by_contra! eq
    exact square v w a b ne ab ha hb ((eq a).mp ha) ((eq b).mp hb)
  have hadj (u v : Fin n) (uv : G.Adj u v) (du : 2≤(G.neighborSet u).ncard)
      (dv : 2≤(G.neighborSet v).ncard) :
      ∃ a b,G.Adj u a ∧ a≠v ∧ G.Adj v b ∧ b≠u ∧ (a=b ∨ ¬G.Adj a b) := by
    have other (s t : Fin n) (ds : 2≤(G.neighborSet s).ncard) : ∃ a,G.Adj s a ∧ a≠t := by
      obtain ⟨a,b,d,ha,hb⟩ := two s ds
      by_cases atv : a=t
      · exact ⟨b,hb,fun e=>d (atv.trans e.symm)⟩
      · exact ⟨a,ha,atv⟩
    obtain ⟨a,ua,av⟩ := other u v du
    obtain ⟨b,vb,bu⟩ := other v u dv
    exact ⟨a,b,ua,av,vb,bu,Or.inr (fun ab=>square u b v a bu.symm av.symm uv ua vb.symm ab.symm)⟩
  obtain ⟨v,w,hve⟩ := edge
  have ho := (edge_at_output hE hve).2
  have ho' : C.output ∈ living n C := mem_living.2 ⟨ho, Relation.ReflTransGen.refl⟩
  let S : Finset (Fin n) := Finset.univ.filter fun v =>
    2 ≤ (G.neighborSet v).ncard ∧ Eligible C v
  have hS (u : Fin n) : u ∈ S ↔ 2 ≤ (G.neighborSet u).ncard ∧ Eligible C u := by
    simp [S]
  have htc : t ≤ S.card := by
    apply ht S
    intro a b hab hda hdb
    obtain ⟨u,v,hu,hu',hv,hv',hind⟩ := hadj a b hab hda hdb
    rcases covers_edge hC hE hab hu hu' hv hv' hind with ha | hb
    · exact Or.inl ((hS a).2 ⟨hda,ha⟩)
    · exact Or.inr ((hS b).2 ⟨hdb,hb⟩)
  let B := (living n C).filter (Branch n C)
  let f (u : Fin n) := if h : Eligible C u then firstBranch C u h else 0
  have hf (u : Fin n) (hu : Eligible C u) : f u = firstBranch C u hu := by simp [f,hu]
  have hcap : S.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f
    · intro u hu
      obtain ⟨_,hs⟩ := (hS u).1 hu
      have hb := firstBranch_spec u hs
      have hlt := (next_le hb.1).trans_lt ho
      show f u ∈ B
      rw [hf u hs]
      exact Finset.mem_filter.2 ⟨mem_living.2 ⟨hlt,hb.1⟩,hb.2.2⟩
    · intro u hu v hv huv
      obtain ⟨hdu,hsu⟩ := (hS u).1 hu
      obtain ⟨hdv,hsv⟩ := (hS v).1 hv
      rw [hf u hsu,hf v hsv] at huv
      exact branch_injective hC hE htwins hsu hsv hdu hdv huv
  have hbudget := supported_budget hC hE A hA ho'
  exact (Nat.add_le_add_left (htc.trans hcap) A.card).trans hbudget

end Active1739

import Mathlib
import PEqualNP.Outside.L_meta_4322

namespace Majority5264
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.Outside.L_meta_4322
open Classical
variable {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
lemma uniqueCenter (r : ℕ) (h4 : C4free G) (A : Finset (Fin n)) (hA : 2*r+2 ≤ A.card) :
    (Finset.univ.filter fun z => (A.filter fun x => ¬ G.Adj z x).card ≤ r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz z' hz'
  rw [Finset.mem_filter] at hz hz'
  by_contra hne
  have h1 := Finset.le_card_sdiff
    ((A.filter fun x => ¬ G.Adj z x) ∪ (A.filter fun x => ¬ G.Adj z' x)) A
  have h2 := Finset.card_union_le (A.filter fun x => ¬ G.Adj z x)
    (A.filter fun x => ¬ G.Adj z' x)
  have h3 : 1 < (A \ ((A.filter fun x => ¬ G.Adj z x) ∪
      (A.filter fun x => ¬ G.Adj z' x))).card := by
    have := hz.2
    have := hz'.2
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h3
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, not_or, not_and,
    not_not] at hx hy
  exact h4 z z' x y hne hxy (hx.2.1 hx.1) (hy.2.1 hy.1) (hx.2.2 hx.1) (hy.2.2 hy.1)

lemma descend (r : ℕ) (hC : IsAO2 n C) (z y : Fin n) :
    ∀ w, y ∈ orIn n C w → 2*r+2 ≤ (orIn n C w).card →
      ((orIn n C w).filter fun x => ¬ G.Adj z x).card ≤ r →
      ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ 2*r+2 ≤ (orIn n C (n + g)).card ∧
        ((orIn n C (n + g)).filter fun x => ¬ G.Adj z x).card ≤ r ∧
        ∃ i : Fin 2, y ∈ orIn n C (opnd C g i) ∧ (orIn n C (opnd C g i)).card ≤ 2*r+1 := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hy hbig ht
    by_cases hw : n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or
    · obtain ⟨h1, h2, hop⟩ := hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have e : n + k - n = k := by omega
      rw [e] at h2 hop
      obtain ⟨i, hi⟩ := orIn_split hC h2 hop hy
      by_cases hs : (orIn n C (opnd C k i)).card ≤ 2*r+1
      · exact ⟨k, h2, hop, hbig, ht, i, hi, hs⟩
      · exact ih _ (opnd_lt hC h2 i) hi (by omega)
          ((Finset.card_le_card (Finset.filter_subset_filter _ (orIn_sub hC h2 hop i))).trans ht)
    · have := zqorIn_small n C w hw
      omega


noncomputable def pool (G : SimpleGraph (Fin n)) (C : Circuit) (r g : ℕ) :
    Finset (Sym2 (Fin n)) :=
  if 2*r+2 ≤ (orIn n C (n+g)).card then
    ((Finset.univ.filter fun z => ((orIn n C (n+g)).filter fun x => ¬ G.Adj z x).card ≤ r) ×ˢ
      ((Finset.univ : Finset (Fin 2)).biUnion fun i =>
        sm (2*r+1) (orIn n C (opnd C g i)))).image (fun p => s(p.1,p.2))
  else ∅

lemma pool_card (h4 : C4free G) (r g : ℕ) : (pool G C r g).card ≤ 2*(2*r+1) := by
  unfold pool
  split_ifs with h
  · have h' := img_card _ _ 1 (2*(2*r+1)) (uniqueCenter r h4 _ h)
      (bi2_card (fun i => sm (2*r+1) (orIn n C (opnd C g i))) (2*r+1) (fun i => sm_card))
    simpa only [one_mul] using h'
  · simp

lemma member (hAO : IsAO2 n C) (u v : Fin n) (w r : ℕ) (hv : v ∈ orIn n C w)
    (wide : 2*r+2 ≤ (orIn n C w).card)
    (bad : ((orIn n C w).filter fun z => ¬G.Adj u z).card ≤ r) :
    ∃ g < C.gates.length, s(u,v) ∈ pool G C r g := by
  obtain ⟨g,hg,_,hw,ht,i,hi,hsm⟩ := descend r hAO u v w hv wide bad
  refine ⟨g,hg,?_⟩
  unfold pool
  rw [if_pos hw]
  exact Finset.mem_image.2 ⟨(u,v), Finset.mem_product.2 ⟨
    Finset.mem_filter.2 ⟨Finset.mem_univ _,ht⟩,
    Finset.mem_biUnion.2 ⟨i,Finset.mem_univ _,mem_sm hsm hi⟩⟩, rfl⟩

theorem paid :
∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : Circuit) (R : ℕ), (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → IsAO2 n C →
        ∀ E : Finset (Sym2 (Fin n)), (∀ e ∈ E, ∃ (u v : Fin n) (w r : ℕ), e = s(u,v) ∧ v ∈ orIn n C w ∧
          r ≤ R ∧ 2*r+2 ≤ (orIn n C w).card ∧
          ((orIn n C w).filter (fun z => ¬ G.Adj u z)).card ≤ r) →
        E.card ≤ ((R+1)*(2*(2*R+1)))*C.size := by
  intro n G inst C R hG hAO E hE
  classical
  have h4 : C4free G := by
    intro a b x y hab hxy hax hay hbx hby
    exact no4 G hG a x b y hax hbx.symm hby hay.symm hab hxy
  let Q := fun r => (Finset.range C.gates.length).biUnion (pool G C r)
  have cover : E ⊆ (Finset.range (R+1)).biUnion Q := by
    intro e he
    obtain ⟨u,v,w,r,rfl,hv,hr,hw,ht⟩ := hE e he
    obtain ⟨g,hg,hm⟩ := member hAO u v w r hv hw ht
    exact Finset.mem_biUnion.2 ⟨r,Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.2 ⟨g,Finset.mem_range.mpr hg,hm⟩⟩
  have bound (r : ℕ) (hr : r ∈ Finset.range (R+1)) :
      (Q r).card ≤ C.gates.length*(2*(2*R+1)) := by
    have hlt := Finset.mem_range.mp hr
    have hb := Finset.card_biUnion_le_card_mul (Finset.range C.gates.length)
      (pool G C r) (2*(2*R+1)) (fun g _ => (pool_card h4 r g).trans (by omega))
    simpa only [Q, Finset.card_range] using hb
  have hb := Finset.card_biUnion_le_card_mul (Finset.range (R+1)) Q
    (C.gates.length*(2*(2*R+1))) bound
  rw [Finset.card_range] at hb
  calc
    E.card ≤ _ := Finset.card_le_card cover
    _ ≤ _ := hb
    _ = ((R+1)*(2*(2*R+1)))*C.size := by change _ = _*C.gates.length; ring

end Majority5264

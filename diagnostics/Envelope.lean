import Mathlib
import PEqualNP.Outside.L_meta_3696

namespace Envelope606
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_3696
-- The walk below is the girth bridge of L3805.
theorem four {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hgirth : ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) :
    NoFourCycle G := by
  intro a b hab
  rw [Finset.card_le_one]
  intro w1 hw1 w2 hw2
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  have hw1a : w1 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw1.1)
  have hw1b : w1 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw1.2)
  have hw2a : w2 ≠ a := fun h => G.loopless.irrefl a (h ▸ hw2.1)
  have hw2b : w2 ≠ b := fun h => G.loopless.irrefl b (h ▸ hw2.2)
  let p : G.Walk a a :=
    SimpleGraph.Walk.cons hw1.1
      (SimpleGraph.Walk.cons hw1.2.symm
        (SimpleGraph.Walk.cons hw2.2
          (SimpleGraph.Walk.cons hw2.1.symm SimpleGraph.Walk.nil)))
  have hcyc : p.IsCycle := by
    refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · simp [p, SimpleGraph.Walk.edges, Sym2.eq_iff, hw1a, hw1b, hw2a, hw2b, hab, hne,
        hab.symm, Ne.symm hne, hw1a.symm, hw1b.symm, hw2a.symm, hw2b.symm]
    · simp [p]
    · simp [p, SimpleGraph.Walk.support, hw1a, hw2a, hw1b, hw2b, hab, hne, hab.symm, Ne.symm hne,
        hw1a.symm, hw2a.symm, hw1b.symm, hw2b.symm]
  have hlen := hgirth a p hcyc
  simp [p] at hlen

theorem active {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit)
    (fan : ∀g∈D.gates,g.inputs.length≤2)
    (correct : circuitFun n D = fun x => decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true)) :
    (Finset.univ.filter (fun p : Fin n=>∃q,G.Adj p q)).card≤D.size+1 := by
  classical
  obtain ⟨S,cap,agreement⟩ := dep n D.gates fan {D.output}
  have memS (p q : Fin n) (pq : G.Adj p q) : p.val∈S := by
    by_contra absent
    let x (v : Fin n) := decide (v=p ∨ v=q)
    let y (v : Fin n) := decide (v=q)
    have det : circuitFun n D x=circuitFun n D y := by
      change (run D.gates (List.ofFn x)).getD D.output false = (run D.gates (List.ofFn y)).getD D.output false
      apply agreement _ _ (by simp) (by simp) _ _ (by simp)
      intro i hi
      by_cases h : i<n
      · let v : Fin n := ⟨i,h⟩
        have ne : v≠p := by intro e;exact absent ((congrArg Fin.val e) ▸ hi)
        change (List.ofFn x).getD v.val false=(List.ofFn y).getD v.val false
        rw [ofFn_getD,ofFn_getD]
        simp [x,y,ne]
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    rw [correct] at det
    have pos : ∃i j,G.Adj i j ∧ x i=true ∧ x j=true := ⟨p,q,pq,by simp [x],by simp [x]⟩
    have neg : ¬∃i j,G.Adj i j ∧ y i=true ∧ y j=true := by
      rintro ⟨i,j,h,hi,hj⟩
      simp only [y,decide_eq_true_eq] at hi hj
      rw [hi,hj] at h
      exact G.loopless.irrefl q h
    simp [pos,neg] at det
  have sub : (Finset.univ.filter (fun p : Fin n=>∃q,G.Adj p q)).image Fin.val ⊆ S := by
    rintro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨q,hq⟩ := (Finset.mem_filter.mp hp).2
    exact memS p q hq
  have h := Finset.card_le_card sub
  rw [Finset.card_image_of_injective _ Fin.val_injective] at h
  exact h.trans (by simpa [Circuit.size] using cap)

theorem square {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀(v : Fin n)(p : G.Walk v v),p.IsCycle→5≤p.length) (D : Circuit)
    (fan : ∀g∈D.gates,g.inputs.length≤2)
    (correct : circuitFun n D = fun x => decide (∃i j,G.Adj i j ∧ x i=true ∧ x j=true)) :
    (2*G.edgeFinset.card)^2 ≤ (D.size+1)*(2*G.edgeFinset.card+(D.size+1)*D.size) := by
  classical
  let S := Finset.univ.filter (fun p : Fin n=>∃q,G.Adj p q)
  let E := Finset.univ.filter (fun t : Fin n×Fin n=>G.Adj t.1 t.2)
  have rect : ∀a a' b b' : Fin n,a≠a'→b≠b'→¬((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E) := by
    rintro a a' b b' ha hb ⟨h1,h2,h3,h4⟩
    have r := four girth a a' ha
    exact hb (Finset.card_le_one.mp r b (by simpa [E] using And.intro ((Finset.mem_filter.mp h1).2) ((Finset.mem_filter.mp h3).2))
      b' (by simpa [E] using And.intro ((Finset.mem_filter.mp h2).2) ((Finset.mem_filter.mp h4).2)))
  have neigh (u : Fin n) : (S.filter (fun v=>(u,v)∈E))= G.neighborFinset u := by
    ext v
    simp only [E,S,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨And.right,fun h=>⟨⟨u,h.symm⟩,h⟩⟩
  have sum : (∑i∈S,G.degree i)=2*G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ absent
    rw [← G.card_neighborFinset_eq_degree,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
    exact fun j hj=>absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,(G.mem_neighborFinset _ _).mp hj⟩)
  have ecard : ((S ×ˢ S).filter (fun t => t∈E)).card=2*G.edgeFinset.card := by
    rw [card_filter_product_eq_sum]
    simp only [neigh,G.card_neighborFinset_eq_degree]
    exact sum
  have bound := c4sq (Fin n) (Fin n) E rect S S
  rw [ecard] at bound
  have cap : S.card≤D.size+1 := active G D fan correct
  exact bound.trans (Nat.mul_le_mul cap (Nat.add_le_add_left (Nat.mul_le_mul cap (by omega)) _))

theorem window {e s c : Nat} (hc : 1≤c) (window : s+2*c≤4*c^2)
    (envelope : (2*e)^2 ≤ (s+1)*(2*e+(s+1)*s)) : e≤c*(s+1) := by
  by_contra! large
  zify at hc window envelope large
  have threshold : (0 : Int) ≤ (s+1)^2 * (4*c^2-2*c-s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have gap : (0 : Int) < (2*e-2*c*(s+1))*(2*e+2*c*(s+1)-(s+1)) := by
    apply mul_pos
    · linarith
    · have h : (0 : Int) ≤ (2*c-1)*(s+1) := mul_nonneg (by linarith) (by positivity)
      nlinarith
  nlinarith
end Envelope606

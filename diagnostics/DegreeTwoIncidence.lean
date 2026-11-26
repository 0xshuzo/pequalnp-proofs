import Mathlib
import PEqualNP.Outside.L_meta_17589
import PEqualNP.Outside.L_meta_3493
import PEqualNP.Outside.L_meta_7639

namespace DegreeTwoPilot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_17589_aux

theorem cover_from_vertex_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : NoFourCycle G) (hdeg : ∀ v, 2 ≤ G.degree v)
    (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G.Adj x) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      n + T.card ≤ C.size + 1 := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨∅, fun u => Fin.elim0 u, by simp⟩
  have two (v : Fin n) : ∃ a b, G.Adj v a ∧ G.Adj v b ∧ a ≠ b := by
    have hd : 1 < (G.neighborFinset v).card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg v
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hd
    exact ⟨a, b, (G.mem_neighborFinset v a).mp ha, (G.mem_neighborFinset v b).mp hb, hab⟩
  have hg : sem_Gr G.Adj := by
    refine ⟨fun _ _ h => h.symm, fun v => G.loopless.irrefl v, ?_, ?_⟩
    · intro v w hvw
      obtain ⟨a,b,ha,hb,hab⟩ := two v
      by_cases hwa : G.Adj w a
      · refine ⟨b,hb,fun hwb => ?_⟩
        have both : 1 < (Finset.univ.filter fun t => G.Adj v t ∧ G.Adj w t).card :=
          Finset.one_lt_card.mpr ⟨a, by simp [ha,hwa], b, by simp [hb,hwb], hab⟩
        exact (Nat.not_lt_of_ge (hfree v w hvw)) both
      · exact ⟨a,ha,hwa⟩
    · intro u v
      obtain ⟨a,b,ha,hb,hab⟩ := two u
      by_cases hav : a = v
      · exact ⟨b,hb,fun h => hab (hav.trans h.symm)⟩
      · exact ⟨a,ha,hav⟩
  have nosingle (i : Fin n) : ¬ sem_Edge G.Adj (fun k => decide (k = i)) := by
    rintro ⟨u,v,huv,hu,hv⟩
    have hui : u = i := of_decide_eq_true hu
    have hvi : v = i := of_decide_eq_true hv
    exact huv.ne (hui.trans hvi.symm)
  have positive (i j : Fin n) (hij : G.Adj i j) :
      sem_Edge G.Adj (fun k => decide (k = i) || decide (k = j)) :=
    ⟨i,j,hij,by simp,by simp⟩
  obtain ⟨D,hlive,hlen,hval⟩ := normalize_strictLive (n := n) C hmono
    (by
      intro b
      let v : Fin n := ⟨0, by omega⟩
      cases b
      · obtain ⟨u,_,hu,_,_⟩ := two v
        refine ⟨_, ?_⟩
        rw [Ne, Bool.not_eq_false]
        exact (hC _).2 (positive v u hu)
      · exact ⟨_, fun he => nosingle v ((hC _).1 he)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun he => nosingle i ((hC _).1 ?_)⟩
      rw [he]
      simp)
    (by
      intro i
      obtain ⟨j,_,hij,_,_⟩ := two i
      refine ⟨fun k => decide (k = j), fun k => decide (k = i) || decide (k = j),
        fun k hk => by simp [hk], fun he => nosingle j ((hC _).1 ?_)⟩
      rw [he]
      exact (hC _).2 (positive i j hij))
  have hcomp : sem_Comp n G.Adj D := fun x => by rw [hval x]; exact hC x
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hg hlive.1 hcomp
  refine ⟨eligSet n D, fun _ _ he => sem_elig_cover hg hlive hcomp he, ?_⟩
  have hp := elig_le_Bplus hlive.1 b hb
  have ht := Bplus_le_total n D
  have he := surplus_identity hlive
  omega

theorem degree_two_cost {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : NoFourCycle G) (hdeg : ∀ v, G.degree v = 2)
    (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge G.Adj x) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.size + 1 := by
  obtain ⟨T,hT,hsize⟩ := cover_from_vertex_count G hfree (fun v => (hdeg v).ge) C hmono hC
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp [hdeg] at hsum
  exact ⟨T,hT,by omega⟩

end DegreeTwoPilot

namespace DegreeTwoPilot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_7639
open PEqualNP.Outside.L_meta_17589_aux

theorem incidence_charge {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (hrow : ∀ p, (Finset.univ.filter (fun l => I p l)).card = 2)
    (hcol : ∀ l, (Finset.univ.filter (fun p => I p l)).card = 2)
    (hfree : ∀ p q l k, p ≠ q → l ≠ k → ¬(I p l ∧ I p k ∧ I q l ∧ I q k))
    (C : Circuit) (hao : IsAO2 (n+m) C)
    (hC : ∀ x : Fin (n+m) → Bool, circuitFun (n+m) C x =
      decide (∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) :
    ∃ T : Finset (Fin (n+m)),
      (∀ p l, I p l → Fin.castAdd m p ∈ T ∨ Fin.natAdd n l ∈ T) ∧
      (PEqualNP.ReadTwo.incid I).card + T.card ≤ C.size+1 := by
  classical
  let E := PEqualNP.ReadTwo.incid I
  let G := graph E
  letI : DecidableRel G.Adj := Classical.decRel _
  have memE (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by
    simp [E, PEqualNP.ReadTwo.incid]
  have hsquare : NoFourCycle G := by
    apply noRectangle
    simpa only [memE] using hfree
  have hm : Monotone2 C := fun g hg => ⟨by simpa using hao.1 g hg, (hao.2.2 g hg).le⟩
  have heval (x : Fin (n+m) → Bool) : C.eval (List.ofFn x) = true ↔ sem_Edge G.Adj x := by
    change circuitFun (n+m) C x = true ↔ _
    rw [hC, decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,he,hp,hl⟩
      exact ⟨Fin.castAdd m p, Fin.natAdd n l, by simpa [G,graph,cross] using (memE p l).mpr he, hp, hl⟩
    · rintro ⟨u,v,ha,hu,hv⟩
      cases u using Fin.addCases <;> cases v using Fin.addCases <;> simp [G,graph,cross] at ha
      · exact ⟨_,_,(memE _ _).mp ha,hu,hv⟩
      · exact ⟨_,_,(memE _ _).mp ha,hv,hu⟩
  have disj (p : Fin n) (l : Fin m) : Fin.castAdd m p ≠ Fin.natAdd n l := by
    intro he
    have hv := congrArg Fin.val he
    change p.val = n+l.val at hv
    omega
  have injP : Function.Injective (Fin.castAdd m : Fin n → Fin (n+m)) := by
    intro a b h
    exact Fin.ext (congrArg Fin.val h)
  have injL : Function.Injective (Fin.natAdd n : Fin m → Fin (n+m)) := by
    intro a b h
    have hv := congrArg Fin.val h
    change n+a.val = n+b.val at hv
    exact Fin.ext (Nat.add_left_cancel hv)
  have deg (u : Fin (n+m)) : G.degree u = 2 := by
    cases u using Fin.addCases with
    | left p =>
      let S := Finset.univ.filter (fun l => I p l)
      have eq : G.neighborFinset (Fin.castAdd m p) = S.image (Fin.natAdd n) := by
        ext v
        rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
        cases v using Fin.addCases with
        | left q =>
          simp [G,graph,cross,fun l => (disj q l).symm]
        | right l =>
          simp [G,graph,cross,memE,S,injL.eq_iff]
      rw [← SimpleGraph.card_neighborFinset_eq_degree,eq,Finset.card_image_of_injective _ injL]
      exact hrow p
    | right l =>
      let S := Finset.univ.filter (fun p => I p l)
      have eq : G.neighborFinset (Fin.natAdd n l) = S.image (Fin.castAdd m) := by
        ext v
        rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
        cases v using Fin.addCases with
        | left p =>
          simp [G,graph,cross,memE,S,injP.eq_iff]
        | right k =>
          simp [G,graph,cross,fun p => disj p k]
      rw [← SimpleGraph.card_neighborFinset_eq_degree,eq,Finset.card_image_of_injective _ injP]
      exact hcol l
  obtain ⟨T,hcover,hcost⟩ := degree_two_cost G hsquare deg C hm heval
  refine ⟨T,fun p l hp => hcover (Fin.castAdd m p) (Fin.natAdd n l) ?_,?_⟩
  · simpa [G,graph,cross] using (memE p l).mpr hp
  · have hcount : E.card ≤ G.edgeFinset.card := counts E
    exact (Nat.add_le_add_right hcount T.card).trans hcost

theorem degree_two_normalization : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ p, (Finset.univ.filter (fun l => x3 p l)).card = 2) →
  (∀ l, (Finset.univ.filter (fun p => x3 p l)).card = 2) →
   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ x15 ∈ x11 ∧ x16 ∈ x10 := by
  intro n m I inst C hrow hcol hfree hao hC
  obtain ⟨T,hcover,hcost⟩ := incidence_charge I hrow hcol hfree C hao hC
  obtain ⟨D,P,L,ok,computes,lsize,shape⟩ := PEqualNP.Outside.L_meta_3493 n m I T hcover
  exact ⟨D,P,L,ok,computes,by omega,shape⟩

end DegreeTwoPilot

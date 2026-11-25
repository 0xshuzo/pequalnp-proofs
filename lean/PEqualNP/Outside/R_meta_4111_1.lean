import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 500000 in
theorem PEqualNP.Outside.R_meta_4111_1
    (compress : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (S : Finset ℕ),
      let w := fun (u v : Fin n) (i : ℕ) (x : Fin n → Bool) =>
        (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD i false
      FanInTwo C → S ⊆ Finset.range C.size → (∀ j ∈ S, (∀ x, w u v (n+j) x = false) ∨
        ∃ i < n+j, ∀ x, w u v (n+j) x = w u v i x) →
      ∃ t, t + S.card ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t)
    (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit),
      let w := fun (u v : Fin n) (i : ℕ) (x : Fin n → Bool) =>
        (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD i false
      ¬ G.Colorable 2 →
      (∀ u, (∃ v, G.Adj u v) → (G.neighborSet u).ncard = 3) →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∃ u v, G.Adj u v) →
      (∀ x, circuitFun n C x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
        C.size + 1 < G.edgeSet.ncard + T.card) →
      IsMinimalCircuit n C →
      (∀ u v, G.Adj u v → ∀ S ⊆ Finset.range C.size, (∀ j ∈ S, (∀ x, w u v (n+j) x = false) ∨
        ∃ i < n+j, ∀ x, w u v (n+j) x = w u v i x) → S.card ≤ 6) →
      ∃ u v, G.Adj u v ∧ ∃ t, t+7 ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update (Function.update x u false) v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∀ (x8 : Fin x1 → Bool), x3 x8 = Bool.true ↔ ∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true) → ∀ (x9 : ℕ), (∀ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) → x9 + (1 : ℕ) < x2.edgeSet.ncard + x10.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x3 x9 → ∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ ∃ (x14 : ℕ), x14 + (7 : ℕ) ≤ x9 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x3 (Function.update (Function.update x15 x12 Bool.false) x13 Bool.false)) x14 := by
  classical
  intro n G f hnon degree girth edge correct s hs hgiven
  have has : ∃ k, HasCircuitSize n f k := ⟨s,hgiven⟩
  obtain ⟨C,hfan,hsize,hval⟩ := Nat.find_spec has
  have eqf : circuitFun n C = f := funext hval
  have small : C.size ≤ s := hsize.trans (Nat.find_min' has hgiven)
  have least : IsMinimalCircuit n C := by
    refine ⟨hfan,?_⟩
    intro D hD heq
    apply hsize.trans
    apply Nat.find_min' has
    exact ⟨D,hD,le_rfl,congrFun (heq.trans eqf)⟩
  by_contra no
  have limited (u v : Fin n) (hadj : G.Adj u v) (S : Finset ℕ) (sub : S ⊆ Finset.range C.size)
      (aliases : ∀ j ∈ S,
        (∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD (n+j) false = false) ∨
        ∃ i < n+j, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD (n+j) false =
          (C.wires (List.ofFn (Function.update (Function.update x u false) v false))).getD i false) : S.card ≤ 6 := by
    by_contra! many
    obtain ⟨t,save,works⟩ := compress n C u v S hfan sub aliases
    rw [eqf] at works
    exact no ⟨u,v,hadj,t,by omega,works⟩
  obtain ⟨u,v,hadj,t,save,works⟩ := sparse n G C hnon degree girth edge
    (fun x => by rw [eqf]; exact correct x) (fun T cover => by have h := hs T cover; omega) least limited
  rw [eqf] at works
  exact no ⟨u,v,hadj,t,by omega,works⟩

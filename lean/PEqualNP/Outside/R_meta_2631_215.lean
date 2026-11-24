import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2631_215
    (normal : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let e (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let r (v : Fin n) := C.gates.filter fun g => (e g).contains v.val
      let a (v : Fin n) := ∃ g∈r v, g.op=.and
      IsMinimalCircuit n C → circuitFun n C=f →
      (∀ v∉A,(G.neighborSet v).ncard=3) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      (∀ u v,G.Adj u v → u∉A) → (∃ u v,G.Adj u v) →
      (∀ v∉A,2≤(r v).length ∧ (r v).length≤3 ∧ ((r v).length=3 → ∀ g∈r v,g.op=.or)) →
∀ v∉A, a v → (∃ h∈r v, ∀ w : Fin n, w≠v → w.val∉e h) ∧
        ∃ t, t+3≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let f := graphFun G A
      let e (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
      let r (v : Fin n) := C.gates.filter fun g => (e g).contains v.val
      let a (v : Fin n) := ∃ g∈r v, g.op=.and
      IsMinimalCircuit n C → circuitFun n C=f →
      (∀ v∉A,(G.neighborSet v).ncard=3) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      (∀ u v,G.Adj u v → u∉A) → (∃ u v,G.Adj u v) →
      (∀ v∉A,2≤(r v).length ∧ (r v).length≤3 ∧ ((r v).length=3 → ∀ g∈r v,g.op=.or)) →
(∃ v∉A, a v) →
      (∀ v∉A, a v → (∃ h∈r v, ∀ w : Fin n, w≠v → w.val∉e h) ∧
        (∃ D : Circuit, IsMinimalCircuit n D ∧ circuitFun n D=(fun x => f (Function.update x v false)) ∧ D.size+3=C.size)) →
      ∃ v∉A, ¬a v ∧ ∃ t, t+4≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  intro n G inst A C
  dsimp only
  intro deg girth iso edge fan eval least limit witness
  let e (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
  let r (v : Fin n) := C.gates.filter fun g => (e g).contains v.val
  let a (v : Fin n) := ∃ g∈r v, g.op=.and
  let f := graphFun G A
  have minimal : IsMinimalCircuit n C := ⟨fan,fun D hf same => least D.size
    ⟨D,hf,le_rfl,congrFun (same.trans eval)⟩⟩
  obtain ⟨v,va,_,has⟩ := witness
  have start : ∃ w∉A,a w := ⟨v,va,has⟩
  by_cases win : ∃ w∉A, a w ∧ ∃ t, t+4≤C.size ∧ HasCircuitSize n (fun x => f (Function.update x w false)) t
  · obtain ⟨w,wa,_,t,sz,ht⟩ := win
    exact ⟨w,wa,t,sz,ht⟩
  · obtain ⟨w,wa,_,t,sz,ht⟩ := residual n G A C minimal eval deg girth iso edge limit start (by
      intro w wa aw
      obtain ⟨arch,t,paid,D,df,cost,hD⟩ := normal n G A C minimal eval deg girth iso edge limit w wa aw
      have capped (k : ℕ) (hk : HasCircuitSize n (fun x => f (Function.update x w false)) k) :
          C.size≤k+3 := by
        by_contra bound
        exact win ⟨w,wa,aw,k,by omega,hk⟩
      have self := capped D.size ⟨D,df,le_rfl,hD⟩
      have eq : D.size+3=C.size := by omega
      refine ⟨arch,D,⟨df,?_⟩,funext hD,eq⟩
      intro E ef same
      have el := capped E.size ⟨E,ef,le_rfl,congrFun (same.trans (funext hD))⟩
      omega)
    exact ⟨w,wa,t,sz,ht⟩

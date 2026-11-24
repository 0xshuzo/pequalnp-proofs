import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4095_17
    (budget : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let r (v : Fin n) := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      let k := (Aᶜ.filter (fun v => (r v).length=3)).card
      IsMinimalCircuit n C → circuitFun n C=graphFun G A →
      (∀ v∉A,(G.neighborSet v).ncard=3) → (∀ a b,G.Adj a b → a∉A) →
      (∃ a b,G.Adj a b) → (∀ v∉A,2≤(r v).length) →
      ∀ T : Finset (Fin n), (∀ a b,G.Adj a b → a∈T ∨ b∈T) → 2*T.card≤Aᶜ.card+2*k →
      ∃ v∉A, ∃ t, t+4≤C.size ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) t)
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
      (∀ v∉A,(G.neighborSet v).ncard=3) → (∀ a b,G.Adj a b → a∉A) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      ∃ T : Finset (Fin n), (∀ a b,G.Adj a b → a∈T ∨ b∈T) ∧ 3*T.card≤2*Aᶜ.card)
    (residual : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let r (v : Fin n) := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      let k := (Aᶜ.filter (fun v => (r v).length=3)).card
      IsMinimalCircuit n C → circuitFun n C=graphFun G A →
      (∀ v∉A,(G.neighborSet v).ncard=3) → (∀ a b,G.Adj a b → a∉A) →
      (∀ v (w : G.Walk v v),w.IsCycle → 7≤w.length) →
      (∀ v∉A,(r v).length=2 ∨ ((r v).length=3 ∧ ∀ g∈r v,g.op=.or)) →
      (∃ v∉A, (∃ g∈r v,g.op=.and) ∧ ∃ h∈r v,h.op=.or) →
      6*k<Aᶜ.card → (∀ T : Finset (Fin n), (∀ a b,G.Adj a b → a∈T ∨ b∈T) → Aᶜ.card+2*k<2*T.card) →
      ∃ v∉A, ∃ t, t+4≤C.size ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => List.take (bif x7.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x7.inputs;   have x8 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x8 : Fin x1) => List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x9).contains ↑x8) x5.gates;   have x9 : ℕ → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : ℕ) => List.filter (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => (x7 x10).contains (x1 + x9)) (List.drop (x9 + (1 : ℕ)) x5.gates);   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (∀ (x11 : Fin x1) (x12 : x2.Walk x11 x11), x12.IsCycle → (7 : ℕ) ≤ x12.length) → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x16 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x16 → x5.size ≤ x16) → (∀ x17 ∉ x4, (2 : ℕ) ≤ (x8 x17).length ∧ (x8 x17).length ≤ (3 : ℕ) ∧ ((x8 x17).length = (3 : ℕ) → ∀ x20 ∈ x8 x17, x20.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x18 ∉ x4, (x8 x18).length = (2 : ℕ) ∧ ∃ x19 ∈ x8 x18, x19.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ x19 ∉ x4, ∀ (x21 : ℕ) (x22 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x21]? = Option.some x22 → x22.op = PEqualNP.CircuitLowerBounds.GateOp.and → (x7 x22).contains ↑x19 = Bool.true → (∃ x26 ∈ x8 x19, x26.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ (x9 x21).length ≤ (1 : ℕ) ∧ ∀ x26 ∈ x9 x21, x26.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ x20 ∉ x4, ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x6 (Function.update x22 x20 Bool.false)) x21 := by
  intro n G inst A C
  dsimp only
  intro deg girth iso edge fan ev least reads witness nextGate
  let r (v : Fin n) := C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
  let k := (Aᶜ.filter (fun v => (r v).length=3)).card
  have minimal : IsMinimalCircuit n C := ⟨fan,fun D hf same => least D.size
    ⟨D,hf,le_rfl,congrFun (same.trans ev)⟩⟩
  by_cases fits : ∃ T : Finset (Fin n), (∀ a b,G.Adj a b → a∈T ∨ b∈T) ∧ 2*T.card≤Aᶜ.card+2*k
  · obtain ⟨T,cov,paid⟩ := fits
    exact budget n G A C minimal ev deg iso edge (fun v hv => (reads v hv).1) T cov paid
  · have costly (T : Finset (Fin n)) (cov : ∀ a b,G.Adj a b → a∈T ∨ b∈T) : Aᶜ.card+2*k<2*T.card :=
      Nat.lt_of_not_ge (fun low => fits ⟨T,cov,low⟩)
    obtain ⟨T,cov,bound⟩ := geometry n G A deg iso girth
    have expensive := costly T cov
    have few : 6*k<Aᶜ.card := by omega
    apply residual n G A C minimal ev deg iso girth _ _ few costly
    · intro v hv
      obtain ⟨lo,hi,allOr⟩ := reads v hv
      by_cases three : (r v).length=3
      · exact Or.inr ⟨three,allOr three⟩
      · exact Or.inl (show (r v).length=2 from by change 2≤(r v).length at lo;change (r v).length≤3 at hi;omega)
    · obtain ⟨v,hv,_,g,hg,op⟩ := witness
      obtain ⟨mem,raw⟩ := List.mem_filter.mp hg
      obtain ⟨i,hi,atI⟩ := List.mem_iff_getElem.mp mem
      have atI' : C.gates[i]?=some g := by rw [List.getElem?_eq_getElem hi,atI]
      exact ⟨v,hv,⟨g,hg,op⟩,(nextGate v hv i g atI' op raw).1⟩

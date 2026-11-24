import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_1973_371
    (restrictCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A T : Finset (Fin n))
      (f : (Fin n → Bool) → Bool),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) →
      (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
      ∃ v ∉ A, ∃ s, s + 5 ≤ A.card + G.edgeSet.ncard + T.card ∧
        HasCircuitSize n (fun x => f (Function.update x v false)) s)
    (countSlots : ∀ (n : ℕ) (A : Finset (Fin n)) (C : Circuit), FanInTwo C →
      (∀ s, HasCircuitSize n (circuitFun n C) s → C.size ≤ s) →
      (∀ a ∈ A, ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      A.card + (∑ v ∈ Aᶜ, (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) ≤ C.size + 1)
    (shortCircuit : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let f := NestedCover.graphFun G A
      let R := fun v : Fin n => (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ i j, G.Adj i j → i ∉ A) → (∃ i j, G.Adj i j) → FanInTwo C →
      circuitFun n C = f → (∀ s, HasCircuitSize n f s → C.size ≤ s) →
      (∀ v ∉ A, 2 ≤ (R v).length ∧ (R v).length ≤ 3 ∧
        ((R v).length = 3 → ∀ g ∈ R v, g.op = .or)) →
      (∃ v ∉ A, (R v).length = 2) →
      (∀ T : Finset (Fin n), (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
        C.size + 1 < A.card + G.edgeSet.ncard + T.card ∧
        (∑ v ∈ Aᶜ, (R v).length) < G.edgeSet.ncard + T.card) →
      ∃ v ∉ A, ∃ s, s + 4 ≤ C.size ∧ HasCircuitSize n (fun x => f (Function.update x v false)) s) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       (2 : ℕ) ≤ x16.length ∧ x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     (∃ x15 ∉ x3, (List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x15) x5.gates).length = (2 : ℕ)) → ∃ x16 ∉ x3, ∃ (x17 : ℕ), x17 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => x4 (Function.update x18 x16 Bool.false)) x17 := by
  classical
  intro n G A f C degree girth noMarked edge fSpec fan computes minimal readBounds twoReaders
  by_cases affordable : ∃ T : Finset (Fin n),
      (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ A.card + G.edgeSet.ncard + T.card ≤ C.size + 1
  · obtain ⟨T,cover,cost⟩ := affordable
    obtain ⟨v,hv,s,hs,model⟩ := restrictCover n G A T f degree noMarked edge fSpec cover
    exact ⟨v,hv,s,by omega,model⟩
  let graphTarget := PEqualNP.MetaComplexity.NestedCover.graphFun G A
  let readers (v : Fin n) : List Gate := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  have sameTarget : graphTarget = f := by
    funext x
    apply Bool.eq_iff_iff.mpr
    change (decide (∃ a ∈ A, x a = true) || decide (∃ u v, G.Adj u v ∧
      x u = true ∧ x v = true)) = true ↔ f x = true
    rw [fSpec x]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  have computesGraph : circuitFun n C = graphTarget := computes.trans sameTarget.symm
  have leastGraph (s : ℕ) (h : HasCircuitSize n graphTarget s) : C.size ≤ s :=
    minimal s (sameTarget ▸ h)
  have essential (a : Fin n) (ha : a ∈ A) : ∃ x y : Fin n → Bool,
      (∀ j, j ≠ a → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y := by
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i = a)
    refine ⟨z,y,fun i hi => by simp [z,y,hi],?_⟩
    rw [computes]
    have hz : f z ≠ true := by simp [fSpec,z]
    have hy : f y = true := (fSpec y).mpr (Or.inl ⟨a,ha,by simp [y]⟩)
    exact fun eq => hz (eq.trans hy)
  have ls (s : ℕ) (h : HasCircuitSize n (circuitFun n C) s) : C.size ≤ s :=
    minimal s (computes ▸ h)
  have slot : A.card + (∑ v ∈ Aᶜ, (readers v).length) ≤ C.size + 1 :=
    countSlots n A C fan ls essential
  have result : ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧
      HasCircuitSize n (fun x => graphTarget (Function.update x v false)) s :=
    shortCircuit n G A C degree girth noMarked edge fan computesGraph
      leastGraph readBounds twoReaders (by
      intro T cover
      have bad : ¬ A.card + G.edgeSet.ncard + T.card ≤ C.size + 1 :=
        fun h => affordable ⟨T,cover,h⟩
      change C.size + 1 < A.card + G.edgeSet.ncard + T.card ∧
        (∑ v ∈ Aᶜ, (readers v).length) < G.edgeSet.ncard + T.card
      omega)
  rwa [sameTarget] at result

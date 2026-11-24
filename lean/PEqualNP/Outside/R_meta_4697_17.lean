import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.BicliqueBlockCost

-- The circuit tests identify unordered pairs; repeated endpoints test singletons.
theorem PEqualNP.Outside.R_meta_4697_17
  (sparse : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)),
    (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
    (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
    (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
    ∀ s, HasCircuitSize n (graphFun G ∅) s → ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ u v : Fin n,
      let x := List.ofFn fun z : Fin n => decide (z = u ∨ z = v)
      (C.eval x = decide (G.Adj u v)) ∧ (¬ G.Adj u v → ∀ i : Fin C.gates.length,
        (C.gates.get i).op = GateOp.and → (C.wires x).getD (n + i.val) false = false))
  (price : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    (∀ v (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) → (∃ u v, G.Adj u v) →
    Monotone2 C → (∀ u v : Fin n,
      let x := List.ofFn fun z : Fin n => decide (z = u ∨ z = v)
      (C.eval x = decide (G.Adj u v)) ∧ (¬ G.Adj u v → ∀ i : Fin C.gates.length,
        (C.gates.get i).op = GateOp.and → (C.wires x).getD (n + i.val) false = false)) → HasBlockCost G C.size)
  (build : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), HasBlockCost G s → ∃ (B : List (Finset (Fin n))) (m : ℕ) (X Y : Fin m → Finset (Fin n)),
    (∀ (P : List (Finset (Fin n))) (a : Finset (Fin n)) (T : List (Finset (Fin n))),
      B = P ++ a :: T → ∃ b c, a = b ∪ c ∧ (b.card ≤ 1 ∨ b ∈ T) ∧ (c.card ≤ 1 ∨ c ∈ T)) ∧
    (∀ i, ((X i).card ≤ 1 ∨ X i ∈ B) ∧ ((Y i).card ≤ 1 ∨ Y i ∈ B)) ∧
    (∀ x : Fin n → Bool, (∃ i, (∃ u ∈ X i, x u = true) ∧ ∃ v ∈ Y i, x v = true) ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∧ B.length + 2*m ≤ s+1) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : List (Finset (Fin x1))) (x12 : ℕ) (x13 : Fin x12 → Finset (Fin x1)) (x14 : Fin x12 → Finset (Fin x1)), (∀ (x15 : List (Finset (Fin x1))) (x16 : Finset (Fin x1)) (x17 : List (Finset (Fin x1))), x11 = x15 ++ x16 :: x17 → ∃ (x19 : Finset (Fin x1)) (x20 : Finset (Fin x1)), x16 = x19 ∪ x20 ∧ (x19.card ≤ (1 : ℕ) ∨ x19 ∈ x17) ∧ (x20.card ≤ (1 : ℕ) ∨ x20 ∈ x17)) ∧ (∀ (x15 : Fin x12), ((x13 x15).card ≤ (1 : ℕ) ∨ x13 x15 ∈ x11) ∧ ((x14 x15).card ≤ (1 : ℕ) ∨ x14 x15 ∈ x11)) ∧ (∀ (x15 : Fin x1 → Bool), (∃ (x16 : Fin x12), (∃ x17 ∈ x13 x16, x15 x17 = Bool.true) ∧ ∃ x17 ∈ x14 x16, x15 x17 = Bool.true) ↔ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x15 x16 = Bool.true ∧ x15 x17 = Bool.true) ∧ x11.length + (2 : ℕ) * x12 ≤ x9 + (1 : ℕ) := by
  intro n G d A deg girth iso edge s hs
  obtain ⟨C,hm,hsize,ht⟩ := sparse n G A deg girth iso edge s hs
  have hprice := price n G C (fun v w h => (by have := girth v w h; omega)) edge hm ht
  obtain ⟨F,hF,hc⟩ := hprice
  exact build n G s ⟨F,hF,hc.trans hsize⟩

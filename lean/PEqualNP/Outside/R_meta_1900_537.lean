import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.BicliqueBlockCost

-- A dirty AND on a negative singleton, pair or empty input triggers a strictly
-- smaller residual circuit.  A star costs one gate per leaf and one more OR
-- exactly when the residual graph has an edge.
theorem PEqualNP.Outside.R_meta_1900_537
    (pairClean : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), (∃ u v, G.Adj u v) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d →
       ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → Monotone2 C → (∀ (x : Fin n → Bool), C.eval (List.ofFn x) = true ↔ ∃ (u v : Fin n), G.Adj u v ∧ x u = true ∧ x v = true) → ¬ (∃ (i : Fin C.gates.length) (x : Fin n → Bool),
       (C.gates.get i).op = GateOp.and ∧ (∃ a b : Fin n, ∀ k : Fin n, x k = true → k = a ∨ k = b) ∧
       (C.wires (List.ofFn x)).getD (n+i.val) false = true ∧
       ¬ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → HasBlockCost G C.size)
    (peelStar : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit), (∃ u v, G.Adj u v) →
    (∀ a b c d : Fin n, a ≠ c → b ≠ d →
       ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → Monotone2 C → (∀ (x : Fin n → Bool), C.eval (List.ofFn x) = true ↔ ∃ (u v : Fin n), G.Adj u v ∧ x u = true ∧ x v = true) → (∃ (i : Fin C.gates.length) (x : Fin n → Bool),
       (C.gates.get i).op = GateOp.and ∧ (∃ a b : Fin n, ∀ k : Fin n, x k = true → k = a ∨ k = b) ∧
       (C.wires (List.ofFn x)).getD (n+i.val) false = true ∧
       ¬ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    ∃ (a : Fin n) (L : Finset (Fin n)) (H : SimpleGraph (Fin n)) (D : Circuit),
      L.Nonempty ∧ (∀ v ∈ L, G.Adj a v) ∧ (∀ u v, H.Adj u v ↔ G.Adj u v ∧ ¬ ((u=a ∧ v∈L) ∨ (v=a ∧ u∈L))) ∧ Monotone2 D ∧ (∀ (x : Fin n → Bool), D.eval (List.ofFn x) = true ↔ ∃ (u v : Fin n), H.Adj u v ∧ x u = true ∧ x v = true) ∧
      D.size + L.card ≤ C.size ∧ ((∃ u v, H.Adj u v) → D.size + L.card + 1 ≤ C.size))
    (glue : ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (a : Fin n) (L : Finset (Fin n)) (s t : ℕ),
    L.Nonempty → (∀ v ∈ L, G.Adj a v) → (∀ u v, H.Adj u v ↔ G.Adj u v ∧ ¬ ((u=a ∧ v∈L) ∨ (v=a ∧ u∈L))) →
    ((∃ u v, H.Adj u v) → HasBlockCost H s) → s + L.card ≤ t →
    ((∃ u v, H.Adj u v) → s + L.card + 1 ≤ t) → HasBlockCost G t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x3.size := by
  classical
  intro n
  let computes := fun (K : SimpleGraph (Fin n)) (D : Circuit) =>
      (∀ (x : Fin n → Bool), D.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)
  let four := fun (G : SimpleGraph (Fin n)) => (∀ a b c d : Fin n, a ≠ c → b ≠ d →
       ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
  have solve : ∀ k, ∀ (G : SimpleGraph (Fin n)) (C : Circuit), C.size = k →
      (∃ u v, G.Adj u v) → four G → Monotone2 C → computes G C → HasBlockCost G C.size := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro G C hsize he hfour hmono hcomp
      by_cases fault : (∃ (i : Fin C.gates.length) (x : Fin n → Bool),
       (C.gates.get i).op = GateOp.and ∧ (∃ a b : Fin n, ∀ k : Fin n, x k = true → k = a ∨ k = b) ∧
       (C.wires (List.ofFn x)).getD (n+i.val) false = true ∧
       ¬ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
      · obtain ⟨a, L, H, D, hL, hstar, hcut, hD, hcalc, hcost, hplus⟩ :=
          peelStar n G C he hfour hmono hcomp fault
        apply glue n G H a L D.size C.size hL hstar hcut _ hcost hplus
        intro hH
        have pos := Finset.card_pos.mpr hL
        apply ih D.size (by omega) H D rfl hH _ hD hcalc
        intro u v w z huw hvz
        rintro ⟨huv, hvw, hwz, hzu⟩
        exact hfour u v w z huw hvz ⟨((hcut _ _).1 huv).1, ((hcut _ _).1 hvw).1,
          ((hcut _ _).1 hwz).1, ((hcut _ _).1 hzu).1⟩
      · exact pairClean n G C he hfour hmono hcomp fault
  intro G C he hfour hmono hcomp
  apply solve C.size G C rfl he _ hmono hcomp
  intro a b c d hac hbd
  rintro ⟨hab, hbc, hcd, hda⟩
  exact hfour a b c d hab.ne hac hda.ne.symm hbc.ne hbd hcd.ne hab hbc hcd hda

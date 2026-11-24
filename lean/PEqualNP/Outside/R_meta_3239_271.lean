import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_3239_271
    (h1 : ∀ C : PEqualNP.MetaComplexity.BinaryCircuit, C.size ≤ 13 →
      (∀ g ∈ C.gates, ∃ c d : Bool, g.op = fun x y => x == c && y == d) →
      (∀ g : PEqualNP.MetaComplexity.BinaryGate, C.gates[0]? = some g →
        (∃ d : Bool, g.op = fun x y => x == false && y == d) ∧
        [g.left, g.right] ≤
          [[1,0,5,8,6,2,4,7,3].getD g.left g.left, [1,0,5,8,6,2,4,7,3].getD g.right g.right]) →
      ∃ (k : Fin 242) (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24),
        (([18446145939384303615, 17582224571832, 53921301135360, 431189485725696] : List ℕ).getD (k.val / 64) 0).testBit (k.val % 64) = true ∧ gs.length ≤ 12 ∧
        ∀ r : ℕ, r < 512 → let v := (List.ofFn (fun j : Fin 9 => r.testBit j.val)) ++ [r.testBit 0 || r.testBit 1, false]
          C.eval v = (PEqualNP.MetaComplexity.BinaryCircuit.mk (gs.map (fun e => ⟨fun x y => x == e.2.2.1 && y == e.2.2.2, e.1.val, e.2.1.val⟩)) o.val).eval (v ++ [(!v.getD (k.val / 22) false) && (v.getD (k.val % 22 / 2) false == (k.val % 2 == 1))]))
    (h2 : ∀ (k : Fin 242) (gs : List (Fin 24 × Fin 24 × Bool × Bool)) (o : Fin 24) (b : Bool),
      (([18446145939384303615, 17582224571832, 53921301135360, 431189485725696] : List ℕ).getD (k.val / 64) 0).testBit (k.val % 64) = true → gs.length ≤ 12 →
      ¬ ∀ r : ℕ, r < 512 → let v := (List.ofFn (fun j : Fin 9 => r.testBit j.val)) ++ [r.testBit 0 || r.testBit 1, false]
        ((PEqualNP.MetaComplexity.BinaryCircuit.mk (gs.map (fun e => ⟨fun x y => x == e.2.2.1 && y == e.2.2.2, e.1.val, e.2.1.val⟩)) o.val).eval (v ++ [(!v.getD (k.val / 22) false) && (v.getD (k.val % 22 / 2) false == (k.val % 2 == 1))]) != b) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r / 64) 0).testBit (r % 64)) :
    ∀ (x1 : PEqualNP.MetaComplexity.BinaryCircuit) (x2 : Bool), (∀ x3 ∈ x1.gates, ∃ (x5 : Bool) (x6 : Bool), x3.op = fun (x7 x8 : Bool) => x7 == x5 && x8 == x6) → (∀ (x4 : PEqualNP.MetaComplexity.BinaryGate), x1.gates[(0 : ℕ)]? = Option.some x4 → (∃ (x6 : Bool), x4.op = fun (x7 x8 : Bool) => x7 == Bool.false && x8 == x6) ∧ [x4.left, x4.right] ≤ [[(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.left x4.left, [(1 : ℕ), (0 : ℕ), (5 : ℕ), (8 : ℕ), (6 : ℕ), (2 : ℕ), (4 : ℕ), (7 : ℕ), (3 : ℕ)].getD x4.right x4.right]) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x1.eval (List.ofFn x5 ++ [x5 (0 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)), Bool.false]) != x2) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → (14 : ℕ) ≤ x1.size := by
  intro C b ops first correct
  by_contra! small
  obtain ⟨k, gs, o, hk, hgs, sim⟩ := h1 C (by omega) ops first
  apply h2 k gs o b hk hgs
  intro r hr
  let x : Fin 9 → Bool := fun j => r.testBit j.val
  change _ = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r / 64) 0).testBit (r % 64)
  rw [← sim r hr]
  have table : ∀ t : Fin 512, ((t.val.testBit 0 && t.val.testBit 1) || (t.val.testBit 1 && t.val.testBit 2) || (t.val.testBit 2 && t.val.testBit 3) || (t.val.testBit 3 && t.val.testBit 4) || (t.val.testBit 4 && t.val.testBit 0) || (t.val.testBit 0 && t.val.testBit 5) || (t.val.testBit 1 && t.val.testBit 6) || (t.val.testBit 2 && t.val.testBit 7) || (t.val.testBit 3 && t.val.testBit 8) || (t.val.testBit 5 && t.val.testBit 7) || (t.val.testBit 6 && t.val.testBit 8) || (t.val.testBit 8 && t.val.testBit 5)) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (t.val / 64) 0).testBit (t.val % 64) := by decide
  exact (correct x).trans (table ⟨r, hr⟩)

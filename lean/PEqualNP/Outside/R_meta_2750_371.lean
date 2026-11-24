import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2750_371
    (peel : ∀ C : Circuit, FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 4)) →
      C.gates[1]?.map Gate.op = some GateOp.not →
      C.gates[2]?.map Gate.op = some GateOp.or →
      ∃ (i : Fin 11) (j k : Fin 12) (D : Circuit),
        FanInTwo D ∧ D.size + 3 = C.size ∧ ∀ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [x 0 || x 4]
      let v := w ++ [!w.getD i.val false]
      D.eval (v ++ [v.getD j.val false || v.getD k.val false]) = circuitFun 9 C x)
    (tailBound : ∀ (i : Fin 11) (j k : Fin 12) (D : Circuit), FanInTwo D →
      (∀ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [x 0 || x 4]
      let v := w ++ [!w.getD i.val false]
      D.eval (v ++ [v.getD j.val false || v.getD k.val false]) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → 13 ≤ D.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → Option.map (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) => x5.op) x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.not → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x1.gates[(2 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (16 : ℕ) ≤ x1.size := by
  intro C hfan hfirst hfun hnot hor
  obtain ⟨i, j, k, D, hD, hsize, heval⟩ := peel C hfan hfirst hnot hor
  have hbound := tailBound i j k D hD (fun x => (heval x).trans (congrFun hfun x))
  omega

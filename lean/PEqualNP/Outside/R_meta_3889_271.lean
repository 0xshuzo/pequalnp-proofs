import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3889_271
    (compile : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (k : Fin 14),
      PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), getElem? C.gates j = some g →
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = k.val)) →
      ∃ (gs : List (Bool × Fin 25 × Fin 25)) (o : Fin 25), gs.length ≤ 13 ∧
        ∀ (x : Fin 9 → Bool) (h b : Bool), (h || b) = true →
          (PEqualNP.CircuitLowerBounds.Circuit.mk ((gs.zipIdx 0).map (fun t => PEqualNP.CircuitLowerBounds.Gate.mk (if Prod.snd t = k.val then PEqualNP.CircuitLowerBounds.GateOp.not else cond (Prod.fst (Prod.fst t)) PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and) [Fin.val (Prod.fst (Prod.snd (Prod.fst t))), Fin.val (Prod.snd (Prod.snd (Prod.fst t)))])) o.val).eval (List.ofFn x ++ [h,b]) = C.eval (List.ofFn x ++ [h,b]))
    (budget : ∀ (i : Fin 11) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (i = 9 ∨ i = 10) → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
      (∀ r : ℕ, r < 512 →
        let w := List.ofFn (fun a : Fin 9 => r.testBit a.val) ++ [r.testBit 0 || r.testBit 2]
        C.eval (w ++ [!w.getD i.val false]) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r / 64) 0).testBit (r % 64)) →
      i = 9 ∧ ∃ k : Fin 14, ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        getElem? C.gates j = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = k.val))
    (finite : ∀ (k : Fin 14) (gs : List (Bool × Fin 25 × Fin 25)) (o : Fin 25), gs.length ≤ 13 →
      ¬ ∀ r : ℕ, r < 512 →
        let h := r.testBit 0 || r.testBit 2
        (PEqualNP.CircuitLowerBounds.Circuit.mk ((gs.zipIdx 0).map (fun t => PEqualNP.CircuitLowerBounds.Gate.mk (if Prod.snd t = k.val then PEqualNP.CircuitLowerBounds.GateOp.not else cond (Prod.fst (Prod.fst t)) PEqualNP.CircuitLowerBounds.GateOp.or PEqualNP.CircuitLowerBounds.GateOp.and) [Fin.val (Prod.fst (Prod.snd (Prod.fst t))), Fin.val (Prod.snd (Prod.snd (Prod.fst t)))])) o.val).eval (List.ofFn (fun a : Fin 9 => r.testBit a.val) ++ [h,!h]) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r / 64) 0).testBit (r % 64)) :
    ∀ (x1 : Fin (11 : ℕ)),   x1 = (9 : Fin (11 : ℕ)) ∨ x1 = (10 : Fin (11 : ℕ)) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [!x7.getD (↑x1) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x8 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x6 x8.1 && x6 x8.2 := by
  intro i hi C fan small
  by_contra! correct
  have table : ∀ r : Fin 512, ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => r.val.testBit e.1.val && r.val.testBit e.2.val) =
      (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r.val / 64) 0).testBit (r.val % 64) := by decide
  have packed : ∀ r : ℕ, r < 512 →
      let w := List.ofFn (fun a : Fin 9 => r.testBit a.val) ++ [r.testBit 0 || r.testBit 2]
      C.eval (w ++ [!w.getD i.val false]) = (([18440827511444797640, 18441957826578283724, 18446744073709222136, 18446744073709485308, 18446744073708175304, 18446744073709551615, 18446744073709223928, 18446744073709551615] : List ℕ).getD (r / 64) 0).testBit (r % 64) := by
    intro r hr
    refine Eq.trans ?_ (table ⟨r,hr⟩)
    exact Classical.byContradiction (correct (fun a => r.testBit a.val))
  obtain ⟨rfl,k,hk⟩ := budget i C hi fan small packed
  obtain ⟨gs,o,hlen,sim⟩ := compile C k fan small hk
  apply finite k gs o hlen
  intro r hr
  let x : Fin 9 → Bool := fun a => r.testBit a.val
  let h := r.testBit 0 || r.testBit 2
  have last : (List.ofFn x ++ [h]).getD 9 false = h := by
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  have agrees := packed r hr
  change C.eval ((List.ofFn x ++ [h]) ++ [!(List.ofFn x ++ [h]).getD 9 false]) = _ at agrees
  rw [last] at agrees
  have hsim := sim x h (!h) (by cases h <;> rfl)
  exact hsim.trans (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using agrees)

import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_3861_271
    (eliminate : ∀ (j : Fin 9) (C : Circuit), (j = 1 ∨ j = 4) → FanInTwo C → C.size ≤ 13 →
      (∀ (r : ℕ), r < 512 → C.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [!r.testBit 0, r.testBit 0 || r.testBit j.val]) =
        ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun m => (r &&& m) == m)) →
      (∃ D : Circuit, Monotone2 D ∧ D.size ≤ 14 ∧ (∀ (r : ℕ), r < 512 → D.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [false]) = ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun m => (r &&& m) == m))) ∨
      ∃ (B : BinaryCircuit) (b : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧ B.size ≤ 11 ∧ (∀ (r : ℕ), r < 256 → (B.eval (List.ofFn (fun i : Fin 8 => r.testBit i.val)) != b) = ([3,6,12,33,66,132,80,160,144] : List ℕ).any (fun m => (r &&& m) == m)))
    (restrict : ∀ (B : BinaryCircuit) (b : Bool), (∀ g ∈ B.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) → B.size ≤ 11 → (∀ (r : ℕ), r < 256 → (B.eval (List.ofFn (fun i : Fin 8 => r.testBit i.val)) != b) = ([3,6,12,33,66,132,80,160,144] : List ℕ).any (fun m => (r &&& m) == m)) →
      ∃ (gs : List (Fin 18 × Fin 18 × Bool × Bool)) (o : Fin 18) (c : Bool), gs.length ≤ 10 ∧ (∀ (r : ℕ), r < 128 → ((BinaryCircuit.mk (gs.map (fun g => BinaryGate.mk (fun x y => x == g.2.2.1 && y == g.2.2.2) g.1.val g.2.1.val)) o.val).eval (List.ofFn (fun i : Fin 7 => r.testBit i.val)) != c) = ([5,6,9,24,18,33,96,66] : List ℕ).any (fun m => (r &&& m) == m)))
    (positive : ∀ D : Circuit, Monotone2 D → (∀ (r : ℕ), r < 512 → D.eval (List.ofFn (fun i : Fin 9 => r.testBit i.val) ++ [false]) = ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun m => (r &&& m) == m)) → 15 ≤ D.size)
    (theta : ∀ (gs : List (Fin 18 × Fin 18 × Bool × Bool)) (o : Fin 18) (c : Bool), gs.length ≤ 10 → ¬ (∀ (r : ℕ), r < 128 → ((BinaryCircuit.mk (gs.map (fun g => BinaryGate.mk (fun x y => x == g.2.2.1 && y == g.2.2.2) g.1.val g.2.1.val)) o.val).eval (List.ofFn (fun i : Fin 7 => r.testBit i.val)) != c) = ([5,6,9,24,18,33,96,66] : List ℕ).any (fun m => (r &&& m) == m)))
    : ∀ (x1 : List ℕ),   x1 = [(0 : ℕ), (1 : ℕ)] ∨ x1 = [(0 : ℕ), (4 : ℕ)] →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [!x6 (0 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro p hp C fan sz
  obtain ⟨j,hj,rfl⟩ : ∃ j : Fin 9, (j = 1 ∨ j = 4) ∧ p = [0,j.val] := by
    rcases hp with rfl | rfl
    · exact ⟨1,Or.inl rfl,rfl⟩
    · exact ⟨4,Or.inr rfl,rfl⟩
  apply Classical.byContradiction
  intro no
  let x := fun (r : Fin 512) (i : Fin 9) => r.val.testBit i.val
  let w := fun r => List.ofFn (x r) ++ [!(x r 0)]
  have pins : ∀ (r : Fin 512) (k : Fin 9),
      GateOp.or.eval (([0,k.val] : List ℕ).map (fun i => (w r).getD i false)) =
        (x r 0 || x r k) := by decide
  let edge := fun y : Fin 9 → Bool =>
    y 0 && y 1 || y 1 && y 2 || y 2 && y 3 || y 3 && y 4 || y 4 && y 0 ||
    y 0 && y 5 || y 1 && y 6 || y 2 && y 7 || y 3 && y 8 || y 5 && y 7 || y 6 && y 8 || y 8 && y 5
  have table : ∀ r : Fin 512, edge (x r) = ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun m => (r.val &&& m) == m) := by decide
  have correct (r : Fin 512) :
      C.eval (List.ofFn (fun i : Fin 9 => r.val.testBit i.val) ++ [!r.val.testBit 0, r.val.testBit 0 || r.val.testBit j.val]) =
        ([3,6,12,24,17,33,66,132,264,160,320,288] : List ℕ).any (fun m => (r.val &&& m) == m) := by
    have h : C.eval (w r ++ [GateOp.or.eval (([0,j.val] : List ℕ).map (fun i => (w r).getD i false))]) = edge (x r) :=
      Classical.byContradiction (fun neq => no ⟨x r,neq⟩)
    rw [pins] at h
    refine Eq.trans ?_ (table r)
    simpa only [w,x,Fin.val_zero,List.append_assoc,List.cons_append,List.nil_append] using h
  rcases eliminate j C hj fan sz (fun r hr => correct ⟨r,hr⟩) with ⟨D,hm,hs,he⟩ | ⟨B,b,hb,hs,he⟩
  · have bound := positive D hm he
    omega
  · obtain ⟨gs,o,c,hlen,hrows⟩ := restrict B b hb hs he
    exact theta gs o c hlen hrows

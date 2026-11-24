import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4817_633
    (project : ∀ (m : ℕ), 0 < m → ∀ (l : List ℕ) (C : Circuit), FanInTwo C →
    (∃ x y : Fin m → Bool,
      C.eval (l.map fun i => ((List.ofFn x).getD i false || (i == m+1))) ≠
      C.eval (l.map fun i => ((List.ofFn y).getD i false || (i == m+1)))) →
    ∃ D : Circuit, FanInTwo D ∧
      D.size + C.gates.countP (fun g =>
        (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
          fun i => decide (m ≤ l.getD i 0)) ≤ C.size ∧
      ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (l.map fun i => ((List.ofFn x).getD i false || (i == m+1))))
    (minor : ∀ p ∈ ([0,2,3,6,46] : List ℕ), ∀ D : Circuit,
    FanInTwo D → (∀ y : Fin 9 → Bool,
      D.eval (List.ofFn fun i : Fin 10 => if h : i.val < 9 then y ⟨i.val,h⟩
        else y (Fin.ofNat 9 (p/10)) && y (Fin.ofNat 9 (p % 10))) =
        (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10))) y) → 15 ≤ D.size)
    (twoReaders : ∀ (C : Circuit) (r : Fin 12), FanInTwo C → C.size ≤ 17 →
    (let v := if r.val < 10 then r.val else 0
     C.gates.countP (fun g => (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any
        (fun i => i == v || i == 11 || (i == 10 && (v == 0 || v == 2)))) ≤ 2) →
    ∃ x : Fin 10 → Bool, let z := List.ofFn x ++ [x 0 && x 2]
      C.eval (z ++ [!z.getD r.val false]) ≠ (fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10))) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (12 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (17 : ℕ) →       ∃ (x5 : Fin (10 : ℕ) → Bool),         have x6 : List Bool := List.ofFn x5 ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))];         x1.eval (x6 ++ [!x6.getD (↑x2) Bool.false]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x5 := by
  intro C r hC size
  let P := (fun x : Fin 10 → Bool => ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any fun e => x (Fin.ofNat 10 (e/10)) && x (Fin.ofNat 10 (e % 10)))
  let Q := (fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e => x (Fin.ofNat 9 (e/10)) && x (Fin.ofNat 9 (e % 10)))
  let v := fun s : Fin 12 => if s.val < 10 then s.val else 0
  let code := fun (s : Fin 12) (i : ℕ) =>
    (([[9,4,0,1,6,7,3,5,2,8],[4,9,6,1,0,3,7,8,2,5],[0,4,9,6,1,5,3,7,8,2],[0,1,6,9,4,5,2,8,7,3],[6,1,0,4,9,8,2,5,3,7],[6,1,0,5,8,9,2,4,7,3],[0,4,3,2,1,5,9,8,7,6],[0,1,6,8,5,4,2,9,3,7],[0,1,2,7,5,4,6,3,9,8],[0,1,2,3,4,5,6,7,8,9]] : List (List ℕ)).getD (v s) []).getD i 0
  let orbit := fun s : Fin 12 => ([0,46,0,6,6,6,3,6,2,2] : List ℕ).getD (v s) 0
  let expand := fun (s : Fin 12) (y : Fin 9 → Bool) (i : Fin 10) =>
    if h : code s i.val < 9 then y ⟨code s i.val,h⟩ else false
  let lift := fun (s : Fin 12) (y : Fin 9 → Bool) (i : Fin 10) =>
    if h : i.val < 9 then y ⟨i.val,h⟩
    else y (Fin.ofNat 9 (orbit s / 10)) && y (Fin.ofNat 9 (orbit s % 10))
  let pins := fun s : Fin 12 =>
    (List.range 10).map (fun i => if i = v s then 10 else code s i) ++
      [if v s = 0 ∨ v s = 2 then 10 else 9,11]
  let marked := fun (s : Fin 12) (i : ℕ) =>
    i == v s || i == 11 || (i == 10 && (v s == 0 || v s == 2))
  have ore : ∀ s, orbit s ∈ ([0,2,3,6,46] : List ℕ) := by
    dsimp only [orbit,v]
    decide +kernel
  have finiteMarks : ∀ s j : Fin 12, decide (10 ≤ (pins s).getD j.val 0) = marked s j.val := by
    dsimp only [pins,code,v,marked]
    decide +kernel
  have allMarks (i : ℕ) : decide (10 ≤ (pins r).getD i 0) = marked r i := by
    by_cases hi : i < 12
    · exact finiteMarks r ⟨i,hi⟩
    · have hv : v r < 10 := by dsimp [v]; split <;> omega
      have he : i ≠ v r := by omega
      have h10 : i ≠ 10 := by omega
      have h11 : i ≠ 11 := by omega
      rw [List.getD_eq_default _ _ (by simp [pins]; omega)]
      simp [marked,he,h10,h11]
  let row := fun (k : Fin 512) (i : Fin 9) => k.val.testBit i.val
  let pack := fun (y : Fin 9 → Bool) =>
    (BitVec.ofBoolListLE (List.ofFn y)).toFin.cast (show 2 ^ (List.ofFn y).length = 512 by simp)
  have recover (y : Fin 9 → Bool) : row (pack y) = y := by
    funext i
    change (BitVec.ofBoolListLE (List.ofFn y)).getLsbD i.val = _
    simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    simp [i.isLt]
  let good := fun (s : Fin 12) (y : Fin 9 → Bool) =>
    ((pins s).map (fun j => (List.ofFn (lift s y)).getD j false || (j == 11)) =
      (let z := List.ofFn (expand s y) ++ [expand s y 0 && expand s y 2]
       z ++ [!z.getD s.val false])) ∧ P (expand s y) = Q y
  have rows (s : Fin 12) : ∀ k : Fin 512, good s (row k) := by
    fin_cases s <;> dsimp only [good,P,Q,pins,expand,lift,orbit,code,v,row] <;> decide +kernel
  have geometry (s : Fin 12) (y : Fin 9 → Bool) : good s y := by
    have h := rows s (pack y)
    rwa [recover] at h
  have samePins (s : Fin 12) (y : Fin 9 → Bool) := (geometry s y).1
  have sameTarget (s : Fin 12) (y : Fin 9 → Bool) := (geometry s y).2
  by_contra noMismatch
  push_neg at noMismatch
  have correct (x : Fin 10 → Bool) :
      (let z := List.ofFn x ++ [x 0 && x 2]
       C.eval (z ++ [!z.getD r.val false])) = P x := by
    have posa1 : Fin.ofNat 10 (1 / 10) = (0 : Fin 10) := by decide
    have posb1 : Fin.ofNat 10 (1 % 10) = (1 : Fin 10) := by decide
    have posa12 : Fin.ofNat 10 (12 / 10) = (1 : Fin 10) := by decide
    have posb12 : Fin.ofNat 10 (12 % 10) = (2 : Fin 10) := by decide
    have posa23 : Fin.ofNat 10 (23 / 10) = (2 : Fin 10) := by decide
    have posb23 : Fin.ofNat 10 (23 % 10) = (3 : Fin 10) := by decide
    have posa34 : Fin.ofNat 10 (34 / 10) = (3 : Fin 10) := by decide
    have posb34 : Fin.ofNat 10 (34 % 10) = (4 : Fin 10) := by decide
    have posa40 : Fin.ofNat 10 (40 / 10) = (4 : Fin 10) := by decide
    have posb40 : Fin.ofNat 10 (40 % 10) = (0 : Fin 10) := by decide
    have posa5 : Fin.ofNat 10 (5 / 10) = (0 : Fin 10) := by decide
    have posb5 : Fin.ofNat 10 (5 % 10) = (5 : Fin 10) := by decide
    have posa16 : Fin.ofNat 10 (16 / 10) = (1 : Fin 10) := by decide
    have posb16 : Fin.ofNat 10 (16 % 10) = (6 : Fin 10) := by decide
    have posa27 : Fin.ofNat 10 (27 / 10) = (2 : Fin 10) := by decide
    have posb27 : Fin.ofNat 10 (27 % 10) = (7 : Fin 10) := by decide
    have posa38 : Fin.ofNat 10 (38 / 10) = (3 : Fin 10) := by decide
    have posb38 : Fin.ofNat 10 (38 % 10) = (8 : Fin 10) := by decide
    have posa49 : Fin.ofNat 10 (49 / 10) = (4 : Fin 10) := by decide
    have posb49 : Fin.ofNat 10 (49 % 10) = (9 : Fin 10) := by decide
    have posa57 : Fin.ofNat 10 (57 / 10) = (5 : Fin 10) := by decide
    have posb57 : Fin.ofNat 10 (57 % 10) = (7 : Fin 10) := by decide
    have posa79 : Fin.ofNat 10 (79 / 10) = (7 : Fin 10) := by decide
    have posb79 : Fin.ofNat 10 (79 % 10) = (9 : Fin 10) := by decide
    have posa96 : Fin.ofNat 10 (96 / 10) = (9 : Fin 10) := by decide
    have posb96 : Fin.ofNat 10 (96 % 10) = (6 : Fin 10) := by decide
    have posa68 : Fin.ofNat 10 (68 / 10) = (6 : Fin 10) := by decide
    have posb68 : Fin.ofNat 10 (68 % 10) = (8 : Fin 10) := by decide
    have posa85 : Fin.ofNat 10 (85 / 10) = (8 : Fin 10) := by decide
    have posb85 : Fin.ofNat 10 (85 % 10) = (5 : Fin 10) := by decide
    simpa only [P,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc,posa1,posb1,posa12,posb12,posa23,posb23,posa34,posb34,posa40,posb40,posa5,posb5,posa16,posb16,posa27,posb27,posa38,posb38,posa49,posb49,posa57,posb57,posa79,posb79,posa96,posb96,posa68,posb68,posa85,posb85] using Classical.byContradiction (noMismatch x)
  have eq (y : Fin 9 → Bool) :
      C.eval ((pins r).map fun j => (List.ofFn (lift r y)).getD j false || (j == 11)) = Q y := by
    rw [samePins, correct, sameTarget]
  let u : Fin 9 → Bool := fun _ => false
  let t : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
  have diff : Q u ≠ Q t := by dsimp only [Q,u,t]; decide
  have nc : ∃ x y : Fin 10 → Bool,
      C.eval ((pins r).map fun i => (List.ofFn x).getD i false || (i == 11)) ≠
      C.eval ((pins r).map fun i => (List.ofFn y).getD i false || (i == 11)) :=
    ⟨lift r u,lift r t,by rw [eq,eq]; exact diff⟩
  obtain ⟨D,hD,saved,eval⟩ := project 10 (by decide) (pins r) C hC nc
  have computes (y : Fin 9 → Bool) : D.eval (List.ofFn (lift r y)) = Q y :=
    (eval (lift r y)).trans (eq y)
  have bound := minor (orbit r) (ore r) D hD computes
  have markEq : (fun i => decide (10 ≤ (pins r).getD i 0)) = marked r := funext allMarks
  simp only [markEq] at saved
  obtain ⟨x,bad⟩ := twoReaders C r hC size (by change C.gates.countP (fun g =>
      (if g.op.eval [false,false] then g.inputs.take 1 else g.inputs).any (marked r)) ≤ 2; omega)
  exact bad (correct x)

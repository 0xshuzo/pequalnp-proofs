import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5208_near
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
attribute [local instance] gateOpDecEq
set_option maxHeartbeats 10000000
set_option maxRecDepth 32768

def C : Circuit := ⟨[
  ⟨.or, [21, 13]⟩,
  ⟨.or, [15, 23]⟩,
  ⟨.or, [17, 24]⟩,
  ⟨.or, [20, 13]⟩,
  ⟨.or, [19, 15]⟩,
  ⟨.or, [16, 24]⟩,
  ⟨.or, [22, 14]⟩,
  ⟨.or, [21, 24]⟩,
  ⟨.or, [30, 25]⟩,
  ⟨.or, [27, 33]⟩,
  ⟨.or, [21, 16]⟩,
  ⟨.or, [14, 36]⟩,
  ⟨.or, [22, 25]⟩,
  ⟨.or, [25, 23]⟩,
  ⟨.or, [37, 17]⟩,
  ⟨.or, [25, 18]⟩,
  ⟨.or, [14, 34]⟩,
  ⟨.or, [26, 19]⟩,
  ⟨.and, [11, 35]⟩,
  ⟨.and, [2, 42]⟩,
  ⟨.or, [23, 32]⟩,
  ⟨.or, [17, 22]⟩,
  ⟨.or, [20, 19]⟩,
  ⟨.and, [4, 40]⟩,
  ⟨.or, [16, 15]⟩,
  ⟨.or, [18, 16]⟩,
  ⟨.or, [24, 14]⟩,
  ⟨.or, [52, 18]⟩,
  ⟨.or, [15, 18]⟩,
  ⟨.or, [23, 51]⟩,
  ⟨.or, [43, 22]⟩,
  ⟨.and, [13, 56]⟩,
  ⟨.or, [29, 50]⟩,
  ⟨.or, [28, 48]⟩,
  ⟨.and, [3, 58]⟩,
  ⟨.and, [0, 57]⟩,
  ⟨.or, [61, 17]⟩,
  ⟨.or, [54, 47]⟩,
  ⟨.or, [19, 55]⟩,
  ⟨.and, [9, 56]⟩,
  ⟨.and, [7, 59]⟩,
  ⟨.or, [21, 41]⟩,
  ⟨.or, [39, 62]⟩,
  ⟨.and, [6, 64]⟩,
  ⟨.and, [0, 68]⟩,
  ⟨.and, [5, 63]⟩,
  ⟨.or, [67, 20]⟩,
  ⟨.or, [13, 53]⟩,
  ⟨.or, [38, 31]⟩,
  ⟨.or, [70, 49]⟩,
  ⟨.and, [12, 74]⟩,
  ⟨.or, [69, 75]⟩,
  ⟨.or, [46, 20]⟩,
  ⟨.or, [71, 66]⟩,
  ⟨.and, [8, 72]⟩,
  ⟨.or, [65, 77]⟩,
  ⟨.and, [1, 73]⟩,
  ⟨.and, [10, 78]⟩,
  ⟨.or, [83, 60]⟩,
  ⟨.or, [45, 84]⟩,
  ⟨.or, [44, 85]⟩,
  ⟨.or, [76, 82]⟩,
  ⟨.or, [86, 87]⟩,
  ⟨.or, [80, 88]⟩,
  ⟨.or, [79, 89]⟩,
  ⟨.or, [81, 90]⟩], 91⟩

def edges : List (Fin 13 × Fin 13) := [
  (0,0), (0,4), (0,10), (0,12),
  (1,0), (1,1), (1,5), (1,11),
  (2,1), (2,2), (2,6), (2,12),
  (3,0), (3,2), (3,3), (3,7),
  (4,1), (4,3), (4,4), (4,8),
  (5,2), (5,4), (5,5), (5,9),
  (6,3), (6,5), (6,6), (6,10),
  (7,4), (7,6), (7,7), (7,11),
  (8,5), (8,7), (8,8), (8,12),
  (9,0), (9,6), (9,8), (9,9),
  (10,1), (10,7), (10,9), (10,10),
  (11,2), (11,8), (11,10), (11,11),
  (12,3), (12,9), (12,11), (12,12)]

theorem legal (i : Nat) (g : Gate) (h : C.gates[i]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+i ∧ b < 26+i := by
  have hi : i < C.gates.length := by
    by_contra! bad
    rw [List.getElem?_eq_none bad] at h
    contradiction
  have he : g = C.gates[i] := by simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using h.symm
  subst g
  have tab : ∀ j : Fin C.gates.length,
      let g := C.gates[j.val]
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 26+j.val ∧ b < 26+j.val := by decide
  obtain ⟨op, ins, ne, ha, hb⟩ := tab ⟨i,hi⟩
  exact ⟨op, _, _, ins, ne, ha, hb⟩

theorem computes (x : Fin 26 → Bool) : C.eval (List.ofFn x) = true ↔
    ∃ p l : Fin 13, p - l ∈ ({0,1,3,9} : Finset (Fin 13)) ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
  have memEdge : ∀ p l : Fin 13, (p,l) ∈ edges ↔ p-l ∈ ({0,1,3,9} : Finset (Fin 13)) := by decide
  have he : C.eval (List.ofFn x) =
      edges.any (fun e => x (Fin.castAdd 13 e.1) && x (Fin.natAdd 13 e.2)) := by
    change C.eval [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15, x 16, x 17, x 18, x 19, x 20, x 21, x 22, x 23, x 24, x 25] = _
    simp [C, edges, Circuit.eval, Circuit.wires, GateOp.eval] <;> bv_decide
  rw [he,List.any_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,m,h⟩
    exact ⟨p,l,(memEdge p l).mp m,by simpa using h⟩
  · rintro ⟨p,l,m,h⟩
    exact ⟨(p,l),(memEdge p l).mpr m,by simpa using h⟩

theorem upper66 : ¬ (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;     x1.size ≤ (66 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x4 x10 x11 ∧ x9 x10 x6 ∧ x9 x11 x7) := by
  intro no
  apply no
  refine ⟨C, by decide, legal, computes, ?_, 31, 44, by decide, ?_, ?_⟩
  · refine ⟨31, by decide, by decide, pairInput 13 13, by decide, by decide⟩
  · exact ⟨by decide, Or.inr (by decide), by decide, by decide⟩
  · exact ⟨by decide, Or.inr (by decide), by decide, by decide⟩

end PEqualNP.Outside.L_meta_5208_near

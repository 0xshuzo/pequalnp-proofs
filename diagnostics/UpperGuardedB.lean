import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18330
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection

def C : Circuit := ⟨[⟨.or,[0,1]⟩,
⟨.or,[14,3]⟩,
⟨.and,[7,15]⟩,
⟨.or,[1,2]⟩,
⟨.or,[17,4]⟩,
⟨.and,[8,18]⟩,
⟨.or,[2,3]⟩,
⟨.or,[20,5]⟩,
⟨.and,[9,21]⟩,
⟨.or,[3,4]⟩,
⟨.or,[23,6]⟩,
⟨.and,[10,24]⟩,
⟨.or,[4,5]⟩,
⟨.or,[26,0]⟩,
⟨.and,[11,27]⟩,
⟨.or,[5,6]⟩,
⟨.or,[29,1]⟩,
⟨.and,[12,30]⟩,
⟨.or,[6,0]⟩,
⟨.or,[32,2]⟩,
⟨.and,[13,33]⟩,
⟨.or,[16,19]⟩,
⟨.or,[35,22]⟩,
⟨.or,[36,25]⟩,
⟨.or,[37,28]⟩,
⟨.or,[38,31]⟩,
⟨.or,[39,34]⟩],40⟩
theorem gateTable : ∀ j : Fin C.gates.length,
      let g := C.gates[j.val]'(j.isLt)
      let a := g.inputs.getD 0 0
      let b := g.inputs.getD 1 0
      (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+j.val ∧ b < 14+j.val := by
  letI := gateOpDecEq
  decide +kernel

theorem legal (i : Nat) (g : Gate) (h : C.gates[i]? = some g) :
    (g.op = .and ∨ g.op = .or) ∧ ∃ a b : Nat, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14+i ∧ b < 14+i := by
  have hi : i < C.gates.length := by
    by_contra! bad
    rw [List.getElem?_eq_none bad] at h
    contradiction
  have he : g = C.gates[i] := by simpa only [List.getElem?_eq_getElem hi, Option.some.injEq] using h.symm
  subst g
  obtain ⟨op, ins, ne, ha, hb⟩ := gateTable ⟨i,hi⟩
  exact ⟨op, _, _, ins, ne, ha, hb⟩


abbrev I := Fin 7
def bad (x : I → Bool) (i : Fin (7+7)) : Bool := Fin.addCases (motive := fun _ => Bool) x (fun l : I =>
  decide (∀ p : I, x p = true → ¬(p=l ∨ p=l+1 ∨ p=l+3))) i
set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem badRows : ∀ a b c d e f g : Bool,
  C.eval (List.ofFn (bad ![a,b,c,d,e,f,g])) = false := by decide +kernel
theorem allRows (x : I → Bool) : C.eval (List.ofFn (bad x)) = false := by
  have hx : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6] := by
    funext i
    fin_cases i <;> rfl
  calc C.eval (List.ofFn (bad x)) = C.eval (List.ofFn (bad ![x 0,x 1,x 2,x 3,x 4,x 5,x 6])) := congrArg (fun y => C.eval (List.ofFn (bad y))) hx
       _ = false := badRows (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6)
end PEqualNP.Outside.L_meta_18330

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
theorem PEqualNP.Outside.L_meta_18330 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧ ∀ (x2 : Fin (7 : ℕ) → Bool), x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬(x5 = x4 ∨ x5 = x4 + (1 : Fin (7 : ℕ)) ∨ x5 = x4 + (3 : Fin (7 : ℕ))))) x3) = Bool.false := by
  exact ⟨PEqualNP.Outside.L_meta_18330.C, by decide, PEqualNP.Outside.L_meta_18330.legal, by decide +kernel, PEqualNP.Outside.L_meta_18330.allRows⟩

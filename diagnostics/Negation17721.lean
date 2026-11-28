import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17721
open PEqualNP.CircuitLowerBounds
theorem negation : ¬ (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), (∀ (x5 : ℕ), x3.getD x5 Bool.false = Bool.true → x4.getD x5 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true) := by
  intro h
  let g : Gate := ⟨.and,[0,1]⟩
  let C : Circuit := ⟨[g],2⟩
  have ops : ∀ v ∈ C.gates, v.op = GateOp.and ∨ v.op = GateOp.or := by
    intro v hv
    obtain rfl : v=g := List.mem_singleton.mp hv
    exact .inl rfl
  have lexy : ∀ i : Nat, [true,true].getD i false = true → [true,true,false].getD i false = true := by
    intro i
    cases i with
    | zero => decide
    | succ j =>
      cases j with
      | zero => decide
      | succ k => simp [List.getD]
  have bad := h C ops [true,true] [true,true,false] lexy (by decide +kernel)
  exact Bool.noConfusion (show false=true from bad)
end PEqualNP.Outside.L_meta_17721

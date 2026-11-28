import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41722
open PEqualNP.CircuitLowerBounds
def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677288 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.or,[1,5]⟩,⟨.and,[2,6]⟩,⟨.and,[0,6]⟩,⟨.or,[1,3]⟩,⟨.and,[1,3]⟩,⟨.or,[8,10]⟩,⟨.and,[0,9]⟩,⟨.or,[7,12]⟩,⟨.and,[4,9]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩,⟨.and,[4,5]⟩,⟨.and,[10,17]⟩,⟨.or,[16,18]⟩], 19⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 6 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

end PEqualNP.Outside.L_meta_41722

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10716
open PEqualNP.CircuitLowerBounds

def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 4, 5, 0, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def witness : Circuit := ⟨[⟨.or,[3,4]⟩,⟨.or,[7,0]⟩,⟨.or,[2,5]⟩,⟨.or,[8,9]⟩,⟨.and,[8,9]⟩,⟨.or,[11,1]⟩,⟨.or,[4,5]⟩,⟨.and,[12,13]⟩,⟨.or,[14,6]⟩,⟨.and,[10,15]⟩,⟨.and,[0,3]⟩,⟨.or,[16,17]⟩], 18⟩

theorem witnessMonotone : ∀ g ∈ witness.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : witness.gates.length = 12 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim

end PEqualNP.Outside.L_meta_10716

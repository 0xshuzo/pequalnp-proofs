import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21907.Shared21907

def witness : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 9]⟩], 11⟩

end PEqualNP.Outside.L_meta_21907.Shared21907

open PEqualNP.Outside.L_meta_21907.Shared21907 in
theorem PEqualNP.Outside.L_meta_21907 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33826 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [witness, PEqualNP.MetaComplexity.Monotone2]

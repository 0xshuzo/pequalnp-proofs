import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20511.Shared21891

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 7]⟩], 10⟩

end PEqualNP.Outside.L_meta_20511.Shared21891

open PEqualNP.Outside.L_meta_20511.Shared21891 in
theorem PEqualNP.Outside.L_meta_20511 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (816 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [witness, PEqualNP.MetaComplexity.Monotone2]

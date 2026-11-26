import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22996

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_22996

theorem PEqualNP.Outside.L_meta_22996 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33586 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22996.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_22996.witness, PEqualNP.MetaComplexity.Monotone2]

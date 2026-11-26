import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21930

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_21930

theorem PEqualNP.Outside.L_meta_21930 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34092 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21930.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_21930.witness, PEqualNP.MetaComplexity.Monotone2]

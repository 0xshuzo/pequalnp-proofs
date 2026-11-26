import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23036

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_23036

theorem PEqualNP.Outside.L_meta_23036 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101176 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23036.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_23036.witness, PEqualNP.MetaComplexity.Monotone2]

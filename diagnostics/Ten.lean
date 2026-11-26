import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_16081

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem result : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨witness, by simp [witness, Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_16081

theorem PEqualNP.Outside.L_meta_16081 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = Nat.testBit 0xeae8e880 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_16081.result

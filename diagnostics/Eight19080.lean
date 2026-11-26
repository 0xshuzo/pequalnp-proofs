import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19080_TightUpper

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0,5]⟩,⟨.or, [1,6]⟩,⟨.or, [2,7]⟩,⟨.and, [8,9]⟩,⟨.or, [11,4]⟩,⟨.or, [8,9]⟩,⟨.and, [13,10]⟩,⟨.or, [14,12]⟩], 15⟩

theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (6077 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19080_TightUpper

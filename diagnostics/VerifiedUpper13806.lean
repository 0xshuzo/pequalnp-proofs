import PEqualNP.Defs

namespace SignedFourByFour

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0,1]⟩,⟨.or, [8,5]⟩,⟨.or, [2,4]⟩,⟨.or, [10,9]⟩,⟨.or, [9,7]⟩,⟨.and, [10,12]⟩,⟨.not, [13]⟩,⟨.and, [11,14]⟩], 15⟩

theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (13806 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end SignedFourByFour

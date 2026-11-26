import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19073_TightUpper

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0,4]⟩,⟨.or, [1,5]⟩,⟨.or, [2,6]⟩,⟨.or, [9,10]⟩,⟨.or, [11,7]⟩,⟨.and, [8,12]⟩,⟨.and, [9,10]⟩,⟨.or, [13,14]⟩], 15⟩

theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (862 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19073_TightUpper

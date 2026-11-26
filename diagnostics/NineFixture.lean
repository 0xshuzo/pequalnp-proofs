import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19353_aux

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [0,7]⟩,⟨.or, [1,5]⟩,⟨.or, [11,6]⟩,⟨.or, [2,12]⟩,⟨.or, [10,8]⟩,⟨.or, [12,14]⟩,⟨.and, [13,14]⟩,⟨.not, [16]⟩,⟨.and, [15,17]⟩], 18⟩

theorem result : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223868 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19353_aux

theorem PEqualNP.Outside.L_meta_19353 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223868 : ℕ).testBit (5 * u.val + v.val)) C := PEqualNP.Outside.L_meta_19353_aux.result

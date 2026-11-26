import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19167

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [6,7]⟩,⟨.and, [0,8]⟩,⟨.or, [5,7]⟩,⟨.and, [1,10]⟩,⟨.or, [4,6]⟩,⟨.and, [2,12]⟩,⟨.or, [4,5]⟩,⟨.and, [3,14]⟩,⟨.or, [9,11]⟩,⟨.or, [16,13]⟩,⟨.or, [17,15]⟩], 18⟩

theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 11 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (13740 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, witness]

end PEqualNP.Outside.L_meta_19167

theorem PEqualNP.Outside.L_meta_19167 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13740 : ℕ).testBit (4 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19167.upper

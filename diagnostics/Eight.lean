import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19203_research

theorem eight :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 8 ∧
      PEqualNP.Represents.Represents (fun u v : Fin 4 => (5068 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [5, 2]⟩,
       ⟨.or, [10, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [13, 4]⟩, ⟨.or, [12, 14]⟩], 15⟩,
    by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19203_research

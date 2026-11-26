import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19528_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [16, 19]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (3195660 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19528_aux

theorem PEqualNP.Outside.L_meta_19528 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3195660 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨PEqualNP.Outside.L_meta_19528_aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_19528_aux.witness]

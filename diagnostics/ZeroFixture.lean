import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19377_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem result : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 0 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223868 : ℕ).testBit (5 * u.val + v.val)) C) := by
  rintro ⟨⟨gs, o⟩, _, hs, hr⟩
  have e : gs.length = 0 := by simpa [Circuit.size] using hs
  have eg : gs = [] := List.length_eq_zero_iff.mp e
  subst gs
  by_cases h : o < 10
  · have cases_o : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 ∨ o = 4 ∨ o = 5 ∨ o = 6 ∨ o = 7 ∨ o = 8 ∨ o = 9 := by omega
    rcases cases_o with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hr <;> decide +kernel
  · have hv := hr (0 : Fin 5) (2 : Fin 5)
    have hh : (oneEach (0 : Fin 5) (2 : Fin 5)).length ≤ o := by
      have : (oneEach (0 : Fin 5) (2 : Fin 5)).length = 10 := by decide
      omega
    simp only [Circuit.eval, Circuit.wires, List.foldl_nil, List.getD_eq_default _ _ hh] at hv
    revert hv
    decide +kernel

end PEqualNP.Outside.L_meta_19377_aux

theorem PEqualNP.Outside.L_meta_19377 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 0 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16223868 : ℕ).testBit (5 * u.val + v.val)) C) := PEqualNP.Outside.L_meta_19377_aux.result

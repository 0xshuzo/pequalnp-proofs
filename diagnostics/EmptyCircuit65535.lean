import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem signedFourByFour_zero : ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 0 ∧ PEqualNP.Represents.Represents
      (fun u v : Fin 4 => (65535 : ℕ).testBit (4 * u.val + v.val)) C := by
  rintro ⟨⟨gs, o⟩, _, hs, hr⟩
  have e : gs.length = 0 := by simpa [Circuit.size] using hs
  have eg : gs = [] := List.length_eq_zero_iff.mp e
  subst gs
  by_cases h : o < 8
  · interval_cases o <;> revert hr <;> decide +kernel
  · have hv := hr (0 : Fin 4) (0 : Fin 4)
    have hh : (oneEach (0 : Fin 4) (0 : Fin 4)).length ≤ o := by
      have : (oneEach (0 : Fin 4) (0 : Fin 4)).length = 8 := by decide
      omega
    simp only [Circuit.eval, Circuit.wires, List.foldl_nil, List.getD_eq_default _ _ hh] at hv
    revert hv
    decide +kernel

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23118

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14332 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23118

theorem PEqualNP.Outside.L_meta_23118 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14332 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_23118.result

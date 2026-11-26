import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [11, 13]⟩], 14⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (363 : ℕ).testBit (4 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20411

theorem PEqualNP.Outside.L_meta_20411 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (363 : ℕ).testBit (4 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20411.result

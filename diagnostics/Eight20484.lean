import PEqualNP.Defs

namespace Rectangular1246Eight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩

theorem eight : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1246 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end Rectangular1246Eight

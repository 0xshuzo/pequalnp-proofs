import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21004_Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [16, 14]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36091 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21004_Upper

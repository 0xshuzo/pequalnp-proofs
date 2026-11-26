import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21811

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274943 : ℕ).testBit (6 * u.val + v.val)) 6 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21811

theorem PEqualNP.Outside.L_meta_21811 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274943 : ℕ).testBit (6 * u.val + v.val)) 6 := PEqualNP.Outside.L_meta_21811.result

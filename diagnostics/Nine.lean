import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21873

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327167 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21873

theorem PEqualNP.Outside.L_meta_21873 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (327167 : ℕ).testBit (6 * u.val + v.val)) 9 := PEqualNP.Outside.L_meta_21873.result

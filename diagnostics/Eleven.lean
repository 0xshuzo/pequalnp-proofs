import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23826

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [14, 13]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1864437 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23826

theorem PEqualNP.Outside.L_meta_23826 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1864437 : ℕ).testBit (6 * u.val + v.val)) 11 := PEqualNP.Outside.L_meta_23826.result

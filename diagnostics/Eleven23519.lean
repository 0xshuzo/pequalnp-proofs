import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23519

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23519

theorem PEqualNP.Outside.L_meta_23519 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900095 : ℕ).testBit (6 * u.val + v.val)) 11 := PEqualNP.Outside.L_meta_23519.result

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23391

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 16]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [18, 17]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838769 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23391

theorem PEqualNP.Outside.L_meta_23391 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838769 : ℕ).testBit (6 * u.val + v.val)) 10 := PEqualNP.Outside.L_meta_23391.result

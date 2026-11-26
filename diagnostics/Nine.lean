import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20952

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [12, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104251 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20952

theorem PEqualNP.Outside.L_meta_20952 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104251 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_20952.result

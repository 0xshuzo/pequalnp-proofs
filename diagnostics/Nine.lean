import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23360

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [12, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816703 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23360

theorem PEqualNP.Outside.L_meta_23360 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816703 : ℕ).testBit (6 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_23360.result

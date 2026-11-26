import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20479

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [13, 12]⟩], 14⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1230 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20479

theorem PEqualNP.Outside.L_meta_20479 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1230 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20479.result

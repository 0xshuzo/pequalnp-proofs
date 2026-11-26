import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21868

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [17, 14]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (324599 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21868

theorem PEqualNP.Outside.L_meta_21868 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (324599 : ℕ).testBit (6 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_21868.result

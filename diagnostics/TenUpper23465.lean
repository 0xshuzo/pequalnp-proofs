import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23465

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [10, 17]⟩, ⟨.or, [15, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1865451 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23465

theorem PEqualNP.Outside.L_meta_23465 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1865451 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_23465.result

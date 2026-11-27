import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21137

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [11, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39251 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21137

theorem PEqualNP.Outside.L_meta_21137 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39251 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_21137.result

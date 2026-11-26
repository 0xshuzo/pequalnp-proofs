import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21054

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [12, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103735 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21054

theorem PEqualNP.Outside.L_meta_21054 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103735 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21054.result

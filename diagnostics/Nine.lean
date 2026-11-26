import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20914

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [15, 16]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39134 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20914

theorem PEqualNP.Outside.L_meta_20914 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39134 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_20914.result

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23091

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [14, 2]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [11, 16]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29681 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23091

theorem PEqualNP.Outside.L_meta_23091 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29681 : ℕ).testBit (6 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_23091.result

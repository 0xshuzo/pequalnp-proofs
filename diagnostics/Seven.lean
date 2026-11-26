import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20514

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3471 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20514

theorem PEqualNP.Outside.L_meta_20514 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3471 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20514.result

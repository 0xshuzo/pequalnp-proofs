import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20519

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3509 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20519

theorem PEqualNP.Outside.L_meta_20519 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3509 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20519.result

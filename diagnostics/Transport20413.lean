import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20519.Transport20413

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20519.Transport20413

theorem PEqualNP.Outside.L_meta_20519 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (379 : ℕ).testBit (4 * u.val + v.val)) 6 :=
  PEqualNP.Outside.L_meta_20519.Transport20413.result

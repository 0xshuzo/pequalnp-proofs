import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [7, 9]⟩], 10⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (19 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (19 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  PEqualNP.Outside.L_meta_20394.result

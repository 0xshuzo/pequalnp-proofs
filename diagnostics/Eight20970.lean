import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20970

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [15, 13]⟩], 16⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114431 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20970

theorem PEqualNP.Outside.L_meta_20970 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114431 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20970.result

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20511

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [12, 2]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3321 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20511

theorem PEqualNP.Outside.L_meta_20511 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3321 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20511.result

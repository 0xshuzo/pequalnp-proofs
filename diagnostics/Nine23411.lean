import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23411

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 10]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841599 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23411

theorem PEqualNP.Outside.L_meta_23411 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841599 : ℕ).testBit (6 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_23411.result

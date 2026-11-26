import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20412

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (366 : ℕ).testBit (4 * u.val + v.val)) 7 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20412

theorem PEqualNP.Outside.L_meta_20412 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (366 : ℕ).testBit (4 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20412.result

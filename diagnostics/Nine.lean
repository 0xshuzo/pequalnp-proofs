import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20483

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1243 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20483

theorem PEqualNP.Outside.L_meta_20483 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1243 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_20483.result

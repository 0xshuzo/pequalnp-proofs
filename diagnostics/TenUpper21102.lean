import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21102

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [10, 7]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [15, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245627 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21102

theorem PEqualNP.Outside.L_meta_21102 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245627 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21102.result

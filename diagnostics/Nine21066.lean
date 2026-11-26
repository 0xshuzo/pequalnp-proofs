import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21066

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [13, 16]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105887 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21066

theorem PEqualNP.Outside.L_meta_21066 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105887 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_21066.result

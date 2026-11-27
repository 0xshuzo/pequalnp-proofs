import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25467

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 14]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [17, 2]⟩, ⟨.and, [15, 18]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [11, 22]⟩, ⟨.and, [21, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_25467

open PEqualNP.Outside.L_meta_25467 in
theorem PEqualNP.Outside.L_meta_25467 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (32435687 : ℕ).testBit (5 * u.val + v.val)) 15 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩


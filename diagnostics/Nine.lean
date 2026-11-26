import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20532.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [3, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20532.Upper

theorem PEqualNP.Outside.L_meta_20532 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (7541 : ℕ).testBit (5 * u.val + v.val)) 9 := PEqualNP.Outside.L_meta_20532.Upper.result

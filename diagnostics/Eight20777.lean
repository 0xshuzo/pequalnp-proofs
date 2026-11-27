import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20777

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.and, [10, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [4, 15]⟩, ⟨.or, [13, 16]⟩], 17⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (29459456 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20777

theorem PEqualNP.Outside.L_meta_20777 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (29459456 : ℕ).testBit (5 * u.val + v.val)) 8 := PEqualNP.Outside.L_meta_20777.result

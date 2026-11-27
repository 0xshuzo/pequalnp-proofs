import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [12, 13]⟩], 14⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (7438336 : ℕ).testBit (5 * u.val + v.val)) 5 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20713

theorem PEqualNP.Outside.L_meta_20713 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7438336 : ℕ).testBit (5 * u.val + v.val)) 5 := PEqualNP.Outside.L_meta_20713.result

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23761

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849387 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23761

theorem PEqualNP.Outside.L_meta_23761 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849387 : ℕ).testBit (6 * u.val + v.val)) 10 := PEqualNP.Outside.L_meta_23761.result

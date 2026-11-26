import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21789

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271156 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21789

theorem PEqualNP.Outside.L_meta_21789 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271156 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21789.result

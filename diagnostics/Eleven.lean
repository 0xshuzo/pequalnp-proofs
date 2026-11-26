import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21177

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103730 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21177

theorem PEqualNP.Outside.L_meta_21177 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103730 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_21177.result

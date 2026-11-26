import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23143

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14127 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23143

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14127 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23143.result

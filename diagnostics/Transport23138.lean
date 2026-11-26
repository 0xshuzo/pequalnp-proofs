import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23138

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [15, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6063 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23138

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6063 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23138.result

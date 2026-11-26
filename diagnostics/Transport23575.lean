import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23575

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [12, 14]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (268207 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23575

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (268207 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_20394.Transport23575.result

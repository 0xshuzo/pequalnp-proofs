import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23623.Transport23623

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [15, 11]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272254 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23623.Transport23623

theorem PEqualNP.Outside.L_meta_23623 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272254 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_23623.Transport23623.result

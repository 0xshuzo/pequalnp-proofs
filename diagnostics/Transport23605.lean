import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23605

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271230 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23605

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271230 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_20394.Transport23605.result

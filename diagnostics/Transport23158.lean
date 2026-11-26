import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23158

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [13, 6]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23158

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23158.result

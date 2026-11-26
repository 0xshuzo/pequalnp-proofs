import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23148

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23148

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23148.result

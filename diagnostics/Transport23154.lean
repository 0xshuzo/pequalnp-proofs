import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23154

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32382 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23154

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32382 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23154.result

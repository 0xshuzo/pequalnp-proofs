import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23684

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [18, 17]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23684

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23684.result

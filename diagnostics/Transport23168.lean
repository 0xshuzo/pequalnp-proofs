import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23168

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [12, 10]⟩, ⟨.and, [18, 17]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23168

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_20394.Transport23168.result

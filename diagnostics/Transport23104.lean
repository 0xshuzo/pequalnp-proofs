import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20519.Transport23104

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6127 : ℕ).testBit (6 * u.val + v.val)) 8 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20519.Transport23104

theorem PEqualNP.Outside.L_meta_20519 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6127 : ℕ).testBit (6 * u.val + v.val)) 8 :=
  PEqualNP.Outside.L_meta_20519.Transport23104.result

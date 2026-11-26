import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23604

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271222 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23604

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (271222 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_20394.Transport23604.result

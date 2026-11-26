import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23573

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (267191 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23573

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (267191 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_20394.Transport23573.result

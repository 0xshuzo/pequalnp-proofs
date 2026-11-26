import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23577.Transport23577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [10, 16]⟩, ⟨.or, [17, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [19, 18]⟩], 20⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (270718 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23577.Transport23577

theorem PEqualNP.Outside.L_meta_23577 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (270718 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_23577.Transport23577.result

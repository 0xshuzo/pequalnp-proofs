import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21091

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [9, 2]⟩, ⟨.and, [12, 11]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (127933 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21091

theorem PEqualNP.Outside.L_meta_21091 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (127933 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21091.result

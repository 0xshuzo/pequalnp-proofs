import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20394.Transport23139

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [13, 9]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [10, 9]⟩, ⟨.and, [17, 16]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (12670 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20394.Transport23139

theorem PEqualNP.Outside.L_meta_20394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (12670 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20394.Transport23139.result

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21241

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [5, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 5) (v : Fin 5) => (27037761 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21241

theorem PEqualNP.Outside.L_meta_21241 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27037761 : ℕ).testBit (5 * u.val + v.val)) 10 := PEqualNP.Outside.L_meta_21241.result

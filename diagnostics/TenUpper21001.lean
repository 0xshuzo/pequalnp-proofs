import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21001

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [15, 3]⟩, ⟨.and, [9, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩

theorem result : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36056 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, by simp [witness, PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21001

theorem PEqualNP.Outside.L_meta_21001 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36056 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21001.result

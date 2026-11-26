import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20167_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[
  ⟨.or, [4, 14]⟩,
  ⟨.or, [16, 12]⟩,
  ⟨.or, [1, 16]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.or, [18, 19]⟩,
  ⟨.or, [13, 17]⟩,
  ⟨.or, [3, 11]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [6, 14]⟩,
  ⟨.and, [13, 23]⟩,
  ⟨.or, [12, 22]⟩,
  ⟨.or, [23, 21]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.and, [26, 20]⟩,
  ⟨.or, [24, 10]⟩,
  ⟨.or, [1, 22]⟩,
  ⟨.or, [30, 31]⟩,
  ⟨.or, [19, 28]⟩,
  ⟨.or, [31, 0]⟩,
  ⟨.and, [10, 34]⟩,
  ⟨.and, [33, 27]⟩,
  ⟨.or, [25, 35]⟩,
  ⟨.or, [15, 5]⟩,
  ⟨.or, [28, 32]⟩,
  ⟨.or, [36, 29]⟩,
  ⟨.and, [38, 39]⟩,
  ⟨.or, [40, 37]⟩,
  ⟨.or, [42, 41]⟩], 43⟩

end PEqualNP.Outside.L_meta_20167_aux

theorem PEqualNP.Outside.L_meta_20167 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨PEqualNP.Outside.L_meta_20167_aux.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_20167_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

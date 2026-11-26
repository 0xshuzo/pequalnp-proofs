import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19190_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 0]⟩,
  ⟨.or, [4, 2]⟩,
  ⟨.or, [8, 5]⟩,
  ⟨.or, [10, 7]⟩,
  ⟨.or, [10, 9]⟩,
  ⟨.and, [11, 9]⟩,
  ⟨.not, [13]⟩,
  ⟨.and, [14, 12]⟩], 15⟩

theorem legal : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (13806 : ℕ).testBit (4 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_19190_aux

theorem PEqualNP.Outside.L_meta_19190 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13806 : ℕ).testBit (4 * u.val + v.val)) C := by
  exact ⟨L_meta_19190_aux.witness, L_meta_19190_aux.legal, by decide, L_meta_19190_aux.correct⟩

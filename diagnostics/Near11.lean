import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10128_upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [1,0]⟩, ⟨.or, [2,10]⟩, ⟨.or, [3,0]⟩, ⟨.or, [6,5]⟩, ⟨.or, [13,12]⟩, ⟨.or, [7,13]⟩, ⟨.and, [15,11]⟩, ⟨.or, [8,14]⟩, ⟨.or, [4,9]⟩, ⟨.and, [18,17]⟩, ⟨.or, [19,16]⟩], 20⟩

theorem upper : RepSizeAtMost (fun u v : Fin 5 => (12066039 : ℕ).testBit (5*u.val+v.val)) 11 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_10128_upper

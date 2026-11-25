import PEqualNP.Defs

namespace PEqualNP.Outside.Table9396Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or,[3,2]⟩, ⟨.or,[5,0]⟩, ⟨.or,[11,10]⟩, ⟨.or,[6,1]⟩, ⟨.or,[13,12]⟩,
    ⟨.or,[7,11]⟩, ⟨.or,[8,13]⟩, ⟨.and,[16,15]⟩, ⟨.or,[9,17]⟩, ⟨.or,[4,18]⟩,
    ⟨.and,[19,14]⟩],20⟩

theorem upper : RepSizeAtMost (fun u v : Fin 5 => (3687098 : ℕ).testBit (5*u.val+v.val)) 11 := by
  refine ⟨witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.Table9396Upper

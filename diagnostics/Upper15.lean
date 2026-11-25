import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8399_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def C : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[8,3]⟩,⟨.or,[9,4]⟩,⟨.and,[0,10]⟩,⟨.or,[2,5]⟩,⟨.and,[1,12]⟩,⟨.and,[2,6]⟩,⟨.and,[3,4]⟩,⟨.or,[3,5]⟩,⟨.or,[16,6]⟩,⟨.and,[7,17]⟩,⟨.or,[11,13]⟩,⟨.or,[19,14]⟩,⟨.or,[20,15]⟩,⟨.or,[21,18]⟩], 22⟩
theorem legal : FanInTwo C := by
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr (Or.inl rfl), by decide⟩ | exact ⟨Or.inr (Or.inr rfl), by decide⟩
def target := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4) || (x 3 && x 7) || (x 5 && x 7) || (x 6 && x 7)
theorem correct : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = target x := by decide +kernel
theorem bound : HasCircuitSize 8 target 15 := ⟨C,legal,by decide,correct⟩
end PEqualNP.Outside.L_meta_8399_aux

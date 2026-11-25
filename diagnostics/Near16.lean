import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_11029_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def C : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[9,7]⟩,⟨.and,[4,10]⟩,⟨.or,[0,2]⟩,⟨.and,[5,12]⟩,⟨.or,[0,3]⟩,⟨.or,[14,8]⟩,⟨.and,[6,15]⟩,⟨.or,[1,2]⟩,⟨.and,[7,17]⟩,⟨.or,[2,3]⟩,⟨.and,[8,19]⟩,⟨.or,[11,13]⟩,⟨.or,[21,16]⟩,⟨.or,[22,18]⟩,⟨.or,[23,20]⟩], 24⟩
theorem legal : FanInTwo C := by
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr (Or.inl rfl), by decide⟩ | exact ⟨Or.inr (Or.inr rfl), by decide⟩
def target := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x := by decide +kernel
theorem bound : HasCircuitSize 9 target 16 := ⟨C,legal,by decide,correct⟩
end PEqualNP.Outside.L_meta_11029_aux

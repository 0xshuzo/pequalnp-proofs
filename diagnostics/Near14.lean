import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10495_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def C : Circuit := ⟨[⟨.or,[4,7]⟩,⟨.or,[9,8]⟩,⟨.and,[10,0]⟩,⟨.or,[5,7]⟩,⟨.and,[12,1]⟩,⟨.or,[6,8]⟩,⟨.and,[14,2]⟩,⟨.and,[7,3]⟩,⟨.or,[6,7]⟩,⟨.and,[17,8]⟩,⟨.or,[11,13]⟩,⟨.or,[19,15]⟩,⟨.or,[20,16]⟩,⟨.or,[21,18]⟩], 22⟩
theorem legal : FanInTwo C := by
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr (Or.inl rfl), by decide⟩ | exact ⟨Or.inr (Or.inr rfl), by decide⟩
def target := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 7 && x 8)
theorem correct : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x := by decide +kernel
theorem bound : HasCircuitSize 9 target 14 := ⟨C,legal,by decide,correct⟩
end PEqualNP.Outside.L_meta_10495_aux

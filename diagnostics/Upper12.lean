import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9929.Exhibit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨.not,[3]⟩,⟨.and,[0, 6]⟩,⟨.not,[4]⟩,⟨.and,[1, 8]⟩,⟨.or,[1, 8]⟩,⟨.and,[10, 7]⟩,⟨.or,[9, 11]⟩,⟨.not,[5]⟩,⟨.and,[2, 13]⟩,⟨.or,[2, 13]⟩,⟨.and,[15, 12]⟩,⟨.or,[14, 16]⟩],17⟩

theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => decide ((1 * (x 3).toNat + 2 * (x 4).toNat + 4 * (x 5).toNat) < (1 * (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat))) 12 := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals constructor <;> decide
  · intro x
    have e : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
    rw [e]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;> decide

end PEqualNP.Outside.L_meta_9929.Exhibit

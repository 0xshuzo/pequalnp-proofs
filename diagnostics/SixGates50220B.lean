import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50220
open PEqualNP.CircuitLowerBounds
private def witness : Circuit :=
  ⟨[⟨.not,[2]⟩, ⟨.and,[1,7]⟩, ⟨.not,[3]⟩, ⟨.and,[0,9]⟩, ⟨.or,[4,10]⟩, ⟨.and,[2,11]⟩], 0⟩

theorem sixGates : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (46 : Nat).testBit t.val := by
  refine ⟨witness, ⟨8, by decide⟩, ⟨12, by decide⟩, ⟨11, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp [witness] at hg
    rcases hg with h|h|h|h|h|h <;> subst g <;> simp
  · intro j hj
    change j < 6 at hj
    interval_cases j <;> decide
  · decide
  · decide
  · decide

end PEqualNP.Outside.L_meta_50220

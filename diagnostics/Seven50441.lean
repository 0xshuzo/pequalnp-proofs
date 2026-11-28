import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50441
open PEqualNP.CircuitLowerBounds
private def witness : Circuit :=
  ⟨[⟨.not,[0]⟩, ⟨.or,[4,7]⟩, ⟨.not,[2]⟩, ⟨.and,[0,9]⟩, ⟨.or,[3,10]⟩, ⟨.or,[1,7]⟩, ⟨.and,[9,12]⟩], 0⟩

theorem sevenGates : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 7 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (33 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val := by
  refine ⟨witness, ⟨13, by decide⟩, ⟨8, by decide⟩, ⟨11, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp [witness] at hg
    rcases hg with h|h|h|h|h|h|h <;> subst g <;> simp
  · intro j hj
    change j < 7 at hj
    interval_cases j <;> decide
  · decide
  · decide
  · decide

end PEqualNP.Outside.L_meta_50441

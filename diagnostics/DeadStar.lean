import Mathlib
import PEqualNP.Defs
namespace DeadStar4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
attribute [local instance] gateOpDecEq

def C : Circuit := ⟨[⟨.and,[0,1]⟩,⟨.and,[0,2]⟩,⟨.or,[3,4]⟩,⟨.or,[1,2]⟩],5⟩
def E : Finset (Fin 1 × Fin 2) := Finset.univ
def star (j : Fin 4) :=
    (gateAt C j.val).op=GateOp.or ∧
    ∀x : Fin 3 → Bool,(C.wires (List.ofFn x)).getD (3+j.val) false=(x 1 || x 2)
instance (j : Fin 4) : Decidable (star j) := by unfold star; infer_instance

set_option maxHeartbeats 0 in
theorem present : IsAO2 3 C ∧ PEqualNP.TwoColour.tCount 3 C (fun i=>decide (1≤i))=0 ∧
    (∀x : Fin 3 → Bool,circuitFun 3 C x=decide (∃(a : Fin 1)(b : Fin 2),(a,b)∈E ∧
      x (Fin.castAdd 2 a)=true ∧ x (Fin.natAdd 1 b)=true)) ∧
    (∀b : Fin 2,b∈(Finset.univ : Finset (Fin 2)) ∧ (∀z : Fin 2,(0,z)∈E) ∧
       ∀x : Fin 3 → Bool,(C.wires (List.ofFn x)).getD 6 false=
       decide (∃z∈(Finset.univ : Finset (Fin 2)),x (Fin.natAdd 1 z)=true)) ∧
    (∀ j : Fin 4,star j ↔ j=3) ∧
    (∀ g∈C.gates,6∉g.inputs) ∧ C.output=5 := by decide +kernel
end DeadStar4970

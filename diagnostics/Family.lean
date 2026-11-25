import Mathlib
import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.NewLowMerge
namespace Family606
open PEqualNP.CircuitLowerBounds PEqualNP.LowMerge

def inc (p : Fin 4) (w : Fin 3) : Bool := decide (p.val=0 ∨ p.val=w.val+1)

def C : Circuit :=
  ⟨[⟨GateOp.and,[1,4]⟩,⟨GateOp.and,[2,5]⟩,⟨GateOp.and,[3,6]⟩,
    ⟨GateOp.or,[7,8]⟩,⟨GateOp.or,[10,9]⟩,
    ⟨GateOp.or,[4,5]⟩,⟨GateOp.or,[12,6]⟩,
    ⟨GateOp.and,[0,13]⟩,⟨GateOp.or,[11,14]⟩],15⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

theorem noRect : ∀p q w v,p≠q → w≠v →
    ¬(inc p w=true ∧ inc p v=true ∧ inc q w=true ∧ inc q v=true) := by decide +kernel

theorem correct : ∀(x : Fin 4→Bool)(y : Fin 3→Bool),C.eval (List.ofFn x++List.ofFn y)=
       decide (∃p w,inc p w=true ∧ x p=true ∧ y w=true) := by decide +kernel

theorem mono : IsMonotoneCircuit C := by
  intro h hh
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem fan : ∀g∈C.gates,g.inputs.length≤2 := by
  intro h hh
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem outputMerges : ∀w,IsLowMerge 4 3 inc C C.output w := by decide +kernel
theorem noEarlier : ∀j : Fin 15, ∀w,¬IsLowMerge 4 3 inc C j.val w := by decide +kernel
end Family606

import Mathlib
import PEqualNP.Defs
namespace TwoDirty4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
attribute [local instance] gateOpDecEq

def C : Circuit := ⟨[⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[0,1]⟩,⟨.or,[6,7]⟩,
  ⟨.and,[8,9]⟩,⟨.and,[0,0]⟩,⟨.and,[1,1]⟩,⟨.or,[11,7]⟩,⟨.or,[12,6]⟩,
  ⟨.and,[13,14]⟩,⟨.and,[10,15]⟩],16⟩
def E : Finset (Fin 2 × Fin 4) := {(0,0),(0,1),(1,2),(1,3)}
def edges : Finset (Fin 6 × Fin 6) := {(0,2),(0,3),(1,4),(1,5)}
def G : SimpleGraph (Fin 6) where
  Adj a b := (a,b) ∈ edges ∨ (b,a) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable ((a,b)∈edges ∨ (b,a)∈edges))

set_option maxHeartbeats 0 in
theorem posted : NoFourCycle G ∧ IsAO2 6 C ∧
    PEqualNP.TwoColour.tCount 6 C (fun i=>decide (2≤i))=0 ∧
    (∀ x : Fin 6 → Bool,circuitFun 6 C x=decide (∃a b,(a,b)∈E ∧
      x (Fin.castAdd 4 a)=true ∧ x (Fin.natAdd 2 b)=true)) ∧
    (∀a b,(a,b)∈E → let Q := (Finset.univ : Finset (Fin 4)).filter (fun t=>(a,t)∈E)
      let j := a.val
      j<C.gates.length ∧ (gateAt C j).op=GateOp.or ∧ 2≤Q.card ∧ b∈Q ∧
      (∀t∈Q,(a,t)∈E) ∧ ∀x : Fin 6 → Bool,(C.wires (List.ofFn x)).getD (6+j) false=
         decide (∃t∈Q,x (Fin.natAdd 2 t)=true)) ∧
    (∀ x : Fin 6→Bool,circuitFun 6 C x=graphFun G ∅ x) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

set_option maxHeartbeats 0 in
theorem obstruction : 4<C.size ∧ (gateAt C 4).op=GateOp.and ∧ ¬BelowF G C 4 ∧
  G.Adj 0 2 ∧ G.Adj 1 4 ∧ s((0:Fin 6),2)≠s((1:Fin 6),4) ∧
  PEqualNP.ReadK.readsAtMost C 6 [0,2] 1=false ∧ PEqualNP.ReadK.readsAtMost C 6 [1,4] 1=false ∧
  gateVal 6 C 4 (pairInput 0 2)=true ∧ gateVal 6 C 4 (pairInput 1 4)=true ∧
  (∀j : Fin 11, j<10 → ∃ k : Fin 11,j<k ∧ 6+j.val∈(gateAt C k.val).inputs) ∧
  gateVal 6 C 4 (pairInput 0 4)=true ∧ gateVal 6 C 9 (pairInput 0 4)=false ∧
  gateVal 6 C 4 (pairInput 0 1)=false ∧ gateVal 6 C 9 (pairInput 0 1)=true := by
  repeat' apply And.intro
  all_goals decide +kernel
end TwoDirty4970

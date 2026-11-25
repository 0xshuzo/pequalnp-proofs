import Mathlib
import PEqualNP.Defs
namespace ActiveStar4970
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
attribute [local instance] gateOpDecEq

def C : Circuit := ⟨[⟨.or,[4,5]⟩,⟨.and,[1,6]⟩,⟨.or,[2,3]⟩,⟨.or,[7,0]⟩,⟨.or,[7,8]⟩,⟨.and,[9,10]⟩],11⟩
def E : Finset (Fin 2 × Fin 4) := {(0,0),(0,1),(1,2),(1,3)}
def f (x : Fin 6 → Bool) := decide (∃(a : Fin 2)(b : Fin 4),(a,b)∈E ∧
      x (Fin.castAdd 4 a)=true ∧ x (Fin.natAdd 2 b)=true)
def cover (S : Finset (Fin 6)) := ∀e∈E,Fin.castAdd 4 e.1∈S ∨ Fin.natAdd 2 e.2∈S
instance (S : Finset (Fin 6)) : Decidable (cover S) := by unfold cover; infer_instance
set_option maxHeartbeats 0 in
theorem example_all : IsAO2 6 C ∧ PEqualNP.TwoColour.tCount 6 C (fun i=>decide (2≤i))=0 ∧
    (∀x : Fin 6 → Bool,circuitFun 6 C x=f x) ∧
    (∀ (a : Fin 2) (b : Fin 4), (a,b)∈E →
      let Q := (Finset.univ : Finset (Fin 4)).filter (fun t=>(a,t)∈E)
      let j := if a.val=0 then 2 else 0
      j<C.gates.length ∧ (gateAt C j).op=GateOp.or ∧ 2≤Q.card ∧ b∈Q ∧
       (∀z∈Q,(a,z)∈E) ∧ ∀x : Fin 6 → Bool,
        (C.wires (List.ofFn x)).getD (6+j) false=decide (∃z∈Q,x (Fin.natAdd 2 z)=true)) ∧
    (∀j : Fin 6,j.val<5 → ∃ k : Fin 6,j.val<k.val ∧ 6+j.val∈(gateAt C k.val).inputs) ∧
    (∀j : Fin 6,(gateAt C j.val).op=GateOp.or → ∃x : Fin 6 → Bool,
       (C.wires (List.ofFn x)).getD (6+j.val) false=true ∧ f x=false) ∧
    (∀ j : Fin 6,(gateAt C j.val).op=GateOp.and → ¬(0∈(gateAt C j.val).inputs ∧ 8∈(gateAt C j.val).inputs)) ∧
    (∀S : Finset (Fin 6),cover S → 2≤S.card) ∧ (gateAt C 5).op=GateOp.and ∧ C.output=11 := by decide +kernel
end ActiveStar4970

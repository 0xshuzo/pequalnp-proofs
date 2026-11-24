import Mathlib
import PEqualNP.Defs

namespace Witness2223
open PEqualNP.CircuitLowerBounds
set_option maxHeartbeats 4500000
set_option maxRecDepth 12000

def C : Circuit := ⟨[⟨.or,[7,13]⟩,
  ⟨.or,[14,11]⟩,
  ⟨.and,[0,15]⟩,
  ⟨.or,[8,7]⟩,
  ⟨.or,[17,12]⟩,
  ⟨.or,[16,1]⟩,
  ⟨.or,[16,18]⟩,
  ⟨.and,[19,20]⟩,
  ⟨.or,[9,8]⟩,
  ⟨.or,[22,13]⟩,
  ⟨.and,[2,23]⟩,
  ⟨.or,[21,24]⟩,
  ⟨.or,[10,9]⟩,
  ⟨.or,[26,7]⟩,
  ⟨.and,[3,27]⟩,
  ⟨.or,[25,28]⟩,
  ⟨.or,[11,10]⟩,
  ⟨.or,[30,8]⟩,
  ⟨.and,[4,31]⟩,
  ⟨.or,[29,32]⟩,
  ⟨.or,[12,11]⟩,
  ⟨.or,[34,9]⟩,
  ⟨.and,[5,35]⟩,
  ⟨.or,[33,36]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[38,10]⟩,
  ⟨.and,[6,39]⟩,
  ⟨.or,[37,40]⟩],41⟩
def flags : List (Fin 7 × Fin 7) := [(0,0),(0,6),(0,4),(1,1),(1,0),(1,5),(2,2),(2,1),(2,6),(3,3),(3,2),(3,0),(4,4),(4,3),(4,1),(5,5),(5,4),(5,2),(6,6),(6,5),(6,3)]

theorem incidence : ∀ p l : Fin 7, (p,l)∈flags ↔ p=l ∨ p=l+1 ∨ p=l+3 := by decide +kernel

def hits (x : Fin 14 → Bool) :=
  flags.any (fun e => x (Fin.castAdd 7 e.1) && x (Fin.natAdd 7 e.2))

theorem eval (x : Fin 14 → Bool) : C.eval (List.ofFn x)=hits x := by
  have expanded : C.eval (List.ofFn x) = (GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.or.eval [(GateOp.and.eval [(GateOp.or.eval [(GateOp.and.eval [x 0,(GateOp.or.eval [(GateOp.or.eval [x 7,x 13]),x 11])]),x 1]),(GateOp.or.eval [(GateOp.and.eval [x 0,(GateOp.or.eval [(GateOp.or.eval [x 7,x 13]),x 11])]),(GateOp.or.eval [(GateOp.or.eval [x 8,x 7]),x 12])])]),(GateOp.and.eval [x 2,(GateOp.or.eval [(GateOp.or.eval [x 9,x 8]),x 13])])]),(GateOp.and.eval [x 3,(GateOp.or.eval [(GateOp.or.eval [x 10,x 9]),x 7])])]),(GateOp.and.eval [x 4,(GateOp.or.eval [(GateOp.or.eval [x 11,x 10]),x 8])])]),(GateOp.and.eval [x 5,(GateOp.or.eval [(GateOp.or.eval [x 12,x 11]),x 9])])]),(GateOp.and.eval [x 6,(GateOp.or.eval [(GateOp.or.eval [x 13,x 12]),x 10])])]) := by rfl
  rw [expanded]
  simp only [hits,flags,List.any_cons,List.any_nil,Bool.or_false,GateOp.eval,
    List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true]
  bv_decide

theorem correct (x : Fin 14 → Bool) : C.eval (List.ofFn x)=true ↔
    ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true := by
  rw [eval]
  simp only [hits,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨⟨p,l⟩,h,u,v⟩
    exact ⟨p,l,(incidence p l).mp h,u,v⟩
  · rintro ⟨p,l,h,u,v⟩
    exact ⟨(p,l),(incidence p l).mpr h,u,v⟩

theorem degree : C.lineDeg 14 {0}=2 ∧ C.lineDeg 14 {7}=2 := by decide +kernel
theorem repeated : ¬((C.output::C.gates.flatMap Gate.inputs).filter (fun w => decide (14≤w))).Nodup := by
  decide +kernel
theorem size : C.gates.length=28 := by decide +kernel

theorem shape (j : ℕ) (g : Gate) (h : C.gates[j]?=some g) :
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ, g.inputs=[a,b] ∧ a≠b ∧ a<14+j ∧ b<14+j := by
  let good (k : ℕ) (t : Gate) :=
    let a := t.inputs.getD 0 0
    let b := t.inputs.getD 1 0
    (t.op=.and ∨ t.op=.or) ∧ t.inputs=[a,b] ∧ a≠b ∧ a<14+k ∧ b<14+k
  have cert : ∀ k : Fin 28, good k (C.gates.getD k ⟨.or,[]⟩) := by
    letI := lineDegreeGateOpDecEq
    dsimp only [good]
    decide +kernel
  obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp h
  have small : j<28 := size ▸ hj
  have he : C.gates.getD j ⟨.or,[]⟩ = g := (List.getD_eq_getElem _ _ hj).trans eq
  have valid : good j (C.gates.getD j ⟨.or,[]⟩) := cert ⟨j,small⟩
  rw [he] at valid
  exact ⟨valid.1,_,_,valid.2⟩

end Witness2223

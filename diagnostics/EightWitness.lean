import PEqualNP.Defs

namespace Research9755.EightWitness
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 12000
def graph (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def C : Circuit := ⟨[⟨.or,[3,9]⟩,⟨.or,[3,5]⟩,⟨.or,[9,5]⟩,⟨.and,[4,10]⟩,⟨.and,[8,11]⟩,⟨.and,[7,12]⟩,⟨.or,[13,14]⟩,⟨.or,[15,16]⟩,⟨.or,[3,7]⟩,⟨.or,[4,5]⟩,⟨.or,[9,8]⟩,⟨.and,[0,19]⟩,⟨.or,[1,18]⟩,⟨.and,[2,22]⟩,⟨.or,[1,20]⟩,⟨.and,[6,24]⟩,⟨.or,[17,21]⟩,⟨.or,[23,25]⟩,⟨.or,[26,27]⟩],28⟩

theorem fit : FanInTwo C := by
  intro g hg
  simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide
def bitrow (x : BitVec 10) (i : Fin 10) := x.getLsbD i.val
def board (x : BitVec 10) := List.ofFn (bitrow x)
def cases' : Array (BitVec 10 × BitVec 10) := #[(16,17),(0,2),(2,6),(0,2),(2,66),(16,17),(2,6),(2,6)]
theorem controlGates : ∀ i : Fin 8,
    let x := cases'[i.val]!.1
    let y := cases'[i.val]!.2
    x &&& 952 = y &&& 952 ∧
    (C.wires (board x)).getD (21+i.val) false ≠ (C.wires (board y)).getD (21+i.val) false
    := by decide +kernel
set_option maxHeartbeats 4000000 in
theorem correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x)=graph x := by decide +kernel
theorem upper : HasCircuitSize 10 graph 19 := ⟨C,fit,by decide,correct⟩
end Research9755.EightWitness

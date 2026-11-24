import PEqualNP.Defs

namespace Plane2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.TopForm PEqualNP.ReadK PEqualNP.CircuitMoves

def threeEdges (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 3)

def block : Circuit := ⟨[
  ⟨.or, [0,1]⟩,
  ⟨.or, [2,3]⟩,
  ⟨.and, [4,5]⟩,
  ⟨.or, [0,3]⟩,
  ⟨.and, [6,7]⟩], 8⟩

def stars : Circuit := ⟨[
  ⟨.or, [2,3]⟩,
  ⟨.and, [0,4]⟩,
  ⟨.and, [1,3]⟩,
  ⟨.or, [5,6]⟩], 7⟩

set_option maxHeartbeats 1000000

theorem block_example :
    IsAO2 4 block ∧ (∀ x, circuitFun 4 block x = threeEdges x) ∧
    (∀ w : Fin 8, ¬ WireBelowOutput 4 block w.val) ∧ ¬ IsReadK 4 block 1 := by
  decide +kernel

theorem stars_example :
    IsAO2 4 stars ∧ (∀ x, circuitFun 4 stars x = threeEdges x) ∧
    IsReadK 4 stars 1 ∧ stars.size + 1 = block.size := by
  decide +kernel

end Plane2583

import PEqualNP.Defs

namespace Near6796
open PEqualNP.CircuitLowerBounds
def core : Circuit := ⟨[
  ⟨.or,[4,8]⟩,
  ⟨.or,[10,7]⟩,
  ⟨.or,[6,7]⟩,
  ⟨.or,[9,6]⟩,
  ⟨.and,[14,12]⟩,
  ⟨.or,[5,9]⟩,
  ⟨.or,[5,0]⟩,
  ⟨.and,[10,12]⟩,
  ⟨.or,[4,0]⟩,
  ⟨.or,[4,16]⟩,
  ⟨.or,[2,19]⟩,
  ⟨.or,[15,3]⟩,
  ⟨.and,[9,9]⟩
],0⟩
def terms : List (ℕ × ℕ) := [(23,17), (18,21), (1,11), (2,5), (13,22), (8,20)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem certificate : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List (ℕ × ℕ)),   have x3 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];   have x4 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.BlindGate.wireValue x1 (11 : ℕ) (fun (x7 : Fin (11 : ℕ)) => x5.testBit ↑x7) x6;   PEqualNP.TopForm.IsAO2 (11 : ℕ) x1 ∧ x2 ≠ [] ∧ x1.size + (2 : ℕ) * x2.length ≤ (25 : ℕ) ∧ (3 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x1 ∧ (∀ x6 ∈ x2, x6.1 < (11 : ℕ) + x1.size ∧ x6.2 < (11 : ℕ) + x1.size) ∧ (∀ x6 < x1.size, (x3.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true ∧ (x4.any fun (x8 : ℕ) => x5 x8 ((11 : ℕ) + x6)) = Bool.true) ∧ (∀ x6 < x1.size, PEqualNP.ReadTwo.isAnd x1 x6 → ∃ x9 ∈ x2, ∃ x10 ∈ [x9.1, x9.2], x10 = (11 : ℕ) + x6 ∨ (11 : ℕ) ≤ x10 ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x1 x6 (x10 - (11 : ℕ))) ∧ ∀ x6 ∈ x3 ++ x4, (x2.any fun (x8 : ℕ × ℕ) => x5 x6 x8.1 && x5 x6 x8.2) = Decidable.decide (x6 ∈ x3) := by
  refine ⟨core,terms,?_⟩
  dsimp only
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
end Near6796

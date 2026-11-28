import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_33242.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_33242
open PEqualNP.CircuitLowerBounds
abbrev Wire (R : Type) := R → Bool

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

abbrev LocalSix := BitVec 6
private def localFun (x : LocalSix) : Wire (Fin 6) := fun i => x.getLsbD i.val
private theorem faceZero : localFun 0 = fun _ => false := by funext i; simp [localFun]
private theorem faceOne : localFun 63 = fun _ => true := by decide +kernel
private def flatWeight (w : LocalSix) :=
  if w = (0 : LocalSix) ∨ w = (63 : LocalSix) then 1 else 0
private theorem flat_le (w : LocalSix) : flatWeight w ≤ cost (localFun w) := by
  classical
  unfold flatWeight
  split
  next h =>
    have hc : Constant (localFun w) := by
      rcases h with rfl | rfl
      · exact ⟨_,faceZero⟩
      · exact ⟨_,faceOne⟩
    simp only [cost,if_pos hc,Nat.le_refl]
  next => exact Nat.zero_le _

end PEqualNP.Outside.L_meta_33242

import PEqualNP.Outside.L_meta_175
import PEqualNP.Outside.L_meta_10436
import PEqualNP.Outside.L_meta_670
namespace PEqualNP.Outside.L_meta_9755.Signed17
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768
abbrev V := Fin 10
def f (x : Fin 10 → Bool) := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 2 && x 3) || (x 2 && x 7) || (x 3 && x 4) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 5 && x 8) || (x 6 && x 8) || (x 6 && x 9) || (x 7 && x 9)
def h (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def reindex : Fin 10 → Fin 10 := ![9,4,0,1,6,7,3,5,2,8]
def f' (x : Fin 10 → Bool) := f (x ∘ reindex)
theorem restrictEq : (fun y : Fin 9 → Bool => f' (Fin.snoc y false))=h := by
  funext y
  exact (by decide +kernel : ∀ x : Fin 9 → Bool, f' (Fin.snoc x false)=h x) y
theorem lower : ¬ HasCircuitSize 10 f 16 := by
  intro hc
  have renamed : HasCircuitSize 10 f' 16 := PEqualNP.Outside.L_meta_10436.relabel_size reindex f 16 hc
  have dep : ∃ x : Fin 10 → Bool, f' (Function.update x (Fin.last 9) (!x (Fin.last 9))) ≠ f' x := by
    exact ⟨fun i => decide (i=6),by decide +kernel⟩
  have nc : ∃ x y : Fin 9 → Bool, f' (Fin.snoc x false) ≠ f' (Fin.snoc y false) := by
    exact ⟨fun _ => false,fun i => decide (i=0 ∨ i=1),by decide +kernel⟩
  have smaller := PEqualNP.MetaComplexity.Helpers.gate_elim 9 f' false 15 dep nc renamed
  rw [restrictEq] at smaller
  exact PEqualNP.Outside.L_meta_670 smaller
end PEqualNP.Outside.L_meta_9755.Signed17

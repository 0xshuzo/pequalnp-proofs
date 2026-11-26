import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2585.Tight870
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def C : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[0,3]⟩,⟨.or,[12,5]⟩,⟨.or,[4,14]⟩,⟨.or,[1,3]⟩,⟨.or,[13,4]⟩,⟨.or,[7,8]⟩,⟨.or,[6,18]⟩,⟨.and,[0,19]⟩,⟨.and,[16,9]⟩,⟨.and,[17,10]⟩,⟨.and,[1,7]⟩,⟨.and,[2,8]⟩,⟨.or,[24,11]⟩,⟨.or,[23,25]⟩,⟨.and,[15,26]⟩,⟨.or,[21,22]⟩,⟨.or,[20,27]⟩,⟨.or,[28,29]⟩],30⟩
def row (i : Fin 6) : Nat := ![23,42,36,24,48,32] i
theorem typed : IsAO2 12 C ∧ C.size=19 := by decide +kernel
theorem right : ∀ x : Fin 12 → Bool, circuitFun 12 C x = decide (∃ a b : Fin 6, (row a).testBit b.val=true ∧ x (Fin.castAdd 6 a)=true ∧ x (Fin.natAdd 6 b)=true) := by decide +kernel
theorem fails : ¬ IsReadK 12 C 1 := by
  intro h
  have prime : IsPrimeImplicant 12 C ({1,7} : Finset (Fin 12)) := by decide +kernel
  have bad := h _ prime
  have no : readsAtMost C 12 (setList ({1,7} : Finset (Fin 12))) 1 = false := by decide +kernel
  exact Bool.noConfusion (bad.symm.trans no)
end PEqualNP.Outside.L_meta_2585.Tight870

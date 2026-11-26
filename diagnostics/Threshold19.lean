import Mathlib
import PEqualNP.Defs

namespace PetersenFeedback19
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def C : Circuit := ⟨[
  ⟨.or,[2,6]⟩, ⟨.and,[1,10]⟩, ⟨.or,[1,4]⟩, ⟨.or,[12,5]⟩,
  ⟨.and,[0,13]⟩, ⟨.or,[2,4]⟩, ⟨.or,[15,8]⟩, ⟨.and,[3,16]⟩,
  ⟨.or,[2,5]⟩, ⟨.or,[18,9]⟩, ⟨.and,[7,19]⟩, ⟨.or,[5,6]⟩,
  ⟨.and,[8,21]⟩, ⟨.or,[4,6]⟩, ⟨.and,[9,23]⟩,
  ⟨.or,[14,17]⟩, ⟨.or,[25,20]⟩, ⟨.or,[26,22]⟩, ⟨.or,[27,24]⟩],28⟩

def raw (m : Nat) : Fin 10 → Bool := fun i => m.testBit i.val
def guard (m : Nat) : Bool := (C.wires (List.ofFn (Function.update (raw m) 0 false))).getD 11 false
def repaired (m : Nat) : Bool := circuitFun 10 C (Function.update (raw m) 0 (raw m 0 || guard m))

theorem scheduled : ∀ (j : Nat) (g : Gate), 10+j ≤ 11 → C.gates[j]? = some g → 0 ∉ g.inputs := by
  intro j g h read
  have hj : j=0 ∨ j=1 := by omega
  rcases hj with rfl|rfl <;> simp [C] at read <;> subst g <;> decide

theorem works : IsAO2 10 C ∧ C.size = 19 ∧
  (∀ n ∈ ([50,104,116,138,208,276,402,548,554,770] : List Nat), guard n = false) ∧
  (∀ n ∈ ([3,6,12,17,24,33,66,132,160,264,288,320,528,576,640] : List Nat), repaired n = true) ∧
  (∀ n ∈ ([50,69,104,116,138,201,208,276,385,402,521,548,554,770,773] : List Nat), repaired n = false) := by
  decide +kernel

end PetersenFeedback19

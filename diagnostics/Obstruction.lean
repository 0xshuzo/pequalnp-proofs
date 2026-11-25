import Mathlib
import PEqualNP.Defs

namespace Obstruction3321
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

attribute [local instance] gateOpDecEq

def G (op : GateOp) (a b : Nat) : Gate := ⟨op,[a,b]⟩
def W {n : Nat} (C : Circuit) (w : Nat) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false
def S (n : Nat) (xs : List Nat) (i : Fin n) : Bool := xs.contains i.val

def star : Circuit :=
  ⟨[G .or 3 4,G .and 0 1,G .or 7 2,G .and 8 6,G .and 9 2],10⟩

def I (p l : Fin 3) : Prop := p=2 ∧ (l=0 ∨ l=1)
instance (p l : Fin 3) : Decidable (I p l) := by unfold I; infer_instance

theorem star_four_free : ∀ p p' l l' : Fin 3, p ≠ p' → l ≠ l' →
    ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by decide +kernel

theorem exact_star : ∀ z : Fin 6 → Bool, circuitFun 6 star z = true ↔
    ∃ p l : Fin 3, I p l ∧ z (Fin.castAdd 3 p)=true ∧ z (Fin.natAdd 3 l)=true := by decide +kernel

theorem single_and_pair :
    (∀ j : Fin 5, (gateAt star j.val).op = .and →
      ∀ i : Fin 6, W star (6+j.val) (S 6 [i.val]) = false) ∧
    (∀ j : Fin 5, (gateAt star j.val).op = .and →
      ∀ p l : Fin 3, ¬ I p l → W star (6+j.val) (S 6 [p.val,3+l.val]) = false) := by
  decide +kernel

theorem larger_assignment_obstructs : (gateAt star 3).op=.and ∧
    W star 9 (S 6 [0,1,3])=true ∧
    W star 9 (fun i : Fin 6 => decide (i.val<3) && S 6 [0,1,3] i)=false ∧
    W star 9 (fun i : Fin 6 => decide (3 ≤ i.val) && S 6 [0,1,3] i)=false ∧
    circuitFun 6 star (S 6 [0,1,3])=false := by decide +kernel

def matching : Circuit :=
  ⟨[G .or 0 1,G .or 2 3,G .and 4 5,G .and 0 2,G .and 1 3,G .or 7 8,G .and 6 9],10⟩

theorem exact_matching : ∀ z : Fin 4 → Bool, circuitFun 4 matching z = true ↔
    ∃ p : Fin 2, z (Fin.castAdd 2 p)=true ∧ z (Fin.natAdd 2 p)=true := by decide +kernel

theorem four_supports : W matching 6 (S 4 [0,2])=true ∧ W matching 6 (S 4 [1,3])=true ∧
    W matching 6 (S 4 [0,3])=true ∧ W matching 6 (S 4 [1,2])=true := by decide +kernel

theorem no_pair_of_old_ports : ∀ a b : Fin 6,
    (W matching a.val (S 4 [0,2]) && W matching b.val (S 4 [0,2])) = true →
    (W matching a.val (S 4 [1,3]) && W matching b.val (S 4 [1,3])) = true →
    ∃ z : Fin 4 → Bool, W matching a.val z=true ∧ W matching b.val z=true ∧
      circuitFun 4 matching z=false := by decide +kernel

def shorter : Circuit := ⟨[G .and 0 2,G .and 1 3,G .or 4 5],6⟩
theorem matching_has_short_repair : shorter.size < matching.size ∧
    (∀ z : Fin 4 → Bool, circuitFun 4 shorter z = circuitFun 4 matching z) ∧
    (∀ j : Fin 3, (gateAt shorter j.val).op=.and → ∀ z : Fin 4 → Bool,
      W shorter (4+j.val) z=true → circuitFun 4 shorter z=true) := by decide +kernel

end Obstruction3321

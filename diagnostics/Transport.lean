import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace Transport3338
set_option maxHeartbeats 1600000 in
theorem transfer : let F (x : Fin 9 → Bool) := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)));
    let R (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 6];
    let T (x : Fin 8 → Bool) := let n := tableIndex x; ([18369897887404062920,18446740762289764600,18446744073709551560,18446744073709551608] : List ℕ).getD (n / 64) 0 |>.testBit (n % 64);
    let I (b : Bool) (x : Fin 8 → Bool) := [x 1,x 0,x 4,x 7,x 5,x 2,b,x 6,x 3,x 1 || b];
    ∀ C : Circuit, (∀ x, C.eval (I false x)=T x) →
    (∀ x, C.eval (I true x)=(T x || x 0 || x 3)) → ∀ z, C.eval (R z)=F z := by
  intro F R T I C low high z
  let a (z : Fin 9 → Bool) : Fin 8 → Bool := ![z 1,z 0,z 5,z 8,z 2,z 4,z 7,z 3]
  have bank : R z = I (z 6) (a z) := by simp [R,I,a,List.ofFn_succ]
  have geom : ∀ x : Fin 9 → Bool, (if x 6 then T (a x) || a x 0 || a x 3 else T (a x)) = F x := by
    intro x
    have tab : x = ![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] := by funext i; fin_cases i <;> rfl
    rw [tab]
    generalize x 0 = a0
    generalize x 1 = a1
    generalize x 2 = a2
    generalize x 3 = a3
    generalize x 4 = a4
    generalize x 5 = a5
    generalize x 6 = a6
    generalize x 7 = a7
    generalize x 8 = a8
    revert a0 a1 a2 a3 a4 a5 a6 a7 a8
    decide +kernel
  rw [bank,← geom]
  cases h : z 6
  · exact low (a z)
  · exact high (a z)
end Transport3338

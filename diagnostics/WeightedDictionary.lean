import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.WeightedDictionary
open Finset
open scoped BigOperators

/-- A list of slots covering each outstanding cell must pay its full nonnegative weight. -/
theorem price {X : Type} [Fintype X] {m : Nat} (w : X → Nat)
    (covered : Fin m → X → Prop) [∀ j x,Decidable (covered j x)]
    (hit : ∀x,∃j,covered j x) (bound : Nat)
    (cap : ∀j,(∑x,if covered j x then w x else 0)≤bound) : ∑x,w x≤m*bound := by
  have each (x : X) : w x≤∑j : Fin m, if covered j x then w x else 0 := by
    obtain ⟨j,h⟩ := hit x
    have one := Finset.single_le_sum (f:=fun j : Fin m => if covered j x then w x else 0)
      (fun i (_ : i∈(univ : Finset (Fin m))) => Nat.zero_le _) (mem_univ j)
    simpa only [if_pos h] using one
  calc
    ∑x,w x ≤ ∑x,∑j : Fin m,if covered j x then w x else 0 := sum_le_sum (fun x _ => each x)
    _ = ∑j : Fin m,∑x,if covered j x then w x else 0 := sum_comm
    _ ≤ ∑_j : Fin m,bound := sum_le_sum (fun j _ => cap j)
    _ = m*bound := by simp

/-- With weights constant on flag orbits, the price bound for each representative
also bounds every separately transformed copy chosen by the physical cover. -/
theorem transport {X : Type} [Fintype X] [DecidableEq X] {D : Type}
    (w : X→Nat) (part : D→Finset X) (limit : Nat)
    (base : ∀d,∑x∈part d,w x≤limit) {m : Nat}
    (d : Fin m→D) (p : Fin m→Equiv.Perm X)
    (stationary : ∀j x,w (p j x)=w x)
    (hit : ∀x,∃j,x∈(part (d j)).image (p j)) :
    ∑x,w x≤m*limit := by
  apply price w (fun j x => x∈(part (d j)).image (p j)) hit limit
  intro j
  let S := (part (d j)).image (p j)
  have cut : (∑x : X,if x∈S then w x else 0)=∑x∈S,w x := by
    rw [← sum_filter]
    simp
  rw [show (∑x : X,if x∈(part (d j)).image (p j) then w x else 0)=∑x∈S,w x from cut]
  unfold S
  rw [sum_image (fun a _ b _ e => (p j).injective e)]
  simpa only [stationary] using base (d j)
end PEqualNP.Outside.L_meta_10007.WeightedDictionary

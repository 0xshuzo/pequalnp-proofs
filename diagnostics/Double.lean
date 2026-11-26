import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9804_aux
def above (r : Nat → Nat → Prop) [DecidableRel r] (t : Finset Nat) (i : Nat) :=
  t.filter (fun j => r i j)
def below (r : Nat → Nat → Prop) [DecidableRel r] (s : Finset Nat) (j : Nat) :=
  s.filter (fun i => r i j)
theorem counted (t : Finset Nat) (p : Nat → Prop) [DecidablePred p] :
    (t.filter p).card = ∑ i∈t, (if p i then 1 else 0) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    by_cases h : p a <;> simp [Finset.filter_insert,ha,h,ih,Nat.add_comm]
theorem double {s t : Finset Nat} (r : Nat → Nat → Prop) [DecidableRel r] :
    (∑ i∈s, (above r t i).card) = ∑ j∈t, (below r s j).card := by
  simp only [above,below,counted]
  exact Finset.sum_comm
end PEqualNP.Outside.L_meta_9804_aux


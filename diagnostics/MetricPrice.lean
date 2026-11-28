import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10007.MetricPrice
open Finset
open scoped BigOperators

/-- A binary code supplies an additive quotient syndrome, with weighted distance to
    its kernel. An erased subset can have smaller syndrome distance than the whole
    box, but its saving in weight pays the difference. -/
theorem marginal {G : Type} [AddCommGroup G] (d : G→ℤ)
    (tri : ∀x y,d (x+y)≤d x + d y) {old piece smaller cut : G}
    (recover : old=(old-smaller)+smaller)
    (split : smaller=piece+cut)
    {whole fee lost : ℤ} (decomp : whole=fee+lost) (removed : d cut≤lost) :
    fee+d old-d (old-smaller) ≤ whole+d piece := by
  have a:=tri (old-smaller) smaller
  rw [←recover] at a
  have b:=tri piece cut
  rw [←split] at b
  omega

/-- Both orders bound the same combined saving. -/
theorem doubleScreen {f g f' g' paid required : ℤ}
    (orderA : paid≤f+g') (orderB : paid≤f'+g) (needed : required≤paid) :
    2*required≤(f+g)+(f'+g') := by omega

abbrev V := Fin 31
abbrev Box := Finset V × Finset V

def mark (r : Box) (i j : V) : Nat := if i∈r.1 ∧ j∈r.2 then 1 else 0
def count {k : Nat} (s : Fin k→Box) (i j : V) := ∑t,mark (s t) i j
def weight (w : V→V→Nat) (r : Box) := ∑j : V,∑i : V,w i j*mark r i j

theorem paidMass {k : Nat} (s : Fin k→Box) (w : V→V→Nat) :
    (∑j : V,∑i : V,w i j*count s i j)=∑t,weight w (s t) := by
  simp only [count,weight,Finset.mul_sum]
  calc
    _ = ∑j : V,∑t : Fin k,∑i : V,w i j*mark (s t) i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def gap (r m : Nat) := if m%2=r then 0 else 1
theorem point (r m : Nat) (bit : r≤1) (paid : r≤m) : r+gap r m≤m := by
  unfold gap
  split <;> omega

theorem coverDistance {k : Nat} (s : Fin k→Box) (w z : V→V→Nat)
    (one : ∀i j,z i j≤1) (covers : ∀i j,z i j≤count s i j)
    (L : V→Nat) (distance : ∀j,L j≤∑i : V,w i j*gap (z i j) (count s i j)) :
    (∑j : V,∑i : V,w i j*z i j)+(∑j : V,L j)≤∑t,weight w (s t) := by
  have localPay (i j : V) := Nat.mul_le_mul_left (w i j)
    (point (z i j) (count s i j) (one i j) (covers i j))
  have h:=Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ =>
    Finset.sum_le_sum (s:=(univ : Finset V)) (fun i _ => localPay i j))
  simp_rw [Nat.mul_add,Finset.sum_add_distrib] at h
  rw [paidMass] at h
  have dd:=Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ => distance j)
  exact (Nat.add_le_add_left dd _).trans h

end PEqualNP.Outside.L_meta_10007.MetricPrice

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.WeightedSpan
open Finset
open scoped BigOperators
abbrev V := Fin 31
abbrev Box := Finset V × Finset V

def cell (r : Box) (i j : V) : Nat := if i∈r.1 ∧ j∈r.2 then 1 else 0
def multiplicity {k : Nat} (R : Fin k → Box) (i j : V) : Nat := ∑t,cell (R t) i j
def cost (w : V→V→Nat) (r : Box) := ∑j : V,∑i : V,w i j*cell r i j

theorem swapWeighted {k : Nat} (w : V→V→Nat) (R : Fin k→Box) :
    (∑j : V,∑i : V,w i j*multiplicity R i j) = ∑t,cost w (R t) := by
  unfold multiplicity cost
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑j : V,∑t : Fin k,∑i : V,w i j*cell (R t) i j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem weightedObstruction {k : Nat} (R : Fin k → Box) (w : V→V→Nat)
    (B : V→V→Bool) (dead : ∀i j,B i j=true → w i j=0)
    (cover : ∀i j,B i j=false → 1≤multiplicity R i j)
    (M : Nat) (price : ∀t,cost w (R t)≤M)
    (P : V→Nat) (parity : ∀j,(∑i : V,w i j*(multiplicity R i j%2))≤P j) :
    2*(∑j : V,∑i : V,w i j) ≤ k*M+∑j : V,P j := by
  have point (i j : V) : 2*w i j ≤ w i j*multiplicity R i j + w i j*(multiplicity R i j%2) := by
    cases hit : B i j
    · have pos:=cover i j hit
      have fact : 2≤multiplicity R i j + multiplicity R i j%2 := by omega
      calc
        2*w i j = w i j*2 := Nat.mul_comm _ _
        _ ≤ w i j*(multiplicity R i j + multiplicity R i j%2) := Nat.mul_le_mul_left _ fact
        _ = _ := Nat.mul_add _ _ _
    · simp [dead i j hit]
  have s := Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ =>
    Finset.sum_le_sum (s:=(univ : Finset V)) (fun i _ => point i j))
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum] at s
  rw [swapWeighted] at s
  have a := Finset.sum_le_sum (s:=(univ : Finset (Fin k))) (fun t _ => price t)
  have b := Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ => parity j)
  have ha : (∑t,cost w (R t))≤k*M := by simpa [Nat.mul_comm] using a
  exact s.trans (Nat.add_le_add ha b)
end PEqualNP.Outside.L_meta_10007.WeightedSpan

import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_10007.ErasedWeighted

open Finset
open scoped BigOperators
abbrev V := Fin 31
abbrev Box := Finset V × Finset V
def cell (r : Box) (i j : V) : Nat := if i∈r.1 ∧ j∈r.2 then 1 else 0
def load {k : Nat} (S : Fin k→Box) (i j : V) := ∑t,cell (S t) i j
def fee (w : V→V→ℤ) (r : Box) := ∑j : V,∑i : V,w i j*(cell r i j : ℤ)
def demand (w : V→V→ℤ) (need : V→V→Bool) (i j : V) := if need i j then w i j else 0
def signed (w : V→V→ℤ) (need : V→V→Bool) (i j : V) := if need i j then w i j else -w i j

theorem columnMass {k : Nat} (S : Fin k→Box) (w : V→V→ℤ) :
    (∑j : V,∑i : V,w i j*(load S i j : ℤ))=∑t,fee w (S t) := by
  simp only [load,fee,Nat.cast_sum,Finset.mul_sum]
  calc
    _ = ∑j : V,∑t : Fin k,∑i : V,w i j*(cell (S t) i j : ℤ) := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem residualBound {k : Nat} (S : Fin k→Box) (w : V→V→ℤ) (pos : ∀i j,0≤w i j)
    (need : V→V→Bool) (cover : ∀i j,need i j=true → 1≤load S i j)
    (M : ℤ) (cap : ∀t,fee w (S t)≤M)
    (P : V→ℤ) (code : ∀j,(∑i : V,signed w need i j*(↑(load S i j%2) : ℤ))≤P j) :
    2*(∑j : V,∑i : V,demand w need i j)≤(k : ℤ)*M+∑j : V,P j := by
  have point (i j : V) :
      2*demand w need i j≤w i j*(load S i j : ℤ)+signed w need i j*(↑(load S i j%2) : ℤ) := by
    cases h : need i j
    · have ord : load S i j%2≤load S i j := Nat.mod_le _ _
      have t := mul_le_mul_of_nonneg_left (by exact_mod_cast ord :
        (↑(load S i j%2) : ℤ)≤(load S i j : ℤ)) (pos i j)
      simp only [demand,signed,h,Bool.false_eq_true,if_false,mul_zero,neg_mul]
      linarith
    · have p:=cover i j h
      have ord : 2≤load S i j+load S i j%2 := by omega
      have t:=mul_le_mul_of_nonneg_left (by exact_mod_cast ord :
        (2 : ℤ)≤(load S i j : ℤ)+(↑(load S i j%2) : ℤ)) (pos i j)
      simp only [demand,signed,h,if_true]
      simpa [mul_add,mul_comm] using t
  have s:=Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ =>
    Finset.sum_le_sum (s:=(univ : Finset V)) (fun i _ => point i j))
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum] at s
  rw [columnMass] at s
  have a:=Finset.sum_le_sum (s:=(univ : Finset (Fin k))) (fun t _ => cap t)
  have b:=Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ => code j)
  have c : (∑t,fee w (S t))≤(k : ℤ)*M := by simpa using a
  exact s.trans (add_le_add c b)

end PEqualNP.Outside.L_meta_10007.ErasedWeighted

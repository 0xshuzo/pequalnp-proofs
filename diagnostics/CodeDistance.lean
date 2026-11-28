import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10007.CodeDistance
open Finset
open scoped BigOperators
abbrev V := Fin 31
abbrev Box := Finset V × Finset V

def cell (s : Box) (i j : V) : Nat :=
  if i∈s.1 ∧ j∈s.2 then 1 else 0

def load {k : Nat} (S : Fin k → Box) (i j : V) : Nat :=
  ∑t,cell (S t) i j

def target (B : V → V → Bool) (i j : V) : Nat := if B i j then 0 else 1

theorem oneBox (s : Box) : (∑j : V,∑i : V,cell s i j)=s.1.card*s.2.card := by
  classical
  have each (j : V) : (∑i : V,cell s i j)=(if j∈s.2 then s.1.card else 0) := by
    by_cases h : j∈s.2
    · simp [cell,h]
    · simp [cell,h]
  simp_rw [each]
  simp [Nat.mul_comm]

theorem totalMass {k : Nat} (S : Fin k → Box) :
    (∑j : V,∑i : V,load S i j)=∑t,(S t).1.card*(S t).2.card := by
  unfold load
  simp_rw [Finset.sum_comm (s:=univ) (t:=(univ : Finset (Fin k)))]
  simp_rw [oneBox]

theorem noCheapCover {k h : Nat} (B : V → V → Bool) (S : Fin k→Box) (E : Fin h→Box)
    (mass : (∑j : V,∑i : V,target B i j)=775)
    (cover : ∀i j,B i j=false → 1≤load S i j+load E i j)
    (parity : ∀j, (∑i : V,load S i j%2)≤20)
    (pure : ∀t,(S t).1.card*(S t).2.card≤49)
    (rest : ∀t,(E t).1.card*(E t).2.card≤60) :
    930 ≤ 49*k+120*h := by
  have localPay (i j : V) : 2*target B i j ≤ load S i j+(load S i j%2)+2*load E i j := by
    cases z : B i j
    · have cov:=cover i j z
      simp only [target,z,Bool.false_eq_true,if_false]
      omega
    · simp [target,z]
  have whole := Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ =>
    Finset.sum_le_sum (s:=(univ : Finset V)) (fun i _ => localPay i j))
  simp_rw [Finset.sum_add_distrib,←Finset.mul_sum] at whole
  rw [mass,totalMass,totalMass] at whole
  have a := Finset.sum_le_sum (s:=(univ : Finset (Fin k))) (fun t _ => pure t)
  have b := Finset.sum_le_sum (s:=(univ : Finset (Fin h))) (fun t _ => rest t)
  have c := Finset.sum_le_sum (s:=(univ : Finset V)) (fun j _ => parity j)
  simp at a b c
  omega

theorem twoExceptions {k h : Nat} (budget : k+h≤17) (payment : 930≤49*k+120*h) : 2≤h := by omega

end PEqualNP.Outside.L_meta_10007.CodeDistance

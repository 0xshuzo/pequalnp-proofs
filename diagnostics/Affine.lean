import Mathlib

namespace Affine3576

def primeAt : Fin 9 → ℕ := ![2,3,5,7,11,13,17,19,23]

theorem small_separated {y z : ℤ} (hy : 0≤y) (hz : 0≤z) (uy : y<50000000) (uz : z<50000000)
    (eq : ∀ i, y%(primeAt i : ℤ) = z%(primeAt i : ℤ)) : y=z := by
  have e0 : y%2 = z%2 := eq (0 : Fin 9)
  have h0 : y-z=2*(y/2-z/2) := by omega
  have e1 : y%3 = z%3 := eq (1 : Fin 9)
  have h1 : y-z=3*(y/3-z/3) := by omega
  have e2 : y%5 = z%5 := eq (2 : Fin 9)
  have h2 : y-z=5*(y/5-z/5) := by omega
  have e3 : y%7 = z%7 := eq (3 : Fin 9)
  have h3 : y-z=7*(y/7-z/7) := by omega
  have e4 : y%11 = z%11 := eq (4 : Fin 9)
  have h4 : y-z=11*(y/11-z/11) := by omega
  have e5 : y%13 = z%13 := eq (5 : Fin 9)
  have h5 : y-z=13*(y/13-z/13) := by omega
  have e6 : y%17 = z%17 := eq (6 : Fin 9)
  have h6 : y-z=17*(y/17-z/17) := by omega
  have e7 : y%19 = z%19 := eq (7 : Fin 9)
  have h7 : y-z=19*(y/19-z/19) := by omega
  have e8 : y%23 = z%23 := eq (8 : Fin 9)
  have h8 : y-z=23*(y/23-z/23) := by omega
  let Q : ℤ := (-11)*(y/2-z/2) + (2)*(y/3-z/3) + (4)*(y/5-z/5) + (3)*(y/7-z/7) + (7)*(y/11-z/11) + (7)*(y/13-z/13) + (14)*(y/17-z/17) + (14)*(y/19-z/19) + (20)*(y/23-z/23)
  have h : y-z=223092870*Q := by
    dsimp only [Q]
    linear_combination (-1227010785)*h0 + (148728580)*h1 + (178474296)*h2 + (95611230)*h3 + (141968190)*h4 + (120126930)*h5 + (183723540)*h6 + (164384220)*h7 + (193993800)*h8
  omega

abbrev ModBlock := (i : Fin 9) × (Fin (primeAt i) × Fin (primeAt i))

theorem mod_count : Fintype.card ModBlock = 1556 := by
  change Fintype.card (Sigma fun i : Fin 9 => Fin (primeAt i) × Fin (primeAt i)) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fin]
  decide

abbrev Point := Fin 5000 × Fin 50000000
abbrev Line := Fin 5000 × Fin 25000000

def onLine (P : Point) (A : Line) : Prop := (P.2.val : ℤ) = (A.1.val : ℤ)*P.1.val + A.2.val

theorem four {P Q : Point} {A B : Line} (pA : onLine P A) (pB : onLine P B)
    (qA : onLine Q A) (qB : onLine Q B) : P=Q ∨ A=B := by
  obtain ⟨x,y⟩ := P
  obtain ⟨w,z⟩ := Q
  obtain ⟨a,b⟩ := A
  obtain ⟨c,e⟩ := B
  change (y.val : ℤ)=(a.val : ℤ)*x.val+b.val at pA
  change (y.val : ℤ)=(c.val : ℤ)*x.val+e.val at pB
  change (z.val : ℤ)=(a.val : ℤ)*w.val+b.val at qA
  change (z.val : ℤ)=(c.val : ℤ)*w.val+e.val at qB
  have prod : ((a.val : ℤ)-c.val)*((x.val : ℤ)-w.val)=0 := by
    linear_combination -pA + pB + qA - qB
  rcases mul_eq_zero.mp prod with ac|xw
  · right
    have ea : a=c := Fin.ext (by omega)
    subst c
    apply Prod.ext rfl
    exact Fin.ext (by omega)
  · left
    have ex : x=w := Fin.ext (by omega)
    subst w
    apply Prod.ext rfl
    exact Fin.ext (by omega)

noncomputable def incidentPoint (A : Line) (x : Fin 5000) : Point :=
  (x,⟨A.1.val*x.val+A.2.val,by
    have u : A.1.val*x.val ≤ 4999*4999 := Nat.mul_le_mul (by have := A.1.isLt; omega) (by have := x.isLt; omega)
    have v := A.2.isLt
    omega⟩)

theorem incident_correct (A : Line) (x : Fin 5000) : onLine (incidentPoint A x) A := by
  change ((A.1.val*x.val+A.2.val : ℕ) : ℤ) = _
  simp only [Nat.cast_add,Nat.cast_mul]

theorem card_margin : (Fintype.card Point + Fintype.card Line + 2)*(1556+2) < Fintype.card (Line × Fin 5000) := by
  simp only [Fintype.card_prod,Fintype.card_fin]
  decide

end Affine3576

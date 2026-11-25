import PEqualNP.Gct.Helpers.Sigma4Space

namespace Gct232Star
noncomputable section
abbrev E := Fin 4 × Fin 4 → ℂ

def star (u v : ℂ) : E := fun p =>
  (![![0,u,v,-u-v],![u,0,0,0],![v,0,0,0],![-u-v,0,0,0]] : Fin 4 → Fin 4 → ℂ) p.1 p.2

def W (a b c d e f g h : ℂ) : E := fun p =>
  (![![a,0,0,b],![0,c,d,e],![0,d,f,g],![b,e,g,h]] : Fin 4 → Fin 4 → ℂ) p.1 p.2

def perm (t : E) := Matrix.permanent (Matrix.of fun (i j : Fin 4) => (1:ℂ) + t (i,j))

def c1 (a b c d e f g h u v : ℂ) : ℂ :=
  6 * a + 12 * b + c * u^2 - 4 * c * u + 6 * c + 2 * d * u * v - 4 * d * u - 4 * d * v + 12 * d - 2 * e * u^2 - 2 * e * u * v + 4 * e * v + 12 * e + f * v^2 - 4 * f * v + 6 * f - 2 * g * u * v + 4 * g * u - 2 * g * v^2 + 12 * g + h * u^2 + 2 * h * u * v + 4 * h * u + h * v^2 + 4 * h * v + 6 * h

def c2 (a b c d e f g h u v : ℂ) : ℂ :=
  2 * a * c + 4 * a * d + 4 * a * e + 2 * a * f + 4 * a * g + 2 * a * h + 2 * b^2 - 2 * b * c * u + 4 * b * c - 2 * b * d * u - 2 * b * d * v + 8 * b * d + 2 * b * e * u + 2 * b * e * v + 4 * b * e - 2 * b * f * v + 4 * b * f + 2 * b * g * u + 2 * b * g * v + 4 * b * g + c * f * u^2 + 2 * c * f * u * v - 2 * c * f * u + c * f * v^2 - 2 * c * f * v + 2 * c * f - 2 * c * g * u * v - 2 * c * g * u - 2 * c * g * v^2 + 4 * c * g + c * h * v^2 + 2 * c * h * v + 2 * c * h + d^2 * u^2 + 2 * d^2 * u * v - 2 * d^2 * u + d^2 * v^2 - 2 * d^2 * v + 2 * d^2 - 2 * d * e * u * v - 2 * d * e * u - 2 * d * e * v^2 + 4 * d * e - 2 * d * g * u^2 - 2 * d * g * u * v - 2 * d * g * v + 4 * d * g + 2 * d * h * u * v + 2 * d * h * u + 2 * d * h * v + 4 * d * h + e^2 * v^2 + 2 * e^2 * v + 2 * e^2 - 2 * e * f * u^2 - 2 * e * f * u * v - 2 * e * f * v + 4 * e * f + 2 * e * g * u * v + 2 * e * g * u + 2 * e * g * v + 4 * e * g + f * h * u^2 + 2 * f * h * u + 2 * f * h + g^2 * u^2 + 2 * g^2 * u + 2 * g^2

def c3 (a b c d e f g h u v : ℂ) : ℂ :=
  a * c * f + 2 * a * c * g + a * c * h + a * d^2 + 2 * a * d * e + 2 * a * d * g + 2 * a * d * h + a * e^2 + 2 * a * e * f + 2 * a * e * g + a * f * h + a * g^2 + b^2 * c + 2 * b^2 * d + b^2 * f - 2 * b * c * f * u - 2 * b * c * f * v + 2 * b * c * f + 2 * b * c * g * v + 2 * b * c * g - 2 * b * d^2 * u - 2 * b * d^2 * v + 2 * b * d^2 + 2 * b * d * e * v + 2 * b * d * e + 2 * b * d * g * u + 2 * b * d * g + 2 * b * e * f * u + 2 * b * e * f + c * f * h + c * g^2 + d^2 * h + 2 * d * e * g + e^2 * f

def c4 (a b c d e f g h u v : ℂ) : ℂ :=
  a * c * f * h + a * c * g^2 + a * d^2 * h + 2 * a * d * e * g + a * e^2 * f + b^2 * c * f + b^2 * d^2

set_option maxHeartbeats 1800000 in
theorem expand (a b c d e f g h u v z : ℂ) :
    perm (star u v + z • W a b c d e f g h) = 24 + z * c1 a b c d e f g h u v +
    z^2 * c2 a b c d e f g h u v + z^3 * c3 a b c d e f g h u v + z^4 * c4 a b c d e f g h u v := by
  simp [perm, PEqualNP.Gct.Helpers.Sigma4Space.permanent_four, star, W, c1,c2,c3,c4]
  <;> ring

theorem coeffs {A B C D : ℂ} (h : ∀ z : ℂ, 24 + z*A + z^2*B + z^3*C + z^4*D = 24) :
    A=0 ∧ B=0 ∧ C=0 ∧ D=0 := by
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination (h (-2) - 8 * h (-1) + 8 * h 1 - h 2) / 12
  · linear_combination (-(h (-2)) + 16 * h (-1) + 16 * h 1 - h 2) / 24
  · linear_combination (-(h (-2)) + 2 * h (-1) - 2 * h 1 + h 2) / 12
  · linear_combination (h (-2) - 4 * h (-1) - 4 * h 1 + h 2) / 24

set_option maxHeartbeats 1200000 in
theorem zero_normal (a b c d e f g h : ℂ)
    (level : ∀ u v z : ℂ, perm (star u v + z • W a b c d e f g h) = 24) :
    W a b c d e f g h = 0 := by
  have eqs (u v : ℂ) := coeffs (A:=c1 a b c d e f g h u v) (B:=c2 a b c d e f g h u v)
    (C:=c3 a b c d e f g h u v) (D:=c4 a b c d e f g h u v)
    (fun z => (expand a b c d e f g h u v z).symm.trans (level u v z))
  have k0 := (eqs 0 0).1
  dsimp [c1] at k0
  have k1 := (eqs 1 0).1
  dsimp [c1] at k1
  have k2 := (eqs (-1) 0).1
  dsimp [c1] at k2
  have k3 := (eqs 0 1).1
  dsimp [c1] at k3
  have k4 := (eqs 0 (-1)).1
  dsimp [c1] at k4
  have k5 := (eqs 1 1).1
  dsimp [c1] at k5
  have l0 : c - h = 0 := by linear_combination (-2 : ℂ) / 3 * k0 + (5 : ℂ) / 12 * k1 + (1 : ℂ) / 4 * k2 + (1 : ℂ) / 3 * k3 + (-1 : ℂ) / 3 * k5
  have l1 : d - h = 0 := by linear_combination (5 : ℂ) / 6 * k0 + (-3 : ℂ) / 8 * k1 + (-1 : ℂ) / 8 * k2 + (-3 : ℂ) / 8 * k3 + (-1 : ℂ) / 8 * k4 + (1 : ℂ) / 6 * k5
  have l2 : e - h = 0 := by linear_combination (1 : ℂ) / 6 * k0 + (-1 : ℂ) / 24 * k1 + (-1 : ℂ) / 8 * k2 + (1 : ℂ) / 6 * k3 + (-1 : ℂ) / 6 * k5
  have l3 : f - h = 0 := by linear_combination (-2 : ℂ) / 3 * k0 + (1 : ℂ) / 3 * k1 + (5 : ℂ) / 12 * k3 + (1 : ℂ) / 4 * k4 + (-1 : ℂ) / 3 * k5
  have l4 : g - h = 0 := by linear_combination (1 : ℂ) / 6 * k0 + (1 : ℂ) / 6 * k1 + (-1 : ℂ) / 24 * k3 + (-1 : ℂ) / 8 * k4 + (-1 : ℂ) / 6 * k5
  have l5 : a + 2 * b + 9 * h = 0 := by linear_combination (-5 : ℂ) / 6 * k0 + (-1 : ℂ) / 4 * k1 + (1 : ℂ) / 4 * k2 + (-1 : ℂ) / 4 * k3 + (1 : ℂ) / 4 * k4 + (1 : ℂ) / 1 * k5
  have pc : c=h := by linear_combination l0
  have pd : d=h := by linear_combination l1
  have pe : e=h := by linear_combination l2
  have pf : f=h := by linear_combination l3
  have pg : g=h := by linear_combination l4
  have pa : a = -2*b-9*h := by linear_combination l5
  have q := (eqs 0 0).2.1
  have r := (eqs 0 0).2.2.1
  simp only [c2,c3,pa,pc,pd,pe,pf,pg] at q r
  have h2 : b^2-6*b*h-63*h^2=0 := by linear_combination q / 2
  have h3 : h^3=0 := by linear_combination (r - 4*h*h2)/96
  have hz : h=0 := (pow_eq_zero_iff (by decide : (3:ℕ)≠0)).mp h3
  have bz : b=0 := by
    have : b^2=0 := by simpa [hz] using h2
    exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp this
  funext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [W,pa,pc,pd,pe,pf,pg,bz,hz]

end
end Gct232Star

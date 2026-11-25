import Mathlib
namespace Sparse238
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

noncomputable def kill (a : ℕ) (p : K[X]) : K[X] := X * derivative p - C (a : K) * p

theorem killCoeff (p : K[X]) (a j : ℕ) :
    (kill a p).coeff j = ((j:K) - (a:K))*p.coeff j := by
  cases j with
  | zero => simp [kill]
  | succ j =>
    simp only [kill,coeff_sub,coeff_X_mul,coeff_derivative,coeff_C_mul]
    push_cast
    ring

theorem step (p : K[X]) (x : K) (a k : ℕ)
    (h : (X-C x)^(k+1) ∣ p) : (X-C x)^k ∣ kill a p := by
  obtain ⟨q,rfl⟩ := h
  refine ⟨X*(C (((k+1:ℕ):K))*q + (X-C x)*derivative q) - C (a:K)*(X-C x)*q,?_⟩
  unfold kill
  rw [derivative_mul,derivative_pow]
  simp only [Nat.add_sub_cancel,derivative_sub,derivative_X,derivative_C,sub_zero,mul_one,pow_succ]
  ring

theorem singletonCase (p : K[X]) (a : ℕ) (hk : kill a p=0) :
    p=C (p.coeff a)*X^a := by
  ext j
  by_cases eq : a=j
  · subst j
    simp [coeff_C_mul_X_pow]
  · have h := killCoeff p a j
    rw [hk,coeff_zero] at h
    have hj : (j : K)≠(a:K) := by exact_mod_cast Ne.symm eq
    have z : p.coeff j=0 := (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hj)
    simp [coeff_C_mul_X_pow,eq,Ne.symm eq,z]

theorem count (x : K) (hx : x≠0) (k : ℕ) (p : K[X]) (hp : p≠0)
    (multiple : (X-C x)^k ∣ p) : k < p.support.card := by
  classical
  have nonempty (f : K[X]) (hf : f≠0) : f.support.Nonempty := by
    by_contra h
    apply hf
    ext i
    by_contra hi
    exact h ⟨i,Polynomial.mem_support_iff.mpr (by simpa using hi)⟩
  induction k generalizing p with
  | zero => exact Finset.card_pos.mpr (nonempty _ hp)
  | succ k ih =>
    obtain ⟨a,ha⟩ := nonempty _ hp
    have neq : kill a p≠0 := by
      intro z
      have hv : p.eval x=0 := by
        obtain ⟨q,hq⟩ := multiple
        simp [hq]
      have form := singletonCase p a z
      have ev := congrArg (Polynomial.eval x) form
      rw [hv] at ev
      simp only [eval_mul,eval_C,eval_pow,eval_X] at ev
      exact (mul_ne_zero (Polynomial.mem_support_iff.mp ha) (pow_ne_zero _ hx)) ev.symm
    have subset : (kill a p).support ⊆ p.support.erase a := by
      intro j hj
      have hk := Polynomial.mem_support_iff.mp hj
      rw [killCoeff] at hk
      have nz := mul_ne_zero_iff.mp hk
      apply Finset.mem_erase.mpr
      exact ⟨fun e => nz.1 (by rw [e]; exact sub_self _),Polynomial.mem_support_iff.mpr nz.2⟩
    have lt := ih _ neq (step p x a k multiple)
    have small := Finset.card_le_card subset
    have cut := Finset.card_erase_add_one ha
    omega

theorem bound (x : K) (hx : x≠0) (p : K[X]) (hp : p≠0) :
    p.rootMultiplicity x < p.support.card := by
  apply count x hx _ p hp
  exact Polynomial.pow_rootMultiplicity_dvd p x
end Sparse238
namespace Binary238
open Polynomial
variable {K : Type*} [Field K] [IsAlgClosed K]

noncomputable def lin (a b : K) (u v : K[X]) := C a*u + C b*v

theorem quad (a b c : K) (u v : K[X]) :
    ∃ a₁ b₁ a₂ b₂ : K,
      C a*u^2+C b*u*v+C c*v^2 = lin a₁ b₁ u v*lin a₂ b₂ u v := by
  by_cases ha : a=0
  · exact ⟨0,1,b,c,by simp [ha,lin] <;> ring⟩
  let f : K[X] := C a*X^2+C b*X+C c
  have top : f.coeff 2=a := by simp [f,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  have deg : f.degree≠0 := by
    intro hz
    have eq := eq_C_of_degree_le_zero (le_of_eq hz)
    have bad := congrArg (fun z : K[X] => z.coeff 2) eq
    change f.coeff 2=(C (f.coeff 0)).coeff 2 at bad
    rw [top] at bad
    exact ha (by simpa [coeff_C] using bad)
  obtain ⟨r,hr⟩ := (IsAlgClosed.splits f).exists_eval_eq_zero deg
  have eqn : a*r^2+b*r+c=0 := by simpa [f] using hr
  have hc : c= -(r*(b+a*r)) := by linear_combination eqn
  refine ⟨1,-r,a,b+a*r,?_⟩
  rw [hc]
  simp [lin] <;> ring

theorem cubic (a b c d : K) (u v : K[X]) :
    ∃ a₁ b₁ a₂ b₂ a₃ b₃ : K,
      C a*u^3+C b*u^2*v+C c*u*v^2+C d*v^3 =
      lin a₁ b₁ u v*lin a₂ b₂ u v*lin a₃ b₃ u v := by
  by_cases ha : a=0
  · obtain ⟨e,f,g,h,fac⟩ := quad b c d u v
    refine ⟨e,f,g,h,0,1,?_⟩
    rw [←fac]
    simp [ha,lin] <;> ring
  let f : K[X] := C a*X^3+C b*X^2+C c*X+C d
  have top : f.coeff 3=a := by simp [f,coeff_add,coeff_C_mul,coeff_X_pow,coeff_X,coeff_C]
  have deg : f.degree≠0 := by
    intro hz
    have eq := eq_C_of_degree_le_zero (le_of_eq hz)
    have bad := congrArg (fun z : K[X] => z.coeff 3) eq
    change f.coeff 3=(C (f.coeff 0)).coeff 3 at bad
    rw [top] at bad
    exact ha (by simpa [coeff_C] using bad)
  obtain ⟨r,hr⟩ := (IsAlgClosed.splits f).exists_eval_eq_zero deg
  have eqn : a*r^3+b*r^2+c*r+d=0 := by simpa [f] using hr
  have hd : d= -(r*(c+b*r+a*r^2)) := by linear_combination eqn
  obtain ⟨e,f',g,h,fac⟩ := quad a (b+a*r) (c+b*r+a*r^2) u v
  refine ⟨e,f',g,h,1,-r,?_⟩
  rw [←fac,hd]
  simp [lin] <;> ring
end Binary238
namespace Pencil238
open Polynomial
variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem supportLin (a b : K) (u v : K[X]) (su : u.support.card≤4) (sv : v.support.card≤4) :
    (Binary238.lin a b u v).support.card≤8 := by
  classical
  have base : (Binary238.lin a b u v).support ⊆ (C a*u).support ∪ (C b*v).support :=
    Polynomial.support_add
  have leg (t : K) (z : K[X]) : (C t*z).support ⊆ z.support := by
    intro j hj
    have nz := Polynomial.mem_support_iff.mp hj
    rw [coeff_C_mul] at nz
    exact Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul nz)
  have st := (Finset.card_le_card base).trans (Finset.card_union_le _ _)
  have z0 := Finset.card_le_card (leg a u)
  have z1 := Finset.card_le_card (leg b v)
  omega

theorem algebraic (u v : K[X]) (su : u.support.card≤4) (sv : v.support.card≤4)
    (e d s : Fin 3 → K) (x : K) (hx : x≠0)
    (nz : (∑i, C (s i) * (Binary238.lin (e i) (d i) u v)^3)≠0) :
    rootMultiplicity x (∑i, C (s i) * (Binary238.lin (e i) (d i) u v)^3)≤21 := by
  let a := ∑i,s i*(e i)^3
  let b := ∑i,3*s i*(e i)^2*d i
  let c := ∑i,3*s i*e i*(d i)^2
  let z := ∑i,s i*(d i)^3
  have ex : (∑i,C (s i)*(Binary238.lin (e i) (d i) u v)^3) =
      C a*u^3+C b*u^2*v+C c*u*v^2+C z*v^3 := by
    simp [a,b,c,z,Fin.sum_univ_three,Binary238.lin]
    ring
  obtain ⟨a₁,b₁,a₂,b₂,a₃,b₃,h⟩ := Binary238.cubic a b c z u v
  rw [ex,h] at nz ⊢
  let l1 := Binary238.lin a₁ b₁ u v
  let l2 := Binary238.lin a₂ b₂ u v
  let l3 := Binary238.lin a₃ b₃ u v
  change l1*l2*l3≠0 at nz
  have h12 := left_ne_zero_of_mul nz
  have first := Sparse238.bound x hx l1 (left_ne_zero_of_mul h12)
  have second := Sparse238.bound x hx l2 (right_ne_zero_of_mul h12)
  have third := Sparse238.bound x hx l3 (right_ne_zero_of_mul nz)
  have b1 : l1.support.card≤8 := supportLin _ _ u v su sv
  have b2 : l2.support.card≤8 := supportLin _ _ u v su sv
  have b3 : l3.support.card≤8 := supportLin _ _ u v su sv
  change rootMultiplicity x (l1*l2*l3)≤21
  rw [rootMultiplicity_mul nz,rootMultiplicity_mul h12]
  omega

theorem real (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X]) (x : ℝ) (hx : 0<x)
    (nz : (∑i, C (s i)*g i^3)≠0)
    (u v : ℝ[X]) (su : u.support.card≤4) (sv : v.support.card≤4)
    (a b : Fin 3 → ℝ) (sp : ∀i,g i=C (a i)*u+C (b i)*v) :
    rootMultiplicity x (∑i,C (s i)*g i^3)≤21 := by
  let h := Complex.ofRealHom
  let P : ℝ[X] := ∑ i,C (s i)*g i^3
  let U := u.map h
  let V := v.map h
  have ms (f : ℝ[X]) : (f.map h).support ⊆ f.support := by
    intro j hj
    apply Polynomial.mem_support_iff.mpr
    intro z
    have n := Polynomial.mem_support_iff.mp hj
    rw [coeff_map,z,map_zero] at n
    exact n rfl
  have keep : P.map h≠0 := by
    intro z
    apply nz
    change P=0
    ext j
    have v := congrArg (fun f : ℂ[X] => f.coeff j) z
    simpa [h,coeff_map] using v
  have eqn : P.map h=∑i,C (h (s i))*(Binary238.lin (h (a i)) (h (b i)) U V)^3 := by
    simp [P,U,V,sp,Binary238.lin,Fin.sum_univ_three]
  have bound := algebraic U V ((Finset.card_le_card (ms u)).trans su)
    ((Finset.card_le_card (ms v)).trans sv) (fun i => h (a i)) (fun i => h (b i)) (fun i => h (s i))
    (h x) (by change (x:ℂ)≠0; exact_mod_cast hx.ne') (eqn ▸ keep)
  rw [←eqn] at bound
  have lift : rootMultiplicity x P ≤ rootMultiplicity (h x) (P.map h) := by
    apply (le_rootMultiplicity_iff keep).2
    obtain ⟨q,eq⟩ := pow_rootMultiplicity_dvd P x
    refine ⟨q.map h,?_⟩
    simpa using congrArg (fun f : ℝ[X] => f.map h) eq
  exact lift.trans bound
end Pencil238

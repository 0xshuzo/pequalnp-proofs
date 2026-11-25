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
namespace Tangent238
open Polynomial
abbrev Poly := ℝ[X]
noncomputable def avg (t : ℝ) (p q : Poly) := C t*p+C (1-t)*q
noncomputable def diff (p q : Poly) := p-q
noncomputable def normal (t : ℝ) (p q h : Poly) := h-avg t p q
noncomputable def form (t : ℝ) (p q h : Poly) := C t*p^3+C (1-t)*q^3-h^3

theorem balance (x : ℝ) (A B : Poly) (a : A≠0) (b : B≠0) (f : A-B≠0)
    (left : rootMultiplicity x A < rootMultiplicity x (A-B))
    (right : rootMultiplicity x B < rootMultiplicity x (A-B)) :
    rootMultiplicity x A=rootMultiplicity x B := by
  by_contra ne
  rcases lt_or_gt_of_ne ne with lt|lt
  · let k := rootMultiplicity x A+1
    have d1 : (X-C x)^k ∣ A-B := (le_rootMultiplicity_iff f).mp left
    have d2 : (X-C x)^k ∣ B := (le_rootMultiplicity_iff b).mp lt
    have d3 := dvd_add d1 d2
    rw [sub_add_cancel] at d3
    have z := (le_rootMultiplicity_iff a).mpr d3
    change rootMultiplicity x A+1≤rootMultiplicity x A at z
    omega
  · let k := rootMultiplicity x B+1
    have d1 : (X-C x)^k ∣ A-B := (le_rootMultiplicity_iff f).mp right
    have d2 : (X-C x)^k ∣ A := (le_rootMultiplicity_iff a).mp lt
    have d3 := dvd_sub d2 d1
    have eqn : A-(A-B)=B := by ring
    rw [eqn] at d3
    have z := (le_rootMultiplicity_iff b).mpr d3
    change rootMultiplicity x B+1≤rootMultiplicity x B at z
    omega

theorem curr (t x : ℝ) (p q h : Poly) (px : p.eval x=1) (qx : q.eval x=1)
    (hx : h.eval x=1) (nonx : x≠0) (pos : t≠0) (other : 1-t≠0)
    (diffNZ : diff p q≠0) (normNZ : normal t p q h≠0)
    (nD : (diff p q).support.card≤8) (nT : (normal t p q h).support.card≤12)
    (nz : form t p q h≠0) (high : 22≤rootMultiplicity x (form t p q h)) :
    1≤rootMultiplicity x (diff p q) ∧ rootMultiplicity x (diff p q)≤5 ∧
    rootMultiplicity x (normal t p q h)=2*rootMultiplicity x (diff p q) := by
  let D := diff p q
  let A := avg t p q
  let T := normal t p q h
  let L := C (t*(1-t))*(3*A+C (1-2*t)*D)
  let R := 3*A^2+3*A*T+T^2
  have one : A.eval x=1 := by simp [A,avg,px,qx]
  have dz : D.eval x=0 := by simp [D,diff,px,qx]
  have tz : T.eval x=0 := by simpa [T,normal,hx] using (sub_eq_zero.mpr one.symm : 1-A.eval x=0)
  have lval : L.eval x≠0 := by simp [L,one,dz,pos,other]
  have rval : R.eval x≠0 := by simp [R,one,tz]
  have lNZ : L≠0 := fun eq => lval (by simp [eq])
  have rNZ : R≠0 := fun eq => rval (by simp [eq])
  have eqn : form t p q h=(D*D)*L-T*R := by
    have two : (C (2:ℝ) : ℝ[X])=2 := Polynomial.C_eq_natCast 2
    simp [form,D,A,T,L,R,avg,normal,diff,two] <;> ring
  have dNZ : D*D≠0 := mul_ne_zero diffNZ diffNZ
  have aNZ := mul_ne_zero dNZ lNZ
  have bNZ := mul_ne_zero normNZ rNZ
  have aord : rootMultiplicity x (D*D*L)=2*rootMultiplicity x D := by
    rw [rootMultiplicity_mul aNZ,rootMultiplicity_mul dNZ,rootMultiplicity_eq_zero lval]
    omega
  have bord : rootMultiplicity x (T*R)=rootMultiplicity x T := by
    rw [rootMultiplicity_mul bNZ,rootMultiplicity_eq_zero rval,Nat.add_zero]
  have vD := Sparse238.bound x nonx _ diffNZ
  have vT := Sparse238.bound x nonx _ normNZ
  change rootMultiplicity x D < _ at vD
  change rootMultiplicity x T < _ at vT
  rw [eqn] at nz high
  have eq := balance x (D*D*L) (T*R) aNZ bNZ nz (by rw [aord]; omega) (by rw [bord]; omega)
  rw [aord,bord] at eq
  have d1 : 1≤rootMultiplicity x D := by
    apply (le_rootMultiplicity_iff diffNZ).mpr
    simpa only [pow_one] using (dvd_iff_isRoot.mpr dz : X-C x ∣ D)
  change 1≤rootMultiplicity x D ∧ rootMultiplicity x D≤5 ∧ rootMultiplicity x T=2*rootMultiplicity x D
  omega
end Tangent238

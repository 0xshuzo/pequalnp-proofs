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
namespace Euler238
open Polynomial
variable {K : Type*} [Field K] [CharZero K]

noncomputable def iter : ℕ → K[X] → K[X]
  | 0,p => p
  | k+1,p => iter k (Sparse238.kill 0 p)

theorem coefficient (k : ℕ) (p : K[X]) (j : ℕ) :
    (iter k p).coeff j = (j:K)^k*p.coeff j := by
  induction k generalizing p with
  | zero => simp [iter]
  | succ k ih => rw [iter,ih,Sparse238.killCoeff]; simp [pow_succ]; ring

theorem add (k : ℕ) (a b : K[X]) : iter k (a+b)=iter k a+iter k b := by
  ext i
  simp [coefficient,coeff_add,mul_add]

theorem fsum {I : Type*} (T : Finset I) (p : I → K[X]) (k : ℕ) :
    iter k (∑i∈T,p i)=∑i∈T,iter k (p i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp; ext j; simp [coefficient]
  | insert i T hi ih => simp [hi,add,ih]

theorem mon (t : K) (a k : ℕ) :
    iter k (C t*X^a)=C ((a:K)^k*t)*X^a := by
  ext j
  rw [coefficient,coeff_C_mul_X_pow,coeff_C_mul_X_pow]
  by_cases h : j=a <;> simp [h]

theorem vanishing (p : K[X]) (x : K) (k : ℕ) (dv : (X-C x)^(k+1)∣p) : (iter k p).eval x=0 := by
  induction k generalizing p with
  | zero =>
    obtain ⟨f,h⟩ := dv
    simp [iter,h]
  | succ k ih =>
    exact ih _ (Sparse238.step p x 0 (k+1) dv)

theorem full {I : Type*} (T : Finset I) (w : I → K) (e : I → ℕ) (p : K[X]) (x : K)
    (reps : p=∑i∈T,C (w i)*X^(e i))
    (nz : p≠0) (k : ℕ) (high : k<rootMultiplicity x p) :
    ∑i∈T,((e i:K)^k*w i)*x^(e i)=0 := by
  have h := vanishing p x k ((le_rootMultiplicity_iff nz).mp high)
  rw [reps,fsum] at h
  simpa only [mon,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] using h

theorem triple {I : Type*} (T : Finset I) (s : K) (w : I → K) (e : I → ℕ) :
    C s*(∑i∈T,C (w i)*X^(e i))^3 =
    ∑i∈T,∑j∈T,∑h∈T,C (s*w i*w j*w h)*X^(e i+e j+e h) := by
  simp only [pow_succ,pow_zero,one_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro h hh
  simp [pow_add]
  ring

theorem cubeMoments (s : Fin 3 → K) (g : Fin 3 → K[X]) (x : K) (k : ℕ)
    (nz : (∑i,C (s i)*g i^3)≠0) (high : k<rootMultiplicity x (∑i,C (s i)*g i^3)) :
    ∑i,∑a∈(g i).support,∑b∈(g i).support,∑c∈(g i).support,
      ((a+b+c:ℕ):K)^k*(s i*(g i).coeff a*(g i).coeff b*(g i).coeff c)*x^(a+b+c)=0 := by
  have v := vanishing _ x k ((le_rootMultiplicity_iff nz).mp high)
  have term (i : Fin 3) : C (s i)*g i^3=
      ∑a∈(g i).support,∑b∈(g i).support,∑c∈(g i).support,
      C (s i*(g i).coeff a*(g i).coeff b*(g i).coeff c)*X^(a+b+c) := by
    have d : g i=∑a∈(g i).support,C ((g i).coeff a)*X^a := by
      first | exact (g i).as_sum_support_C_mul_X_pow | exact?
    conv_lhs => rw [d]
    exact triple _ _ _ _ 
  simp only [term,fsum,mon,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X] at v
  exact v
end Euler238
namespace ExactJet238
open Polynomial Euler238
variable {K : Type*} [Field K] [CharZero K]

theorem leading (x : K) (n : ℕ) (q : K[X]) :
    (iter n ((X-C x)^n*q)).eval x=(n.factorial:K)*x^n*q.eval x := by
  induction n generalizing q with
  | zero => simp [iter]
  | succ n ih =>
    have remove : Sparse238.kill 0 ((X-C x)^(n+1)*q) =
        (X-C x)^n*(X*(C (((n+1:ℕ):K))*q+(X-C x)*derivative q)) := by
      unfold Sparse238.kill
      rw [derivative_mul,derivative_pow]
      simp only [Nat.add_sub_cancel,derivative_sub,derivative_X,derivative_C,sub_zero,
        mul_one,pow_succ,Nat.cast_zero,map_zero,zero_mul]
      ring
    rw [iter,remove,ih]
    simp [Nat.factorial_succ,pow_succ] <;> ring

theorem criterion (p : K[X]) (nz : p≠0) (x : K) (hx : x≠0) (n : ℕ) :
    n≤rootMultiplicity x p ↔ ∀k<n,(iter k p).eval x=0 := by
  constructor
  · intro hi k hk
    exact vanishing p x k ((le_rootMultiplicity_iff nz).mp (by omega))
  · intro hv
    by_contra! lt
    let r := rootMultiplicity x p
    obtain ⟨q,hq⟩ := pow_rootMultiplicity_dvd p x
    have neq : q.eval x≠0 := by
      intro z
      have qd : X-C x ∣ q := dvd_iff_isRoot.mpr z
      obtain ⟨t,ht⟩ := qd
      have large : (X-C x)^(r+1) ∣ p := by
        refine ⟨t,?_⟩
        calc
          p = (X-C x)^r*q := hq
          _ = (X-C x)^(r+1)*t := by rw [ht,pow_succ]; ring
      have bound := (le_rootMultiplicity_iff nz).mpr large
      change r+1≤r at bound
      omega
    have atRoot := hv r lt
    have hterm : p=(X-C x)^r*q := hq
    have hvv : (iter r ((X-C x)^r*q)).eval x=0 := by
      exact (congrArg (fun z : K[X] => (iter r z).eval x) hterm).symm.trans atRoot
    rw [leading] at hvv
    have nf : (r.factorial:K)≠0 := by exact_mod_cast (Nat.factorial_ne_zero r)
    exact (mul_ne_zero (mul_ne_zero nf (pow_ne_zero r hx)) neq) hvv
end ExactJet238

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
namespace Sharp238
open Polynomial
abbrev Poly := ℝ[X]
noncomputable def mix (u : ℝ) (p q : Poly) := C u*p+C (1-u)*q
noncomputable def f (t : ℝ) (p q h : Poly) := C t*p^3+C (1-t)*q^3-h^3
noncomputable def dval (p q : Poly) := p-q

theorem subSet (p q : Poly) : (p-q).support ⊆ p.support ∪ q.support := by
  intro j hj
  by_contra no
  have z1 : p.coeff j=0 := by by_contra n; exact no (Finset.mem_union_left _ (Polynomial.mem_support_iff.mpr n))
  have z2 : q.coeff j=0 := by by_contra n; exact no (Finset.mem_union_right _ (Polynomial.mem_support_iff.mpr n))
  exact (Polynomial.mem_support_iff.mp hj) (by simp [z1,z2])

theorem unionSix (t : ℝ) (p q : Poly) (tz : t≠0) (tone : 1-t≠0)
    (ps : p.support.card≤4) (qs : q.support.card≤4) (hs : (mix t p q).support.card≤4) :
    (p.support ∪ q.support).card≤6 := by
  classical
  let A := p.support
  let B := q.support
  have sub : (A∪B)\(A∩B) ⊆ (mix t p q).support := by
    intro j hj
    obtain ⟨hu,hi⟩ := Finset.mem_sdiff.mp hj
    apply Polynomial.mem_support_iff.mpr
    change (C t*p+C (1-t)*q).coeff j≠0
    rw [coeff_add,coeff_C_mul,coeff_C_mul]
    rcases Finset.mem_union.mp hu with hp|hq
    · have hn : j∉B := fun h => hi (Finset.mem_inter.mpr ⟨hp,h⟩)
      have v : q.coeff j=0 := by by_contra h; exact hn (Polynomial.mem_support_iff.mpr h)
      simpa [v] using mul_ne_zero tz (Polynomial.mem_support_iff.mp hp)
    · have hn : j∉A := fun h => hi (Finset.mem_inter.mpr ⟨h,hq⟩)
      have v : p.coeff j=0 := by by_contra h; exact hn (Polynomial.mem_support_iff.mpr h)
      simpa [v] using mul_ne_zero tone (Polynomial.mem_support_iff.mp hq)
  have inc : A∩B ⊆ A∪B := by intro j hj; exact Finset.mem_union_left _ (Finset.mem_inter.mp hj).1
  have cap := (Finset.card_le_card sub).trans hs
  have cnt := Finset.card_sdiff_add_card_eq_card inc
  have sum := Finset.card_union_add_card_inter A B
  change A.card≤4 at ps
  change B.card≤4 at qs
  change (A∪B).card≤6
  omega

theorem line (t u x : ℝ) (p q : Poly) (xx : x≠0) (tz : t≠0) (tone : 1-t≠0)
    (px : p.eval x=1) (qx : q.eval x=1) (ps : p.support.card≤4) (qs : q.support.card≤4)
    (hs : (mix u p q).support.card≤4) (nz : f t p q (mix u p q)≠0) :
    rootMultiplicity x (f t p q (mix u p q))≤10 := by
  let D := p-q
  have replace : p=q+D := by dsimp [D]; ring
  have dx : D.eval x=0 := by simp [D,px,qx]
  have dn : D≠0 := by
    intro z
    apply nz
    have eqp : p=q := by rw [replace,z,add_zero]
    simp [f,mix,eqp] <;> ring
  have lo := Sparse238.bound x xx D dn
  have dcap := Finset.card_le_card (subSet p q)
  change D.support.card≤(p.support∪q.support).card at dcap
  have two : (C (2:ℝ):Poly)=2 := Polynomial.C_eq_natCast 2
  have three : (C (3:ℝ):Poly)=3 := Polynomial.C_eq_natCast 3
  by_cases equal : u=t
  · subst u
    let L := 3*C (t*(1-t))*q+C (t*(1-t^2))*D
    have factor : f t p q (mix t p q)= D*D*L := by
      simp [f,mix,L,D,two,three] <;> ring
    have lv : L.eval x≠0 := by simp [L,dx,qx,tz,tone]
    have ln : L≠0 := fun h => lv (by simp [h])
    have dn2 := mul_ne_zero dn dn
    have cap := unionSix t p q tz tone ps qs hs
    rw [factor,rootMultiplicity_mul (mul_ne_zero dn2 ln),rootMultiplicity_mul dn2,rootMultiplicity_eq_zero lv]
    omega
  · let L := 3*C (t-u)*q^2+3*C (t-u^2)*q*D+C (t-u^3)*D^2
    have factor : f t p q (mix u p q)=D*L := by
      simp [f,mix,L,D,two,three] <;> ring
    have lv : L.eval x≠0 := by simp [L,dx,qx,sub_ne_zero.mpr equal.symm]
    have ln : L≠0 := fun h => lv (by simp [h])
    have cap := Finset.card_union_le p.support q.support
    rw [factor,rootMultiplicity_mul (mul_ne_zero dn ln),rootMultiplicity_eq_zero lv]
    omega
end Sharp238

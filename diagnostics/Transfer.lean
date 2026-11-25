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
namespace Mixed238
open Polynomial
abbrev P := ℝ[X]

theorem pure (x : ℝ) (n : ℕ) : rootMultiplicity x ((X-C x)^n)=n := by
  classical
  have px : (X-C x : P)≠0 := X_sub_C_ne_zero x
  induction n with
  | zero => simp [rootMultiplicity_eq_zero]
  | succ n ih =>
    rw [pow_succ,rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n px) px),ih,rootMultiplicity_X_sub_C]
    simp

theorem unpack (p : P) (x : ℝ) (nz : p≠0) (r : ℕ) (hp : rootMultiplicity x p=r) :
    ∃v,(p=(X-C x)^r*v) ∧ v.eval x≠0 := by
  have d := pow_rootMultiplicity_dvd p x
  rw [hp] at d
  obtain ⟨v,hv⟩ := d
  refine ⟨v,hv,?_⟩
  intro z
  obtain ⟨t,ht⟩ := (dvd_iff_isRoot.mpr z : X-C x∣v)
  have d : (X-C x)^(r+1)∣p := ⟨t,by rw [hv,ht,pow_succ];ring⟩
  have h := (le_rootMultiplicity_iff nz).mpr d
  omega

theorem cubeOrder (p : P) (x : ℝ) (nz : p≠0) :
    rootMultiplicity x (p^3)=3*rootMultiplicity x p := by
  have a := mul_ne_zero nz nz
  have b := mul_ne_zero a nz
  have eq : p^3=p*p*p := by ring
  rw [eq,rootMultiplicity_mul b,rootMultiplicity_mul a]
  omega

theorem quadOrder (p q : P) (x : ℝ) (pn : p≠0) (qn : q≠0) (r : ℕ)
    (pr : rootMultiplicity x p=r) (qr : rootMultiplicity x q=r) :
    p^2-p*q+q^2≠0 ∧ rootMultiplicity x (p^2-p*q+q^2)=2*r := by
  obtain ⟨v,pv,vx⟩ := unpack p x pn r pr
  obtain ⟨w,qw,wx⟩ := unpack q x qn r qr
  let U := v^2-v*w+w^2
  have ux : U.eval x≠0 := by
    simp only [U,eval_add,eval_sub,eval_pow,eval_mul]
    nlinarith [sq_nonneg (v.eval x-2*w.eval x),sq_pos_of_ne_zero vx]
  have un : U≠0 := fun e => ux (by simp [e])
  have fac : p^2-p*q+q^2=(X-C x)^(r+r)*U := by rw [pv,qw,pow_add];dsimp [U];ring
  have prod := mul_ne_zero (pow_ne_zero (r+r) (X_sub_C_ne_zero x)) un
  rw [fac]
  exact ⟨prod,by rw [rootMultiplicity_mul prod,pure,rootMultiplicity_eq_zero ux];omega⟩

theorem forced (p q h : P) (x : ℝ) (xx : x≠0) (ps : p.support.card≤4)
    (qs : q.support.card≤4) (hs : h.support.card≤4) (pn : p≠0) (qn : q≠0) (hn : h≠0)
    (r c : ℕ) (pr : rootMultiplicity x p=r) (qr : rootMultiplicity x q=r)
    (hr : rootMultiplicity x h=c) (nz : p^3+q^3-h^3≠0)
    (high : 22≤rootMultiplicity x (p^3+q^3-h^3)) :
    p+q≠0 ∧ rootMultiplicity x (p+q)+2*r=3*c ∧ rootMultiplicity x (p+q)≤7 := by
  have capP := Sparse238.bound x xx p pn
  have capH := Sparse238.bound x xx h hn
  have co := cubeOrder h x hn
  have hc : h^3≠0 := pow_ne_zero 3 hn
  have div : (X-C x)^22∣p^3+q^3-h^3 := (le_rootMultiplicity_iff nz).mp high
  have nu : p+q≠0 := by
    intro z
    have fac : p^3+q^3=(p+q)*(p^2-p*q+q^2) := by ring
    rw [fac,z,zero_mul,zero_sub] at div
    have dl : (X-C x)^22∣h^3 := by simpa using div
    have bad := (le_rootMultiplicity_iff hc).mpr dl
    omega
  obtain ⟨nn,order⟩ := quadOrder p q x pn qn r pr qr
  have fac : p^3+q^3=(p+q)*(p^2-p*q+q^2) := by ring
  have nt : p^3+q^3≠0 := fac ▸ mul_ne_zero nu nn
  have sumord : rootMultiplicity x (p^3+q^3)=rootMultiplicity x (p+q)+2*r := by
    rw [fac,rootMultiplicity_mul (mul_ne_zero nu nn),order]
  have sc : (p+q).support.card≤p.support.card+q.support.card :=
    (Finset.card_le_card Polynomial.support_add).trans (Finset.card_union_le _ _)
  have count := Sparse238.bound x xx (p+q) nu
  have same := Tangent238.balance x (p^3+q^3) (h^3) nt hc nz (by omega) (by omega)
  exact ⟨nu,by omega,by omega⟩

theorem extreme (p q : P) (x : ℝ) (xx : x≠0) (ps : p.support.card≤4)
    (qs : q.support.card≤4) (nz : p+q≠0) (top : rootMultiplicity x (p+q)=7) :
    (p+q).support.card=8 ∧ p.support.card=4 ∧ q.support.card=4 ∧ (p.support∩q.support).card=0 := by
  have lower := Sparse238.bound x xx (p+q) nz
  have a : (p+q).support.card≤(p.support∪q.support).card := Finset.card_le_card Polynomial.support_add
  have b := Finset.card_union_add_card_inter p.support q.support
  exact ⟨by omega,by omega,by omega,by omega⟩
end Mixed238
namespace TransferSing238
open Polynomial
abbrev P := ℝ[X]
noncomputable def total (s : Fin 3 → ℝ) (g : Fin 3 → P) : P := ∑i,C (s i)*(g i)^3
theorem scale (s : Fin 3 → ℝ) (g : Fin 3 → P) (B : P) :
    total s (fun i => B*g i)=B^3*total s g := by
  unfold total
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem transfer (x : ℝ) (s : Fin 3 → ℝ) (g : Fin 3 → P) (B : P)
    (bn : B≠0) (nz : total s g≠0) (gn : ∀i,g i≠0)
    (size : ∀i,(B*g i).support.card≤4)
    (ordSum : ∀i,rootMultiplicity x B+rootMultiplicity x (g i)=3)
    (three : ∀f : Fin 3 → P, (∀i,(f i).support.card≤4) →
      (∀i,rootMultiplicity x (f i)=3) → total s f≠0 → rootMultiplicity x (total s f)≤21) :
    rootMultiplicity x (total s g)+3*rootMultiplicity x B≤21 := by
  have n := mul_ne_zero (pow_ne_zero 3 bn) nz
  have non : total s (fun i => B*g i)≠0 := by rw [scale];exact n
  have allord (i : Fin 3) : rootMultiplicity x (B*g i)=3 := by
    rw [rootMultiplicity_mul (mul_ne_zero bn (gn i))]
    exact ordSum i
  have h := three (fun i => B*g i) size allord non
  rw [scale,rootMultiplicity_mul n,Mixed238.cubeOrder B x bn] at h
  omega
end TransferSing238

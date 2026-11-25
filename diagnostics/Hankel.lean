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
namespace Support238
open Polynomial
variable {K : Type*} [Field K]

theorem splitMul {p q : K[X]} {k : ℕ} (hm : k∈(p*q).support) :
    ∃a∈p.support,∃b∈q.support,a+b=k := by
  classical
  have h := Polynomial.mem_support_iff.mp hm
  rw [coeff_mul] at h
  obtain ⟨⟨a,b⟩,hab,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨a,Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hv),
    b,Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hv),by first | simpa using hab | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hab | exact?⟩

theorem label (S : Finset ℕ) (small : S.card≤4) :
    ∃ f : Fin 4 → ℕ,∀a∈S,∃i,f i=a := by
  classical
  let e := Fintype.equivFin S
  let idx (a : S) : Fin 4 := ⟨(e a).val,lt_of_lt_of_le (e a).isLt (by simpa using small)⟩
  let pick (i : Fin 4) : ℕ := if h : ∃a:S,idx a=i then (Classical.choose h).val else 0
  refine ⟨pick,?_⟩
  intro a ha
  let v : S := ⟨a,ha⟩
  have z : ∃u:S,idx u=idx v := ⟨v,rfl⟩
  refine ⟨idx v,?_⟩
  change (if h : ∃u:S,idx u=idx v then (Classical.choose h).val else 0)=a
  rw [dif_pos z]
  have same : Classical.choose z=v := e.injective (Fin.ext (congrArg (fun w : Fin 4 => w.val) (Classical.choose_spec z)))
  exact congrArg Subtype.val same

def triples : Finset (Fin 4 × Fin 4 × Fin 4) := Finset.univ.filter (fun t => t.1≤t.2.1 ∧ t.2.1≤t.2.2)
theorem number : triples.card=20 := by decide +kernel

theorem ordered (f : Fin 4 → ℕ) (i j k : Fin 4) :
    ∃t∈triples, f t.1+f t.2.1+f t.2.2=f i+f j+f k := by
  have pick (a b c : Fin 4) (ab : a≤b) (bc : b≤c)
      (eqn : f a+f b+f c=f i+f j+f k) : ∃t∈triples,f t.1+f t.2.1+f t.2.2=f i+f j+f k :=
    ⟨(a,b,c),Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,bc⟩,eqn⟩
  rcases le_total i j with ij|ji
  · rcases le_total j k with jk|kj
    · exact pick i j k ij jk rfl
    · rcases le_total i k with ik|ki
      · exact pick i k j ik kj (by omega)
      · exact pick k i j ki ij (by omega)
  · rcases le_total i k with ik|ki
    · exact pick j i k ji ik (by omega)
    · rcases le_total j k with jk|kj
      · exact pick j k i jk ki (by omega)
      · exact pick k j i kj ji (by omega)

theorem cube (p : K[X]) (small : p.support.card≤4) : (p^3).support.card≤20 := by
  classical
  obtain ⟨f,repr⟩ := label p.support small
  let total (t : Fin 4 × Fin 4 × Fin 4) := f t.1+f t.2.1+f t.2.2
  have sub : (p^3).support ⊆ triples.image total := by
    intro k hk
    have eqn : p^3=(p*p)*p := by ring
    rw [eqn] at hk
    obtain ⟨u,hu,c,hc,e⟩ := splitMul hk
    obtain ⟨a,ha,b,hb,ab⟩ := splitMul hu
    obtain ⟨i,hi⟩ := repr a ha
    obtain ⟨j,hj⟩ := repr b hb
    obtain ⟨l,hl⟩ := repr c hc
    obtain ⟨t,ht,ts⟩ := ordered f i j l
    exact Finset.mem_image.mpr ⟨t,ht,by change f t.1+f t.2.1+f t.2.2=k; omega⟩
  have bound := (Finset.card_le_card sub).trans Finset.card_image_le
  simpa [number] using bound

theorem constantMul (s : K) (p : K[X]) : (C s*p).support⊆p.support := by
  intro j hj
  apply Polynomial.mem_support_iff.mpr
  have h := Polynomial.mem_support_iff.mp hj
  rw [coeff_C_mul] at h
  exact right_ne_zero_of_mul h

theorem terms (s : Fin 3 → K) (g : Fin 3 → K[X]) (small : ∀i,(g i).support.card≤4) :
    (∑i,C (s i)*g i^3).support.card≤60 := by
  classical
  let S (i : Fin 3) := (g i^3).support
  have sub : (∑ i,C (s i)*g i^3).support⊆Finset.univ.biUnion S := by
    intro j hj
    have h := Polynomial.mem_support_iff.mp hj
    have some : ∃i,(C (s i)*g i^3).coeff j≠0 := by
      by_contra! z
      exact h (by simp [Fin.sum_univ_three,coeff_add,z])
    obtain ⟨i,hc⟩ := some
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,constantMul _ _ (Polynomial.mem_support_iff.mpr hc)⟩
  calc
    _ ≤ (Finset.univ.biUnion S).card := Finset.card_le_card sub
    _ ≤ ∑i, (S i).card := Finset.card_biUnion_le
    _ ≤ ∑_i : Fin 3,20 := Finset.sum_le_sum (fun i _ => cube _ (small i))
    _ = 60 := by decide

end Support238
namespace Unique238
open Polynomial
abbrev Poly := ℝ[X]

theorem subcap (p q : Poly) : (p-q).support.card≤p.support.card+q.support.card := by
  classical
  have sub : (p-q).support⊆p.support∪q.support := by
    intro j hj
    by_contra no
    have zeroP : p.coeff j=0 := by by_contra hc; exact no (Finset.mem_union_left _ (Polynomial.mem_support_iff.mpr hc))
    have zeroQ : q.coeff j=0 := by by_contra hc; exact no (Finset.mem_union_right _ (Polynomial.mem_support_iff.mpr hc))
    exact (Polynomial.mem_support_iff.mp hj) (by simp [zeroP,zeroQ])
  exact (Finset.card_le_card sub).trans (Finset.card_union_le _ _)

theorem unique (x : ℝ) (hx : x≠0) (T p q : Poly) (pp : p.support.card≤4) (qq : q.support.card≤4)
    (unit : p.eval x≠0) (hp : (X-C x)^8 ∣ T-p^3) (hq : (X-C x)^8 ∣ T-q^3) : p=q := by
  by_contra ne
  let U := p^2+p*q+q^2
  have val : U.eval x≠0 := by
    simp only [U,eval_add,eval_pow,eval_mul]
    have positive : 0<(p.eval x)^2 := sq_pos_of_ne_zero unit
    nlinarith [sq_nonneg (p.eval x+2*q.eval x)]
  have unz : U≠0 := fun e => val (by simp [e])
  have eq : (T-q^3)-(T-p^3)=(p-q)*U := by dsimp [U]; ring
  have dv := dvd_sub hq hp
  rw [eq] at dv
  have pn := sub_ne_zero.mpr ne
  have h := (le_rootMultiplicity_iff (mul_ne_zero pn unz)).mpr dv
  rw [rootMultiplicity_mul (mul_ne_zero pn unz),rootMultiplicity_eq_zero val,Nat.add_zero] at h
  have max := Sparse238.bound x hx _ pn
  have card := subcap p q
  omega

noncomputable def mu (p : Poly) (x : ℝ) (n : ℕ) := ∑j∈p.support,((j:ℝ)^n*p.coeff j)*x^j

theorem recur (p : Poly) (sp : p.support.card≤4) (x : ℝ) :
  ∃ a b c d : ℕ, ∀ n : ℕ,
    mu p x (n+4) = ((a:ℝ)+b+c+d)*mu p x (n+3)
       -((a:ℝ)*b+a*c+a*d+(b:ℝ)*c+b*d+(c:ℝ)*d)*mu p x (n+2)
       +((a:ℝ)*b*c+a*b*d+a*c*d+(b:ℝ)*c*d)*mu p x (n+1)
       -(a:ℝ)*b*c*d*mu p x n := by
  classical
  obtain ⟨f,hf⟩ := Support238.label p.support sp
  refine ⟨f 0,f 1,f 2,f 3,?_⟩
  intro n
  let a : ℝ := f 0
  let b : ℝ := f 1
  let c : ℝ := f 2
  let d : ℝ := f 3
  change mu p x (n+4)=(a+b+c+d)*mu p x (n+3)-(a*b+a*c+a*d+b*c+b*d+c*d)*mu p x (n+2)+
    (a*b*c+a*b*d+a*c*d+b*c*d)*mu p x (n+1)-a*b*c*d*mu p x n
  unfold mu
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have zero : ((j:ℝ)-a)*(j-b)*(j-c)*(j-d)=0 := by
    obtain ⟨i,ri⟩ := hf j hj
    fin_cases i <;> simp [a,b,c,d,←ri]
  simp only [pow_add]
  linear_combination ((j:ℝ)^n*p.coeff j*x^j)*zero
end Unique238
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
namespace Hankel238
open Polynomial Unique238
abbrev P := ℝ[X]

theorem lift (T : P) (x a : ℝ) (av : a≠0) (tv : T.eval x=a^3) (n : ℕ) :
    ∃ v : P, v.eval x=a ∧ (X-C x)^(n+1)∣T-v^3 := by
  let Z : P := X-C x
  have zv : Z.eval x=0 := by simp [Z]
  induction n with
  | zero =>
    refine ⟨C a,by simp,?_⟩
    simpa only [Nat.zero_add,pow_one] using
      (dvd_iff_isRoot.mpr (show (T-(C a)^3).eval x=0 by simp [tv]))
  | succ n ih =>
    obtain ⟨v,vv,q,eq⟩ := ih
    change T-v^3=Z^(n+1)*q at eq
    let w : P := Z^(n+1)
    let c : ℝ := q.eval x/(3*a^2)
    let u : P := C c
    let h : P := q-3*v^2*u-3*v*w*u^2-w^2*u^3
    have wz : w.eval x=0 := by simp [w,zv]
    have hv : h.eval x=0 := by
      simp [h,u,wz,vv,c]
      field_simp [av] <;> ring
    obtain ⟨s,hs⟩ := (dvd_iff_isRoot.mpr hv : Z∣h)
    refine ⟨v+w*u,by simp [vv,wz],s,?_⟩
    calc
      T-(v+w*u)^3=w*h := by
        change T-v^3=w*q at eq
        dsimp only [h]
        linear_combination eq
      _ = (X-C x)^(n+1+1)*s := by rw [hs,pow_succ]; dsimp only [w,Z]; ring

theorem compareJet (x : ℝ) (T p v : P) (v0 : v.eval x≠0) (n : ℕ)
    (vp : (X-C x)^n∣T-v^3) (pp : (X-C x)^n∣T-p^3) : (X-C x)^n∣p-v := by
  by_cases eq : p=v
  · simp [eq]
  let Q : P := p^2+p*v+v^2
  have qv : Q.eval x≠0 := by
    simp only [Q,eval_add,eval_pow,eval_mul]
    nlinarith [sq_nonneg (2*p.eval x+v.eval x),sq_pos_of_ne_zero v0]
  have qnz : Q≠0 := fun e => qv (by simp [e])
  have prod : (T-v^3)-(T-p^3)=(p-v)*Q := by dsimp [Q]; ring
  have d := dvd_sub vp pp
  rw [prod] at d
  have pn := sub_ne_zero.mpr eq
  have h := (le_rootMultiplicity_iff (mul_ne_zero pn qnz)).mpr d
  rw [rootMultiplicity_mul (mul_ne_zero pn qnz),rootMultiplicity_eq_zero qv,Nat.add_zero] at h
  exact (le_rootMultiplicity_iff pn).mp h

theorem moments (p : P) (x : ℝ) (n : ℕ) :
    (Euler238.iter n p).eval x=mu p x n := by
  have eq : p=∑i∈p.support,C (p.coeff i)*X^i := by
    first | exact p.as_sum_support_C_mul_X_pow | exact?
  conv_lhs => rw [eq,Euler238.fsum]
  simp only [Euler238.mon,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,mu]

theorem same (x : ℝ) (T p v : P) (v0 : v.eval x≠0) (n : ℕ)
    (vp : (X-C x)^n∣T-v^3) (pp : (X-C x)^n∣T-p^3) :
    ∀k<n,mu p x k=mu v x k := by
  intro k hk
  have both := compareJet x T p v v0 n vp pp
  have div : (X-C x)^(k+1)∣p-v := dvd_trans (pow_dvd_pow _ (by omega)) both
  have zero := Euler238.vanishing (p-v) x k div
  have lin : Euler238.iter k (p-v)=Euler238.iter k p-Euler238.iter k v := by
    ext i
    simp [Euler238.coefficient,coeff_sub,mul_sub]
  rw [lin,eval_sub,moments,moments,sub_eq_zero] at zero
  exact zero

theorem obstruction (x : ℝ) (T p v : P) (v0 : v.eval x≠0) (n b : ℕ) (sp : p.support.card≤4)
    (vp : (X-C x)^n∣T-v^3) (enough : b+8<n)
    (c : Fin 5 → ℝ) (low : ∀j<4, ∑i : Fin 5,c i*mu v x (b+i.val+j)=0)
    (high : (∑i : Fin 5,c i*mu v x (b+i.val+4))≠0) :
    ¬ (X-C x)^n∣T-p^3 := by
  intro pp
  have eqs := same x T p v v0 n vp pp
  obtain ⟨a,d,e,f,h⟩ := Unique238.recur p sp x
  let A : ℝ := (a:ℝ)+d+e+f
  let B : ℝ := (a:ℝ)*d+a*e+a*f+(d:ℝ)*e+d*f+(e:ℝ)*f
  let Cc : ℝ := (a:ℝ)*d*e+a*d*f+a*e*f+(d:ℝ)*e*f
  let D : ℝ := (a:ℝ)*d*e*f
  have recV (i : Fin 5) : mu v x (b+i.val+4)=A*mu v x (b+i.val+3)-B*mu v x (b+i.val+2)+
      Cc*mu v x (b+i.val+1)-D*mu v x (b+i.val+0) := by
    have bound := i.isLt
    have key := h (b+i.val)
    rw [eqs (b+i.val+4) (by omega),eqs (b+i.val+3) (by omega),eqs (b+i.val+2) (by omega),
      eqs (b+i.val+1) (by omega),eqs (b+i.val) (by omega)] at key
    exact key
  apply high
  calc
    _ = A*(∑i : Fin 5,c i*mu v x (b+i.val+3))-B*(∑i : Fin 5,c i*mu v x (b+i.val+2))+
        Cc*(∑i : Fin 5,c i*mu v x (b+i.val+1))-D*(∑i : Fin 5,c i*mu v x (b+i.val+0)) := by
      simp only [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [recV]
      ring
    _ = 0 := by rw [low 3 (by decide),low 2 (by decide),low 1 (by decide),low 0 (by decide)]; ring
end Hankel238

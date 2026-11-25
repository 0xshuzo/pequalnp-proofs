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
namespace Quintic238
open Polynomial Unique238
structure Five where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ

def rule (v : Five) : ℝ :=
  58*v.a^5-290*v.a^3*v.b+300*v.a^2*v.c+285*v.a*v.b^2-315*v.a*v.d-285*v.b*v.c+315*v.e

def cube (h : Five) : Five :=
  let a := h.a/4
  let b := h.b/20
  let c := h.c/120
  let d := h.d/840
  let e := h.e/6720
  ⟨3*a, 3*b+3*a^2, 3*c+6*a*b+a^3, 3*d+6*a*c+3*b^2+3*a^2*b,
    3*e+6*a*d+6*b*c+3*a^2*c+3*a*b^2⟩

def data (a b c d : ℝ) : Five :=
  let h1 := a
  let h2 := a*h1-b
  let h3 := a*h2-b*h1+c
  let h4 := a*h3-b*h2+c*h1-d
  let h5 := a*h4-b*h3+c*h2-d*h1
  ⟨h1,h2,h3,h4,h5⟩

theorem scalar (a b c d : ℝ) : rule (cube (data a b c d))=0 := by
  dsimp [rule,cube,data]
  ring

theorem realAtoms (p : ℝ[X]) (x : ℝ) (sp : p.support.card≤4)
    (z0 : mu p x 0=0) (z1 : mu p x 1=0) (z2 : mu p x 2=0) (nz : mu p x 3≠0) :
    rule (cube ⟨mu p x 4/mu p x 3,mu p x 5/mu p x 3,mu p x 6/mu p x 3,
      mu p x 7/mu p x 3,mu p x 8/mu p x 3⟩)=0 := by
  obtain ⟨i,j,k,l,hr⟩ := Unique238.recur p sp x
  let a : ℝ := (i:ℝ)+j+k+l
  let b : ℝ := (i:ℝ)*j+i*k+i*l+(j:ℝ)*k+j*l+(k:ℝ)*l
  let c : ℝ := (i:ℝ)*j*k+i*j*l+i*k*l+(j:ℝ)*k*l
  let d : ℝ := (i:ℝ)*j*k*l
  let w (n : ℕ) := mu p x n/mu p x 3
  have recW (n : ℕ) : w (n+4)=a*w (n+3)-b*w (n+2)+c*w (n+1)-d*w n := by
    dsimp only [w]
    rw [hr n]
    dsimp only [a,b,c,d]
    ring
  have q0 : w 0=0 := by simp [w,z0]
  have q1 : w 1=0 := by simp [w,z1]
  have q2 : w 2=0 := by simp [w,z2]
  have q3 : w 3=1 := div_self nz
  have q4 : w 4=a := by simpa [q0,q1,q2,q3] using recW 0
  have q5 : w 5=a*a-b := by simpa [q1,q2,q3,q4] using recW 1
  have q6 : w 6=a*(a*a-b)-b*a+c := by simpa [q2,q3,q4,q5] using recW 2
  change rule (cube ⟨w 4,w 5,w 6,w 7,w 8⟩)=0
  have q7 := recW 3
  have q8 := recW 4
  norm_num only [Nat.reduceAdd] at q7 q8
  rw [q8,q7,q6,q5,q4,q3]
  simpa only [data,mul_one] using scalar a b c d

def shift (p d : Five) (t : ℝ) : Five :=
  ⟨p.a+t*d.a,p.b+t*d.b,p.c+t*d.c,p.d+t*d.d,p.e+t*d.e⟩

theorem threeChoices (p d : Five) (p0 : rule p=0) (p1 : rule (shift p d 1)=0) :
    ∃ c b a : ℝ, ∀ t : ℝ, t≠0 → t≠1 → rule (shift p d t)=0 →
      58*d.a^5*t^3+a*t^2+b*t+c=0 := by
  let v2 : ℝ := 580*d.a^2*p.a^3 - 870*d.a^2*p.a*p.b + 300*d.a^2*p.c - 870*d.a*d.b*p.a^2 + 570*d.a*d.b*p.b + 600*d.a*d.c*p.a - 315*d.a*d.d + 285*d.b^2*p.a - 285*d.b*d.c
  let v3 : ℝ := 580*d.a^3*p.a^2 - 290*d.a^3*p.b - 870*d.a^2*d.b*p.a + 300*d.a^2*d.c + 285*d.a*d.b^2
  let v4 : ℝ := 290*d.a^4*p.a - 290*d.a^3*d.b
  let v5 : ℝ := 58*d.a^5
  refine ⟨v2+v3+v4+v5,v3+v4+v5,v4+v5,?_⟩
  intro t tn to1 ht
  have eq : rule (shift p d t)=(1-t)*rule p+t*rule (shift p d 1)+
      t*(t-1)*(58*d.a^5*t^3+(v4+v5)*t^2+(v3+v4+v5)*t+(v2+v3+v4+v5)) := by
    dsimp [rule,shift,v2,v3,v4,v5]
    ring
  rw [p0,p1,ht] at eq
  simp only [mul_zero,zero_add] at eq
  exact (mul_eq_zero.mp eq.symm).resolve_left (mul_ne_zero tn (sub_ne_zero.mpr to1))
end Quintic238

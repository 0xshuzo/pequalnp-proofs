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
namespace Quad238
open Polynomial Unique238
abbrev P := ℝ[X]

theorem squareExpansion (a b c d : ℝ) (p : P) (x : ℝ) :
  (∑j∈p.support, (((j:ℝ)^4+a*j^3+b*j^2+c*j+d)^2*(p.coeff j))*x^j)=
  mu p x 8+(2*a)*mu p x 7+(a^2+2*b)*mu p x 6+(2*a*b+2*c)*mu p x 5+
  (b^2+2*a*c+2*d)*mu p x 4+(2*b*c+2*a*d)*mu p x 3+(c^2+2*b*d)*mu p x 2+
  (2*c*d)*mu p x 1+d^2*mu p x 0 := by
  unfold mu
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

theorem gauss (p A : P) (x : ℝ) (sp : p.support.card≤4)
    (pos : ∀j∈A.support,0≤A.coeff j*x^j)
    (eq : ∀n<8,mu p x n=mu A x n) : mu p x 8 ≤ mu A x 8 := by
  obtain ⟨f,hf⟩ := Support238.label p.support sp
  let u : ℝ := f 0
  let v : ℝ := f 1
  let w : ℝ := f 2
  let z : ℝ := f 3
  let a := -(u+v+w+z)
  let b := u*v+u*w+u*z+v*w+v*z+w*z
  let c := -(u*v*w+u*v*z+u*w*z+v*w*z)
  let d := u*v*w*z
  let Q (i : ℕ) : ℝ := (i:ℝ)^4+a*i^3+b*i^2+c*i+d
  have qp (i : ℕ) (hi : i∈p.support) : Q i=0 := by
    obtain ⟨k,hk⟩ := hf i hi
    have fac : Q i=((i:ℝ)-u)*(i-v)*(i-w)*(i-z) := by dsimp [Q,a,b,c,d]; push_cast; ring
    rw [fac]
    fin_cases k <;> simp [u,v,w,z,←hk]
  have zero : (∑j∈p.support, ((Q j)^2*p.coeff j)*x^j)=0 :=
    Finset.sum_eq_zero (fun j hj => by simp [qp j hj])
  have nonneg : 0≤∑j∈A.support, ((Q j)^2*A.coeff j)*x^j := by
    apply Finset.sum_nonneg
    intro j hj
    rw [mul_assoc]
    exact mul_nonneg (sq_nonneg _) (pos j hj)
  change (∑j∈p.support, (((j:ℝ)^4+a*j^3+b*j^2+c*j+d)^2*p.coeff j)*x^j)=0 at zero
  change 0≤∑j∈A.support, (((j:ℝ)^4+a*j^3+b*j^2+c*j+d)^2*A.coeff j)*x^j at nonneg
  rw [squareExpansion] at zero nonneg
  rw [eq 7 (by decide),eq 6 (by decide),eq 5 (by decide),eq 4 (by decide),eq 3 (by decide),
    eq 2 (by decide),eq 1 (by decide),eq 0 (by decide)] at zero
  linarith
end Quad238

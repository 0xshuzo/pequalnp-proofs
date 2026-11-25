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
namespace Pade238
open Polynomial
abbrev Poly := ℝ[X]
noncomputable def E (f : Poly) := X*derivative f
noncomputable def wr (g T : Poly) := g*E T-C 3*(T*E g)
theorem supportE (p : Poly) : (E p).support⊆p.support := by
  intro i hi
  have eq : E p=Sparse238.kill 0 p := by simp [E,Sparse238.kill]
  rw [eq] at hi
  have hc := Polynomial.mem_support_iff.mp hi
  rw [Sparse238.killCoeff] at hc
  exact Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hc)

theorem wrsize (g T : Poly) : (wr g T).support.card≤g.support.card*T.support.card := by
  classical
  let S := (g.support ×ˢ T.support).image (fun e => e.1+e.2)
  have a : (g*E T).support ⊆ S := by
    intro i hi
    obtain ⟨x,hx,y,hy,xy⟩ := Support238.splitMul hi
    exact Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,supportE _ hy⟩,xy⟩
  have b : (C 3*(T*E g)).support ⊆ S := by
    intro i hi
    obtain ⟨x,hx,y,hy,xy⟩ := Support238.splitMul (Support238.constantMul 3 _ hi)
    exact Finset.mem_image.mpr ⟨(y,x),Finset.mem_product.mpr ⟨supportE _ hy,hx⟩,by omega⟩
  have inside : (wr g T).support ⊆ S := by
    intro i hi
    by_contra no
    have zero1 : (g*E T).coeff i=0 := by
      by_contra nc
      exact no (a (Polynomial.mem_support_iff.mpr nc))
    have zero2 : (C 3*(T*E g)).coeff i=0 := by
      by_contra nc
      exact no (b (Polynomial.mem_support_iff.mpr nc))
    have hc := Polynomial.mem_support_iff.mp hi
    exact hc (by simp [wr,coeff_sub,zero1,zero2])
  have small := (Finset.card_le_card inside).trans Finset.card_image_le
  simpa [Finset.card_product] using small

theorem contact (g T : Poly) (x : ℝ) (hx : x≠0) (unit : g.eval x≠0)
    (nz : T-g^3≠0) (m : ℕ) (mult : rootMultiplicity x (T-g^3)=m+1) :
    wr g T≠0 ∧ (X-C x)^m ∣ wr g T := by
  let Z : Poly := X-C x
  let F := T-g^3
  obtain ⟨q,eq⟩ := (le_rootMultiplicity_iff nz).mp (show m+1≤rootMultiplicity x (T-g^3) by omega)
  change F=Z^(m+1)*q at eq
  have qval : q.eval x≠0 := by
    intro hv
    obtain ⟨w,hw⟩ := (dvd_iff_isRoot.mpr hv : Z ∣ q)
    have big : (X-C x)^(m+2)∣F := by refine ⟨w,?_⟩; rw [eq,hw]; change _=Z^(m+1+1)*w; rw [pow_succ]; ring
    have bigger := (le_rootMultiplicity_iff nz).mpr big
    omega
  have base : wr g T=g*E F-C 3*(F*E g) := by
    have three : (C (3:ℝ):Poly)=3 := Polynomial.C_eq_natCast 3
    simp [wr,F,E,derivative_sub,derivative_pow,three] <;> ring
  let U := g*X*C ((m+1:ℕ):ℝ)*q + Z*(g*X*derivative q-C 3*(q*E g))
  have factor : wr g T=Z^m*U := by
    rw [base,eq]
    change g*(X*derivative (Z^(m+1)*q)) - C 3*(Z^(m+1)*q*E g) = Z^m*U
    rw [derivative_mul,derivative_pow]
    have dz : derivative Z=1 := by simp [Z]
    simp only [dz,Nat.add_sub_cancel,mul_one,pow_succ]
    dsimp only [U]
    ring
  have val : U.eval x≠0 := by
    have index : ((m+1:ℕ):ℝ)≠0 := by exact_mod_cast Nat.succ_ne_zero m
    have zval : Z.eval x=0 := by simp [Z]
    simpa [U,zval] using mul_ne_zero (mul_ne_zero (mul_ne_zero unit hx) index) qval
  have unz : U≠0 := fun z => val (by simp [z])
  exact ⟨factor ▸ mul_ne_zero (pow_ne_zero m (X_sub_C_ne_zero x)) unz,⟨U,factor⟩⟩

theorem bound (g T : Poly) (x : ℝ) (hx : x≠0) (unit : g.eval x≠0) (nz : T-g^3≠0) :
    rootMultiplicity x (T-g^3)≤g.support.card*T.support.card := by
  cases hm : rootMultiplicity x (T-g^3) with
  | zero => omega
  | succ m =>
    obtain ⟨nonz,div⟩ := contact g T x hx unit nz m hm
    have order := Sparse238.count x hx m _ nonz div
    have card := wrsize g T
    omega
end Pade238

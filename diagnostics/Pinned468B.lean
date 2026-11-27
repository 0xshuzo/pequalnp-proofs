import PEqualNP.Defs
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev V (m k : ℕ) := Fin m × Option (Fin k)
abbrev P (m k : ℕ) := MvPolynomial (V m k) K
abbrev Mask (m : ℕ) := Finset (Fin m)
noncomputable def part {m k : ℕ} (S : Mask m) (j : Option (Fin k)) : P m k := ∑ i∈S, X (i,j)
noncomputable def test {m k : ℕ} (S : Mask m) : P m k :=
  part S none * ∏ j : Fin k, (1 + part S (some j))
noncomputable def bools (m k : ℕ) : Set (P m k) := Set.range (fun v : V m k => X v * X v + X v)
noncomputable def pin {m k : ℕ} (S : Mask m) : Set (P m k) := {1 + part S none} ∪ Set.range (fun j : Fin k => part S (some j))
noncomputable def sys {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) : Set (P m k) :=
  bools m k ∪ Set.image (test (k:=k)) (H : Set (Mask m)) ∪ pin S
def short (m k : ℕ) : Finset (Mask m) := Finset.univ.filter (fun S => S.card≤k+1)

variable {σ τ : Type}
theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

theorem cube_sum (n : ℕ) (f : MvPolynomial (Fin n) (ZMod 2)) (hf : f.totalDegree < n) :
    ∑ x : Fin n → ZMod 2, MvPolynomial.eval x f = 0 := by
  classical
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [← Finset.mul_sum]
  have hprod : ∑ x : Fin n → ZMod 2, ∏ i, x i ^ d i = ∏ i, ∑ c : ZMod 2, c ^ d i := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hex : ∃ i, d i = 0 := by
    by_contra hno
    have hpos : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.2 (fun h => hno ⟨i, h⟩)
    have h1 := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have h2 : ∑ _i : Fin n, 1 ≤ ∑ i, d i := Finset.sum_le_sum (fun i _ => hpos i)
    simp at h2
    omega
  obtain ⟨i, hi⟩ := hex
  rw [hprod, Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
  rw [hi]
  decide

end Pool468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
def bit {m : ℕ} (S : Mask m) (i : Fin m) : K := if i∈S then 1 else 0
def probe {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) : V m k → K
  | (i,none) => (if i=p then 1 else 0) + (if i=a then z 0 else 0)
  | (i,some j) => if i=b then z j.succ else 0

theorem sumProbe_none {m k : ℕ} (R : Mask m) (p a b : Fin m) (z : Fin (k+1) → K) :
    (∑ i∈R, probe p a b z (i,none)) = bit R p + bit R a*z 0 := by
  classical
  simp [probe,Finset.sum_add_distrib,bit,ite_mul]
theorem sumProbe_some {m k : ℕ} (R : Mask m) (p a b : Fin m) (z : Fin (k+1) → K) (j : Fin k) :
    (∑ i∈R, probe p a b z (i,some j)) = bit R b*z j.succ := by
  classical
  simp [probe,bit,ite_mul]
theorem affine_sum (c v : K) : ∑ z : K, (c+v*z) = v := by revert c v; decide
theorem factors (k : ℕ) (u : K → K) (v : Fin k → K → K) :
    (∑ z : Fin (k+1) → K, u (z 0) * ∏ j : Fin k, v j (z j.succ)) =
    (∑ y : K, u y) * ∏ j : Fin k, ∑ y : K, v j y := by
  classical
  let h : Fin (k+1) → K → K := Fin.cases u v
  have eq : (∑ z : Fin (k+1) → K, ∏ i : Fin (k+1), h i (z i)) =
      ∏ i : Fin (k+1), ∑ c : K, h i c := by
    rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
  simpa only [Fin.prod_univ_succ,h,Fin.cases_zero,Fin.cases_succ] using eq

theorem profile {m k : ℕ} (hk : 0<k) (p a b : Fin m) (R : Mask m) :
    (∑ z : Fin (k+1) → K, eval (probe p a b z) (test R)) = bit R a * bit R b := by
  classical
  calc
    _ = ∑ z : Fin (k+1) → K, (bit R p + bit R a*z 0) *
        ∏ j : Fin k, (1 + bit R b*z j.succ) := by
      apply Finset.sum_congr rfl
      intro z _
      simp [test,part,sumProbe_none,sumProbe_some]
    _ = _ := by
      rw [factors k (fun c => bit R p + bit R a*c) (fun _ c => 1+bit R b*c),affine_sum]
      simp only [affine_sum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      by_cases h : b∈R
      · simp [bit,h]
      · simp [bit,h,Nat.ne_of_gt hk]

noncomputable def probePoly {m k : ℕ} (p a b : Fin m) : V m k → MvPolynomial (Fin (k+1)) K
  | (i,none) => (if i=p then 1 else 0) + (if i=a then X 0 else 0)
  | (i,some j) => if i=b then X j.succ else 0
theorem probePoly_low {m k : ℕ} (p a b : Fin m) (v : V m k) :
    (probePoly (k:=k) p a b v).totalDegree≤1 := by
  obtain ⟨i,_|j⟩ := v
  · exact (totalDegree_add _ _).trans (max_le (by split <;> simp) (by split <;> simp))
  · simp only [probePoly]; split <;> simp
theorem probePoly_eval {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) (v : V m k) :
    eval z (probePoly p a b v)=probe p a b z v := by
  obtain ⟨i,_|j⟩ := v
  · by_cases h : i=p <;> by_cases h' : i=a <;> simp only [probe,probePoly,h,h',if_pos,if_true,if_false,map_add,map_one,map_zero,eval_X]
  · by_cases h : i=b <;> simp [probe,probePoly,h]

theorem evalProbeBind {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) (f : P m k) :
    eval (probe p a b z) f = eval z (bind₁ (probePoly p a b) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add g h ig ih => simp [map_add,ig,ih]
  | mul_X g i ig => simp [map_mul,bind₁_X_right,ig,probePoly_eval]

theorem cubeLow {m k : ℕ} (p a b : Fin m) (f : P m k) (hd : f.totalDegree<k+1) :
    ∑ z : Fin (k+1) → K, eval (probe p a b z) f = 0 := by
  have cap := totalDegree_bind₁_le (probePoly p a b) (probePoly_low p a b) f
  rw [one_mul] at cap
  have van := cube_sum (k+1) (bind₁ (probePoly p a b) f) (cap.trans_lt hd)
  convert van using 1
  apply Finset.sum_congr rfl
  intro z _
  exact evalProbeBind p a b z f

end Pool468
namespace Obstruction468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev Poly (V : Type) := MvPolynomial V K
def agree {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (p : Poly V) (c : T → K) :=
  ∀ x∈Q, eval x p = ∑ i, c i * eval x (f i)
def separated {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (d : ℕ) :=
  ∀ (p : Poly V) (c : T → K), p.totalDegree<d → agree Q f p c → ∀ i, c i=0

theorem mulX_degree {V : Type} (v : V) (p : Poly V) (hp : p≠0) :
    p.totalDegree < (X v * p).totalDegree := by
  classical
  have ne : p.support.Nonempty := by
    by_contra! bad
    apply hp
    ext d
    have h : d∉p.support := by simp [bad]
    simpa using (not_ne_iff.mp (fun hn => h (mem_support_iff.mpr hn)))
  obtain ⟨e,he,eq⟩ := Finset.exists_mem_eq_sup p.support ne (fun m => m.sum (fun _ n => n))
  have step : (e+Finsupp.single v 1) ∈ (X v*p).support := by
    apply mem_support_iff.mpr
    have h := mem_support_iff.mp he
    have key : coeff (e+Finsupp.single v 1) (X v*p)=coeff e p := by
      first
      | solve | simp
      | solve | simp [mul_comm (X v) p]
      | solve | simp [X,add_comm]
      | exact?
    rwa [key]
  have more := le_totalDegree step
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at more
  change (p.support.sup (fun m => m.sum (fun _ n => n))) < _
  omega

theorem lines {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (van : ∀ a∈A, ∀ x∈Q, eval x a=0) (sep : separated Q f d)
    {p : Poly V} (h : PCDerivable (A ∪ Set.range f) d p) : ∃ c, agree Q f p c := by
  classical
  induction h with
  | ax hp _ =>
    rcases hp with a|⟨i,rfl⟩
    · exact ⟨0,fun x hx => by simpa using van _ a x hx⟩
    · refine ⟨fun j => if i=j then 1 else 0,?_⟩
      intro x hx
      simp
  | zero => exact ⟨0,fun x _ => by simp⟩
  | add _ _ il ir =>
    obtain ⟨a,ha⟩ := il
    obtain ⟨b,hb⟩ := ir
    refine ⟨a+b,?_⟩
    intro x hx
    simp only [map_add,ha x hx,hb x hx,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  | @mulX v p hp hd ih =>
    refine ⟨0,?_⟩
    intro x hx
    by_cases hn : p=0
    · simp [hn]
    · have degree := mulX_degree v p hn
      obtain ⟨c,hc⟩ := ih
      have z := sep p c (by omega) hc
      have hz : eval x p=0 := by simpa [z] using hc x hx
      simp [hz]

theorem notRefutable {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (hd : 0<d) (wit : Q.Nonempty) (van : ∀ a∈A, ∀ x∈Q, eval x a=0)
    (sep : separated Q f d) : ¬PCRefutable (A ∪ Set.range f) d := by
  intro contra
  obtain ⟨c,hc⟩ := lines Q f A d van sep contra
  have val := sep 1 c (by simpa using hd) hc
  obtain ⟨x,hx⟩ := wit
  have bad := hc x hx
  simpa [val] using bad

theorem cube_separates {V T B Z : Type} [Fintype T] [Fintype Z]
    (Q : Set (V → K)) (f : T → Poly V) (d : ℕ)
    (probe : B → Z → (V → K)) (inside : ∀ b z, probe b z∈Q)
    (low : ∀ p : Poly V, p.totalDegree < d → ∀ b, ∑ z, eval (probe b z) p=0)
    (profiles : LinearIndependent K (fun i : T => fun b : B => ∑ z, eval (probe b z) (f i))) :
    separated Q f d := by
  classical
  intro p c dp agree
  apply Fintype.linearIndependent_iff.mp profiles c
  funext b
  change (∑ i, c i • (fun b : B => ∑ z, eval (probe b z) (f i))) b = 0
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, eval (probe b z) p := Finset.sum_congr rfl (fun z _ => (agree _ (inside b z)).symm)
    _ = 0 := low p dp b
end Obstruction468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
def pinned {m k : ℕ} (S : Mask m) (x : V m k → K) :=
  (∑ i∈S, x (i,none))=1 ∧ ∀ j : Fin k, (∑ i∈S, x (i,some j))=0

theorem vanishPin {m k : ℕ} (S : Mask m) (g : P m k) (hg : g∈bools m k ∪ pin S)
    (x : V m k → K) (hx : pinned S x) : eval x g=0 := by
  rcases hg with ⟨v,rfl⟩|hg
  · have field (a : K) : a*a+a=0 := by revert a; decide
    simp [field]
  · rcases hg with h|⟨j,rfl⟩
    · have eq : g=1+part S none := h
      rw [eq]
      simp [part,hx.1] <;> decide
    · simpa [part] using hx.2 j

theorem noRefBelow {m k : ℕ} (hk : 0<k) (S : Mask m) (sne : S.Nonempty)
    (H : Finset (Mask m)) {B : Type} (a b : B → Fin m)
    (awayA : ∀ t, a t∉S) (awayB : ∀ t, b t∉S)
    (li : LinearIndependent K (fun R : H => fun t : B => bit R.val (a t)*bit R.val (b t))) :
    ¬PCRefutable (sys (k:=k) H S) (k+1) := by
  classical
  obtain ⟨p,hp⟩ := sne
  let f : H → P m k := fun R => test R.val
  let Q : Set (V m k → K) := { x | pinned S x }
  have bank : sys (k:=k) H S = (bools m k ∪ pin S) ∪ Set.range f := by
    ext g
    constructor
    · rintro ((h|⟨R,hr,rfl⟩)|h)
      exact Or.inl (Or.inl h)
      exact Or.inr ⟨⟨R,hr⟩,rfl⟩
      exact Or.inl (Or.inr h)
    · rintro ((h|h)|⟨R,rfl⟩)
      exact Or.inl (Or.inl h)
      exact Or.inr h
      exact Or.inl (Or.inr ⟨R.val,R.property,rfl⟩)
  rw [bank]
  apply Obstruction468.notRefutable Q f (bools m k ∪ pin S) (k+1) (by omega)
  · refine ⟨probe p p p (fun _ : Fin (k+1) => 0),?_⟩
    constructor
    · rw [sumProbe_none]; simp [bit,hp]
    · intro j; rw [sumProbe_some]; simp
  · exact fun g hg x hx => vanishPin S g hg x hx
  apply Obstruction468.cube_separates Q f (k+1) (fun t z => probe p (a t) (b t) z)
  · intro t z
    constructor
    · rw [sumProbe_none]; simp [bit,hp,awayA t]
    · intro j; rw [sumProbe_some]; simp [bit,awayB t]
  · intro g dg t
    exact cubeLow p (a t) (b t) g dg
  · simpa only [f,profile hk] using li

end Pool468

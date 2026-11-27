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
def bools (m k : ℕ) : Set (P m k) := Set.range (fun v : V m k => X v * X v + X v)
def pin {m k : ℕ} (S : Mask m) : Set (P m k) := {1 + part S none} ∪ Set.range (fun j : Fin k => part S (some j))
def sys {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) : Set (P m k) :=
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
  · by_cases h : i=p <;> by_cases h' : i=a <;> simp [probe,probePoly,h,h']
  · by_cases h : i=b <;> simp [probe,probePoly,h]

theorem cubeLow {m k : ℕ} (p a b : Fin m) (f : P m k) (hd : f.totalDegree<k+1) :
    ∑ z : Fin (k+1) → K, eval (probe p a b z) f = 0 := by
  have cap := totalDegree_bind₁_le (probePoly p a b) (probePoly_low p a b) f
  have van := cube_sum (k+1) (bind₁ (probePoly p a b) f) (by simpa only [one_mul] using cap.trans_lt hd)
  convert van using 1
  apply Finset.sum_congr rfl
  intro z _
  rw [eval_bind₁]
  simp only [Function.comp_def,probePoly_eval]

end Pool468

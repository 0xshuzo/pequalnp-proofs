import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1095

section ProofBody

private abbrev V (q : ℕ) : Type := Fin q → ZMod 2

private def dot {q : ℕ} (a x : V q) : ZMod 2 := ∑ i, a i * x i

private def chi {q : ℕ} (a x : V q) : ℚ := if dot a x = 0 then 1 else -1

private lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

private lemma v_add_self {q : ℕ} (a : V q) : a + a = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  rcases zmod2_cases (a i) with h | h <;> rw [h] <;> decide

private lemma v_add_eq_zero_iff {q : ℕ} (a b : V q) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    have hi : a i + b i = 0 := congrFun h i
    rcases zmod2_cases (a i) with ha | ha <;> rcases zmod2_cases (b i) with hb | hb <;>
      simp [ha, hb] at hi ⊢
  · rintro rfl; exact v_add_self a

private lemma dot_zero_left {q : ℕ} (x : V q) : dot (0 : V q) x = 0 := by
  simp [dot]

private lemma dot_add_left {q : ℕ} (a b x : V q) : dot (a + b) x = dot a x + dot b x := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right {q : ℕ} (a x y : V q) : dot a (x + y) = dot a x + dot a y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma chi_zero {q : ℕ} (x : V q) : chi (0 : V q) x = 1 := by
  simp [chi, dot_zero_left]

private lemma chi_mul_left {q : ℕ} (a b x : V q) : chi a x * chi b x = chi (a + b) x := by
  unfold chi
  rw [dot_add_left]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with ha | ha <;> rcases zmod2_cases (dot b x) with hb | hb <;>
    simp [ha, hb, h11]

private lemma chi_mul_right {q : ℕ} (a x y : V q) : chi a (x + y) = chi a x * chi a y := by
  unfold chi
  rw [dot_add_right]
  have h11 : (1 : ZMod 2) + 1 = 0 := rfl
  rcases zmod2_cases (dot a x) with hx | hx <;> rcases zmod2_cases (dot a y) with hy | hy <;>
    simp [hx, hy, h11]

private lemma chi_sq {q : ℕ} (a x : V q) : chi a x * chi a x = 1 := by
  rw [chi_mul_left, v_add_self, chi_zero]

private lemma one_sub_chi {q : ℕ} (a x : V q) :
    1 - chi a x = if dot a x = 0 then 0 else 2 := by
  unfold chi
  split_ifs <;> norm_num

private lemma card_V (q : ℕ) : (Fintype.card (V q) : ℚ) = (2 : ℚ) ^ q := by
  have h : Fintype.card (V q) = 2 ^ q := by
    simp [V, ZMod.card]
  exact_mod_cast h

private lemma sum_chi {q : ℕ} (a : V q) :
    ∑ x : V q, chi a x = if a = 0 then (2 : ℚ) ^ q else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [chi_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, ↓reduceIte]
    exact card_V q
  · simp only [ha, ↓reduceIte]
    have hex : ∃ i : Fin q, a i ≠ 0 := by
      by_contra h
      push Not at h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    have hai : a i = 1 := by
      rcases zmod2_cases (a i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    let e : V q := Pi.single i (1 : ZMod 2)
    have hdot_e : dot a e = 1 := by
      unfold dot
      rw [Finset.sum_eq_single i]
      · simp [e, hai]
      · intro j _ hji
        simp [e, Pi.single_eq_of_ne hji]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    have hchi_e : chi a e = -1 := by
      unfold chi
      rw [hdot_e]
      norm_num
    let eqv : V q ≃ V q :=
      { toFun := fun x => x + e
        invFun := fun x => x + e
        left_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero]
        right_inv := fun x => by dsimp only; rw [add_assoc, v_add_self, add_zero] }
    have hsum : ∑ x : V q, chi a x = ∑ x : V q, chi a (x + e) :=
      (Fintype.sum_equiv eqv _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : V q, chi a (x + e) = -(∑ x : V q, chi a x) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [chi_mul_right, hchi_e]
      ring
    linarith

private lemma sum_chi_mul {q : ℕ} (a b : V q) :
    ∑ x : V q, chi a x * chi b x = if a = b then (2 : ℚ) ^ q else 0 := by
  have h1 : ∑ x : V q, chi a x * chi b x = ∑ x : V q, chi (a + b) x :=
    Finset.sum_congr rfl fun x _ => chi_mul_left a b x
  rw [h1, sum_chi]
  simp only [v_add_eq_zero_iff]


private abbrev F := ZMod 2

private def local' {n} (D : Fin n → Finset (Fin n)) (T : Fin n → V n → F) :=
  ∀ i x y, (∀ j ∈ D i, x j = y j) → T i x = T i y

private def fill {n} (U : Finset (Fin n)) (b : V n) (z : U → F) (i : Fin n) : F :=
  if h : i∈U then z ⟨i,h⟩ else b i

private def obs {n m} (Q : Fin n → V m) (U : Finset (Fin n)) (T : Fin n → V n → F)
    (b : V n) (z : U → F) (r : Fin m) : F :=
  ∑ i, (fill U b z i + T i (fill U b z))*Q i r

private def uniform' {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) :=
  ∀ T, local' D T → ∀ b v, 2^m * Nat.card {z : U → F // obs Q U T b z = v}=2^U.card

private def pivot {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (a : V m) (j : Fin n) :=
  dot a (Q j)=1 ∧ ∀ i, j∈D i → dot a (Q i)=0

private def cond {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m) (U : Finset (Fin n)) :=
  ∀ a : V m, a≠0 → ∃ j∈U, pivot D Q a j

private lemma dot_swap {m} (a b : V m) : dot a b=dot b a := by simp [dot,mul_comm]

private lemma chi_swap {m} (a b : V m) : chi a b=chi b a := by simp [chi,dot_swap a b]

private lemma dot_obs {n m} (a : V m) (Q : Fin n → V m) (U : Finset (Fin n))
    (T : Fin n → V n → F) (b : V n) (z : U → F) :
    dot a (obs Q U T b z)=∑ i, (fill U b z i + T i (fill U b z))*dot a (Q i) := by
  simp only [dot,obs,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def unit {m : Nat} (r : Fin m) : V m := Pi.single r 1

private lemma dot_unit {m} (a : V m) (r) : dot a (unit r)=a r := by
  unfold dot
  rw [Finset.sum_eq_single r]
  · simp [unit]
  · intro i _ hi
    simp [unit,Pi.single_eq_of_ne hi]
  · simp

private lemma zero_or_one (x : F) : x=0 ∨ x=1 := zmod2_cases x
private lemma twice (x : F) : x+x=0 := by revert x; decide

private lemma uniform_needs {n m} {D : Fin n → Finset (Fin n)} {Q : Fin n → V m}
    {U : Finset (Fin n)} (h : uniform' D Q U) : cond D Q U := by
  classical
  intro a ha
  by_contra lack
  let K := U.filter fun j => dot a (Q j)=1
  have get (j : Fin n) (hj : j∈K) : ∃ i, j∈D i ∧ dot a (Q i)=1 := by
    by_contra! bad
    obtain ⟨mem,one⟩ := Finset.mem_filter.mp hj
    apply lack
    refine ⟨j,mem,one,?_⟩
    intro i hi
    exact (zero_or_one _).resolve_right (bad i hi)
  let owner (j : Fin n) := if hj : j∈K then Classical.choose (get j hj) else j
  have ow (j : Fin n) (hj : j∈K) : j∈D (owner j) ∧ dot a (Q (owner j))=1 := by
    simpa [owner,hj] using Classical.choose_spec (get j hj)
  let T (i : Fin n) (x : V n) : F := ∑ j∈K, if owner j=i then x j else 0
  have loc : local' D T := by
    intro i x y eq
    apply Finset.sum_congr rfl
    intro j mem
    by_cases e : owner j=i
    · subst i; simp [eq j (ow j mem).1]
    · simp [e]
  have cancel (z : U → F) : dot a (obs Q U T 0 z)=0 := by
    rw [dot_obs]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    let x := fill U (0 : V n) z
    have raw : (∑ i, x i * dot a (Q i))=∑ i∈K, x i := by
      rw [show K=Finset.univ.filter (fun j => j∈U ∧ dot a (Q j)=1) by ext j; simp [K]]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i∈U
      · rcases zero_or_one (dot a (Q i)) with eq | eq <;> simp [eq,hi]
      · simp [x,fill,hi]
    have rules : (∑ i, T i x*dot a (Q i))=∑ i∈K,x i := by
      unfold T
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simp [ite_mul,(ow j hj).2]
    change (∑ i,x i*dot a (Q i))+(∑ i,T i x*dot a (Q i))=0
    rw [raw,rules,twice]
  obtain ⟨r,hr⟩ : ∃ r,a r≠0 := by
    by_contra! allzero
    exact ha (funext allzero)
  let v := unit r
  have hcnt := h T loc 0 v
  have empty : IsEmpty {z : U → F // obs Q U T 0 z=v} := ⟨by
    rintro ⟨z,hz⟩
    have eq := cancel z
    rw [hz,dot_unit] at eq
    exact hr eq⟩
  have no : Nat.card {z : U → F // obs Q U T 0 z=v}=0 := @Nat.card_eq_zero_of_isEmpty _ empty
  rw [no,Nat.mul_zero] at hcnt
  exact (Nat.ne_of_gt (Nat.two_pow_pos U.card)) hcnt.symm


end ProofBody
end PEqualNP.Outside.L_lib_1095

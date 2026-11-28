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

private lemma fiberCount {A : Type} [Fintype A] {m : Nat} (f : A → V m)
    (hz : ∀ a : V m, a≠0 → ∑ x, chi a (f x)=0) (v : V m) :
    2^m*Nat.card {x : A // f x=v}=Fintype.card A := by
  classical
  have total : (∑ x, ∑ a, chi (f x) a * chi v a) = (Fintype.card A : ℚ) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single (0 : V m)]
    · simp [fun (x : V m) => (chi_swap x 0).trans (chi_zero x)]
    · intro a _ ha
      rw [← Finset.sum_mul]
      have hh : (∑ x, chi (f x) a)=0 := by
        simpa only [chi_swap a] using hz a ha
      simp [hh]
    · simp
  have sumh : (∑ x : A, if f x=v then (2:ℚ)^m else 0) = (Fintype.card A : ℚ) := by
    simpa only [sum_chi_mul] using total
  rw [← Finset.sum_filter] at sumh
  simp only [Finset.sum_const,nsmul_eq_mul] at sumh
  have cnt : Nat.card {x : A // f x=v} = (Finset.univ.filter (fun x => f x=v)).card := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  rw [cnt,mul_comm]
  exact_mod_cast sumh

private lemma cond_suffices {n m} {D : Fin n → Finset (Fin n)} {Q : Fin n → V m}
    {U : Finset (Fin n)} (h : cond D Q U) : uniform' D Q U := by
  classical
  intro T loc b v
  have balance (a : V m) (ha : a≠0) : (∑ z : U → F, chi a (obs Q U T b z))=0 := by
    obtain ⟨j,hj,own,quiet⟩ := h a ha
    let t : U := ⟨j,hj⟩
    let change : (U → F) → (U → F) := fun z i => if i=t then z i+1 else z i
    have cancel (c : F) : c+1+1=c := by revert c; decide
    let e : (U → F) ≃ (U → F) := ⟨change,change,
      fun z => by funext i; by_cases hi : i=t <;> simp [change,hi,cancel],
      fun z => by funext i; by_cases hi : i=t <;> simp [change,hi,cancel]⟩
    have raw (z : U → F) (i : Fin n) :
        fill U b (change z) i=fill U b z i+(if i=j then 1 else 0) := by
      by_cases eq : i=j
      · subst i; simp [fill,change,hj,t]
      · by_cases mem : i∈U
        · have dif : (⟨i,mem⟩ : U)≠t := fun hh => eq (congrArg Subtype.val hh)
          simp [fill,change,mem,eq,dif]
        · simp [fill,mem,eq]
    have moved (z : U → F) : dot a (obs Q U T b (change z))=dot a (obs Q U T b z)+1 := by
      rw [dot_obs,dot_obs]
      have term (i : Fin n) :
          (fill U b (change z) i+T i (fill U b (change z)))*dot a (Q i)=
          (fill U b z i+T i (fill U b z))*dot a (Q i)+(if i=j then 1 else 0) := by
        by_cases zero : dot a (Q i)=0
        · have ne : i≠j := fun e => by subst i; rw [own] at zero; exact one_ne_zero zero
          simp [zero,ne]
        · have same : T i (fill U b (change z))=T i (fill U b z) := by
            apply loc
            intro k hk
            have ne : k≠j := fun ee => by subst k; exact zero (quiet i hk)
            simp [raw,ne]
          rw [same,raw]
          by_cases eq : i=j
          · subst i; simp [own]; ring
          · simp [eq]
      simp_rw [term]
      rw [Finset.sum_add_distrib]
      simp
    have alt (z : U → F) : chi a (obs Q U T b (e z)) = -chi a (obs Q U T b z) := by
      change chi a (obs Q U T b (change z))=_
      unfold chi
      rw [moved]
      rcases zero_or_one (dot a (obs Q U T b z)) with hz | hz <;> simp [hz, twice]
    have total := e.sum_comp (fun z => chi a (obs Q U T b z))
    simp only [alt, Finset.sum_neg_distrib] at total
    linarith
  simpa [Fintype.card_fun,ZMod.card,F] using fiberCount (obs Q U T b) balance v

end ProofBody
end PEqualNP.Outside.L_lib_1095

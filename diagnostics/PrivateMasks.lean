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

private abbrev NZ (m : Nat) := {a : V m // a≠0}

private lemma nzCard (m : Nat) : Fintype.card (NZ m) = 2^m-1 := by
  classical
  change Fintype.card {a : V m // ¬ a=0}=_
  rw [Fintype.card_subtype_compl]
  simp [V,ZMod.card]

private def readSet {n} (D : Fin n → Finset (Fin n)) (j : Fin n) :=
  Finset.univ.filter fun i => j∈D i

private lemma totalReads {n} (D : Fin n → Finset (Fin n)) :
    (∑ j,(readSet D j).card)=∑ i,(D i).card := by
  classical
  simp_rw [readSet,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp

private lemma countLower {n m} (D : Fin n → Finset (Fin n)) (Q : Fin n → V m)
    (W : Finset (Fin n)) (card : W.card=2^m-1) (all : cond D Q Finset.univ)
    (minimal : ∀ j∈W, ¬cond D Q (Finset.univ.erase j)) :
    2^m-1≤n ∧ (∀ j∈W,m-1≤(readSet D j).card) ∧
      (2^m-1)*(m-1)≤∑ i,(D i).card := by
  classical
  have privateMask (j : W) : ∃ a : NZ m, pivot D Q a j ∧ ∀ i, pivot D Q a i → i=j := by
    have bad := minimal j j.property
    unfold cond at bad
    push_neg at bad
    obtain ⟨a,non,miss⟩ := bad
    obtain ⟨i,_,hp⟩ := all a non
    have only (k : Fin n) (ok : pivot D Q a k) : k=j := by
      by_contra diff
      exact miss k (Finset.mem_erase.mpr ⟨diff,Finset.mem_univ _⟩) ok
    exact ⟨⟨a,non⟩,only i hp ▸ hp,only⟩
  choose f existsPivot uniquePivot using privateMask
  have inj : Function.Injective f := by
    intro j k eq
    apply Subtype.ext
    exact uniquePivot k j (eq ▸ existsPivot j)
  have onto : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,by simpa [nzCard] using card⟩).2
  have oneAt (j : W) (a : V m) (hp : pivot D Q a j) : a=(f j).val := by
    have non : a≠0 := by
      intro zero
      have := hp.1
      rw [zero,dot_zero_left] at this
      exact zero_ne_one this
    obtain ⟨k,hk⟩ := onto ⟨a,non⟩
    have eq : (f k).val=a := congrArg Subtype.val hk
    have jk : j=k := Subtype.ext (uniquePivot k j (eq ▸ hp))
    simpa [jk] using eq.symm
  have quantity (j : W) : m-1≤(readSet D j.val).card := by
    let R := readSet D j.val
    let code (w : V m) : F × (R → F) := (dot w (Q j), fun i => dot w (Q i.val))
    have mono : Function.Injective code := by
      intro a b same
      have o : dot a (Q j)=dot b (Q j) := congrArg Prod.fst same
      have eq (i : R) : dot a (Q i)=dot b (Q i) := congrFun (congrArg Prod.snd same) i
      have hp := existsPivot j
      have fixed : pivot D Q ((f j).val+(a+b)) j := by
        constructor
        · rw [dot_add_left,dot_add_left,o,twice,hp.1,add_zero]
        · intro i hi
          have mem : i∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
          rw [dot_add_left,dot_add_left,eq ⟨i,mem⟩,twice,hp.2 i hi,add_zero]
      have hsame := oneAt j _ fixed
      have vanish : a+b=0 := add_left_cancel (show (f j).val+(a+b)=(f j).val+0 by simpa using hsame)
      exact (v_add_eq_zero_iff a b).mp vanish
    have hcap := Fintype.card_le_of_injective code mono
    have pp : 2^m ≤ 2^(R.card+1) := by simpa [V,F,ZMod.card,pow_succ,mul_comm] using hcap
    by_contra! low
    have e : R.card+1<m := by change m-1>R.card at low; omega
    exact (Nat.not_lt_of_ge pp) (Nat.pow_lt_pow_right (by decide : 1<2) e)
  refine ⟨?_,fun j hj => quantity ⟨j,hj⟩,?_⟩
  · have sz := Finset.card_le_card (Finset.subset_univ W)
    simpa [card] using sz
  · rw [← totalReads,←card]
    calc
      W.card*(m-1) = ∑ _j∈W,m-1 := by simp
      _ ≤ ∑ j∈W,(readSet D j).card := Finset.sum_le_sum (fun j mem => quantity ⟨j,mem⟩)
      _ ≤ ∑ j,(readSet D j).card := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

end ProofBody
end PEqualNP.Outside.L_lib_1095

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


private def ones {m : Nat} (a : V m) := Finset.univ.filter fun r => a r=1

private lemma onesNon {m} (a : NZ m) : (ones a.val).Nonempty := by
  classical
  by_contra empty
  apply a.property
  funext r
  exact (zero_or_one (a.val r)).resolve_right (fun h => empty ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩)

private noncomputable def low {m} (a : NZ m) := (ones a.val).min' (onesNon a)
private noncomputable def high {m} (a : NZ m) := (ones a.val).max' (onesNon a)

private noncomputable def col {m} (a : NZ m) : V m :=
  if h : (high a).val+1<m then unit (low a)+unit ⟨(high a).val+1,h⟩ else unit (low a)

private lemma oddCol {m} (a : NZ m) : dot a.val (col a)=1 := by
  classical
  have hl : a.val (low a)=1 :=
    (Finset.mem_filter.mp (Finset.min'_mem (ones a.val) (onesNon a))).2
  unfold col
  split_ifs with h
  · let s : Fin m := ⟨(high a).val+1,h⟩
    have hs : a.val s=0 := by
      apply (zero_or_one _).resolve_right
      intro one
      have mem : s∈ones a.val := Finset.mem_filter.mpr ⟨Finset.mem_univ _,one⟩
      have hle : s≤high a := Finset.le_max' _ _ mem
      change (high a).val+1≤(high a).val at hle
      omega
    change dot a.val (unit (low a)+unit s)=1
    rw [dot_add_right,dot_unit,dot_unit,hl,hs,add_zero]
  · rw [dot_unit,hl]

private lemma supportTwo {m} (a : NZ m) : (Finset.univ.filter (fun r => col a r≠0)).card≤2 := by
  classical
  unfold col
  split_ifs with h
  · let s : Fin m := ⟨(high a).val+1,h⟩
    apply (Finset.card_le_card (t:=({low a,s} : Finset (Fin m))) ?_).trans (Finset.card_pair_le _ _)
    intro r hr
    by_contra bad
    simp only [Finset.mem_insert,Finset.mem_singleton] at bad
    have l : r≠low a := fun q => bad (.inl q)
    have u : r≠s := fun q => bad (.inr q)
    exact (Finset.mem_filter.mp hr).2 (by change unit (low a) r+unit s r=0; simp [unit,Pi.single_eq_of_ne l,Pi.single_eq_of_ne u])
  · have sub : Finset.univ.filter (fun r => unit (low a) r ≠ 0) ⊆ {low a} := by
      intro r hr
      by_contra e
      have ne : r≠low a := fun q => e (Finset.mem_singleton.mpr q)
      exact (Finset.mem_filter.mp hr).2 (by simp [unit,Pi.single_eq_of_ne ne])
    exact (Finset.card_le_card sub).trans (by simp)

private noncomputable def intervalSite {m} (l r : Fin m) (le : l≤r) : NZ m :=
  ⟨fun i => if l≤i ∧ i≤r then 1 else 0,by
    intro eq
    have h := congrFun eq l
    simpa [le] using h⟩

private lemma intervalMem {m} (l r : Fin m) (le : l≤r) (x : Fin m) :
    x∈ones (intervalSite l r le).val ↔ l≤x ∧ x≤r := by
  simp [ones,intervalSite]

private lemma loInterval {m} (l r : Fin m) (le : l≤r) : low (intervalSite l r le)=l := by
  apply le_antisymm
  · exact Finset.min'_le _ _ ((intervalMem l r le l).mpr ⟨le_rfl,le⟩)
  · exact ((intervalMem l r le _).mp (Finset.min'_mem _ _)).1

private lemma hiInterval {m} (l r : Fin m) (le : l≤r) : high (intervalSite l r le)=r := by
  apply le_antisymm
  · exact ((intervalMem l r le _).mp (Finset.max'_mem _ _)).2
  · exact Finset.le_max' _ _ ((intervalMem l r le r).mpr ⟨le,le_rfl⟩)

private lemma stockOne {m} (i : Fin m) : ∃ a : NZ m,col a=unit i := by
  let z : Fin m := ⟨m-1,by have := i.isLt; omega⟩
  have le : i≤z := by change i.val≤m-1; have := i.isLt; omega
  refine ⟨intervalSite i z le,?_⟩
  have last : ¬ z.val+1<m := by dsimp [z]; have := i.isLt; omega
  simp [col,loInterval,hiInterval,last]

private lemma stockPairLt {m} (i j : Fin m) (ij : i<j) : ∃ a : NZ m,col a=unit i+unit j := by
  let z : Fin m := ⟨j.val-1,by have := j.isLt; omega⟩
  have le : i≤z := by change i.val≤j.val-1; change i.val<j.val at ij; omega
  refine ⟨intervalSite i z le,?_⟩
  have next : z.val+1=j.val := by change j.val-1+1=j.val; change i.val<j.val at ij; omega
  simp [col,loInterval,hiInterval,next]

private lemma stockPair {m} (i j : Fin m) (ij : i≠j) : ∃ a : NZ m,col a=unit i+unit j := by
  rcases lt_or_gt_of_ne ij with lt | gt
  · exact stockPairLt i j lt
  · simpa only [add_comm (unit i) (unit j)] using stockPairLt j i gt

end ProofBody
end PEqualNP.Outside.L_lib_1095

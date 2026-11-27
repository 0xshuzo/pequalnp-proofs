import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_301_aux


abbrev V (n : Nat) := Bool × Fin n
def cross {n : Nat} (P : Equiv.Perm (Fin n)) (S : Finset (V n)) :=
  Finset.univ.filter (fun i : Fin n => ¬ ((false,i)∈S ↔ (true,P i)∈S))
def agrees {n : Nat} (P Q : Equiv.Perm (Fin n)) := Finset.univ.filter (fun i => P i=Q i)
private def mateOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (j : Fin r) (v : V n) : V n :=
  if v.1 then (false, (M j).symm v.2) else (true, M j v.2)

private def borderOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) : Finset (V n) :=
  S.filter (fun v => ∃ j : Fin r, mateOf M j v ∉ S)

private def ballCard (n r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (r + 1), Nat.choose n j

private theorem pow_101_le (n : ℕ) : 101 ^ n ≤ 2 ^ (n / 50 + 1) * 100 ^ n := by
  have h50 : (101 : ℕ) ^ 50 ≤ 2 * 100 ^ 50 := by norm_num
  have hdiv : n = 50 * (n / 50) + n % 50 := (Nat.div_add_mod n 50).symm
  have hmod : n % 50 < 50 := Nat.mod_lt n (by omega)
  have hpart1 : 101 ^ (50 * (n / 50)) ≤ 2 ^ (n / 50) * 100 ^ (50 * (n / 50)) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left h50 _
  have hpart2 : 101 ^ (n % 50) ≤ 2 * 100 ^ (n % 50) := by
    have hmul : 101 ^ (n % 50) * 100 ^ (50 - n % 50) ≤ 2 * 100 ^ 50 := by
      calc 101 ^ (n % 50) * 100 ^ (50 - n % 50)
          ≤ 101 ^ (n % 50) * 101 ^ (50 - n % 50) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = 101 ^ 50 := by rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
        _ ≤ 2 * 100 ^ 50 := h50
    have h50eq : 100 ^ 50 = 100 ^ (n % 50) * 100 ^ (50 - n % 50) := by
      rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
    rw [h50eq, ← mul_assoc] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by omega))
  conv_lhs => rw [hdiv, pow_add]
  calc 101 ^ (50 * (n / 50)) * 101 ^ (n % 50)
      ≤ (2 ^ (n / 50) * 100 ^ (50 * (n / 50))) * (2 * 100 ^ (n % 50)) :=
        Nat.mul_le_mul hpart1 hpart2
    _ = 2 ^ (n / 50 + 1) * (100 ^ (50 * (n / 50)) * 100 ^ (n % 50)) := by rw [pow_succ]; ring
    _ = 2 ^ (n / 50 + 1) * 100 ^ n := by rw [← pow_add, ← hdiv]

private theorem ballCard_le_pow2 {n r : ℕ} (hr : r ≤ n) :
    ballCard n r ≤ 2 ^ (n / 50 + 1 + 7 * r) := by
  have hbinom : 100 ^ (n - r) * ballCard n r ≤ 101 ^ n := by
    have hexp : (100 + 1 : ℕ) ^ n = ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j := by
      have h1 := add_pow (1 : ℕ) 100 n
      rw [show (100 + 1 : ℕ) = 1 + 100 from rfl, h1]
      refine Finset.sum_congr rfl fun j _ => by simp only [one_pow, one_mul, Nat.cast_id]
    have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
    calc 100 ^ (n - r) * ballCard n r
        = ∑ j ∈ Finset.range (r + 1), 100 ^ (n - r) * Nat.choose n j := by
          unfold ballCard; rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (r + 1), 100 ^ (n - j) * Nat.choose n j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j :=
          Finset.sum_le_sum_of_subset hsub
      _ = 101 ^ n := hexp.symm
  have h101 := pow_101_le n
  have hsplit : 100 ^ n = 100 ^ (n - r) * 100 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  have h100r : 100 ^ r ≤ 2 ^ (7 * r) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num : 100 ≤ 2 ^ 7) r
  have hmul : 100 ^ (n - r) * ballCard n r ≤ 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by
    calc 100 ^ (n - r) * ballCard n r
        ≤ 101 ^ n := hbinom
      _ ≤ 2 ^ (n / 50 + 1) * 100 ^ n := h101
      _ = 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 100 ^ r) := by rw [hsplit]; ring
      _ ≤ 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 2 ^ (7 * r)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h100r)
      _ = 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by rw [← pow_add]
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

private theorem perm_image_fiber_card {n : ℕ} (A Y : Finset (Fin n)) (hcard : A.card = Y.card) :
    Nat.choose n A.card *
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  let fib (Z : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π : Equiv.Perm (Fin n) => A.image π = Z)
  have hfib_eq : ∀ Z : Finset (Fin n), Z.card = A.card → (fib Z).card = (fib Y).card := by
    intro Z hZ
    have hZY : Z.card = Y.card := hZ.trans hcard
    have hc_eq : ((Finset.univ : Finset (Fin n)) \ Z).card = ((Finset.univ : Finset (Fin n)) \ Y).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ, hZY]
    let e1 : ↥Z ≃ ↥Y := Fintype.equivOfCardEq (by simp [hZY])
    let e2 : ↥((Finset.univ : Finset (Fin n)) \ Z) ≃ ↥((Finset.univ : Finset (Fin n)) \ Y) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hc_eq)
    let τ : Equiv.Perm (Fin n) := {
      toFun := fun x => if hx : x ∈ Z then (e1 ⟨x, hx⟩).val else (e2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩).val
      invFun := fun y => if hy : y ∈ Y then (e1.symm ⟨y, hy⟩).val else (e2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩).val
      left_inv := fun x => by
        dsimp only
        by_cases hx : x ∈ Z
        · rw [dif_pos hx, dif_pos (e1 ⟨x, hx⟩).property]
          exact congrArg Subtype.val (e1.symm_apply_apply ⟨x, hx⟩)
        · have hx' : x ∈ (Finset.univ : Finset (Fin n)) \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          have hny : (e2 ⟨x, hx'⟩).val ∉ Y := (Finset.mem_sdiff.mp (e2 ⟨x, hx'⟩).property).2
          rw [dif_neg hx, dif_neg hny]
          exact congrArg Subtype.val (e2.symm_apply_apply ⟨x, hx'⟩)
      right_inv := fun y => by
        dsimp only
        by_cases hy : y ∈ Y
        · rw [dif_pos hy, dif_pos (e1.symm ⟨y, hy⟩).property]
          exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
        · have hy' : y ∈ (Finset.univ : Finset (Fin n)) \ Y := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
          have hnz : (e2.symm ⟨y, hy'⟩).val ∉ Z := (Finset.mem_sdiff.mp (e2.symm ⟨y, hy'⟩).property).2
          rw [dif_neg hy, dif_neg hnz]
          exact congrArg Subtype.val (e2.apply_symm_apply ⟨y, hy'⟩)
    }
    have hτZ : Z.image τ = Y := by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (if hx' : x ∈ Z then (e1 ⟨x, hx'⟩).val else _) ∈ Y
        rw [dif_pos hx]
        exact (e1 ⟨x, hx⟩).property
      · intro hy
        refine ⟨(e1.symm ⟨y, hy⟩).val, (e1.symm ⟨y, hy⟩).property, ?_⟩
        change (if hx' : (e1.symm ⟨y, hy⟩).val ∈ Z then (e1 ⟨_, hx'⟩).val else _) = y
        rw [dif_pos (e1.symm ⟨y, hy⟩).property]
        exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
    refine Finset.card_bij (fun π _ => π.trans τ) ?_ ?_ ?_
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      have himg : A.image (π.trans τ) = (A.image π).image τ := by
        ext y; simp [Equiv.trans_apply]
      rw [himg, hπ, hτZ]
    · intro π1 _ π2 _ heq
      apply Equiv.ext
      intro x
      exact τ.injective (by simpa [Equiv.trans_apply] using Equiv.ext_iff.mp heq x)
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      refine ⟨π.trans τ.symm, ?_, by ext x; simp⟩
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      have himg : A.image (π.trans τ.symm) = (A.image π).image τ.symm := by
        ext x; simp [Equiv.trans_apply]
      rw [himg, hπ, ← hτZ]
      ext x; simp
  have hpart : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).biUnion fib := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, fib, Finset.mem_filter, true_iff]
    exact ⟨A.image π, Finset.card_image_of_injective A π.injective, rfl⟩
  have hdisj : ((Finset.powersetCard A.card (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint fib := by
    intro Z1 _ Z2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  have htot := congrArg Finset.card hpart
  rw [Finset.card_univ, Finset.card_biUnion hdisj] at htot
  have hsum_eq : ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card =
      Nat.choose n A.card * (fib Y).card := by
    calc ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card
        = ∑ _Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Y).card :=
          Finset.sum_congr rfl fun Z hZ => hfib_eq Z (Finset.mem_powersetCard.mp hZ).2
      _ = (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).card * (fib Y).card := by simp
      _ = Nat.choose n A.card * (fib Y).card := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hsum_eq, ← htot]

private theorem card_finset_card_le {n r : ℕ} :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r)).card ≤ ballCard n r := by
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r) ⊆
      (Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ] at hT ⊢
    exact ⟨T.card, by omega, rfl⟩
  calc _ ≤ ((Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (r + 1), (Finset.powersetCard j (Finset.univ : Finset (Fin n))).card :=
        Finset.card_biUnion_le
    _ = ballCard n r := by
        unfold ballCard
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma choose_lower (n k : Nat) (hk : k≤n) :
    2^min k (n-k) ≤ n.choose k := by
  induction n generalizing k with
  | zero => have eq : k=0 := by omega; subst k; decide
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases edge : n=k
      · subst k; simp
      · have h₁ := ih k (by omega)
        have h₂ := ih (k+1) (by omega)
        have step₁ : min (k+1) (n+1-(k+1)) - 1 ≤ min k (n-k) := by omega
        have step₂ : min (k+1) (n+1-(k+1)) - 1 ≤ min (k+1) (n-(k+1)) := by omega
        let d := min (k+1) (n+1-(k+1))-1
        have eq : min (k+1) (n+1-(k+1)) = d+1 := by dsimp [d]; omega
        have x : 2^d ≤ n.choose k := (Nat.pow_le_pow_right (by decide) step₁).trans h₁
        have y : 2^d ≤ n.choose (k+1) := (Nat.pow_le_pow_right (by decide) step₂).trans h₂
        rw [eq,pow_succ,Nat.choose_succ_succ]; omega

private def badOverlap {n : Nat} (Q : Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun P : Equiv.Perm (Fin n) => n<128*(agrees P Q).card)

private theorem overlap_bound {n : Nat} (hn : 512≤n) (Q : Equiv.Perm (Fin n)) :
    4*(badOverlap Q).card ≤ Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let F := Fintype.card (Equiv.Perm (Fin n))
  let row (i : Fin n) := Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i=Q i)
  have point (i : Fin n) : n*(row i).card=F := by
    have h := perm_image_fiber_card ({i} : Finset (Fin n)) {Q i} (by simp)
    simpa [row,F] using h
  have transposed : ∑ P : Equiv.Perm (Fin n), (agrees P Q).card = ∑ i : Fin n,(row i).card := by
    simp only [agrees,row,Finset.card_filter]
    rw [Finset.sum_comm]
  have count : ∑ P : Equiv.Perm (Fin n),(agrees P Q).card = F := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<n)
    rw [transposed,Finset.mul_sum]
    simp only [point,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  calc
    4*(badOverlap Q).card = ∑ _P ∈ badOverlap Q, 4 := by simp [Nat.mul_comm]
    _ ≤ ∑ P ∈ badOverlap Q,(agrees P Q).card := by
      apply Finset.sum_le_sum
      intro P h
      have := (Finset.mem_filter.mp h).2
      omega
    _ ≤ ∑ P : Equiv.Perm (Fin n),(agrees P Q).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := count
private theorem expansion_triple :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
      (∀ j l : Fin 3,j≠l → 128*(agrees (M j) (M l)).card≤n) ∧
      ∀ S : Finset (V n), n ≤ 2*S.card → 2*S.card≤3*n → n/5000 ≤ (borderOf M S).card := by
  refine ⟨500000, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hn32 : 32 ≤ n := by omega
  let M0 : Equiv.Perm (Fin n) := Equiv.refl (Fin n)
  let M1 : Equiv.Perm (Fin n) := {
    toFun := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn0⟩
    invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn0⟩
    left_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt h]
        have : i.val + 1 + n - 1 = n + i.val := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
      · have heq : i.val + 1 = n := by omega
        rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    right_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h0 : i.val = 0
      · have hm : (i.val + n - 1) % n = n - 1 := by
          rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hm, h0]
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      · have hm : (i.val + n - 1) % n = i.val - 1 := by
          have h1 : i.val + n - 1 = n + (i.val - 1) := by omega
          rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        have : i.val - 1 + 1 = i.val := by omega
        rw [this, Nat.mod_eq_of_lt hi]
  }
  let Mof : Equiv.Perm (Fin n) → (Fin 3 → Equiv.Perm (Fin n)) := fun π j =>
    match j with
    | ⟨0, _⟩ => M0
    | ⟨1, _⟩ => M1
    | ⟨2, _⟩ => π
  set b := n / 5000
  have hb_ge : 100 ≤ b := by omega

  let transOf (A : Finset (Fin n)) : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => decide (i ∈ A) ≠ decide (M1 i ∈ A))
  let candA : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun A => (transOf A).card ≤ 2 * b ∧ n / 8 ≤ A.card ∧ A.card + n/8 ≤ n)
  let candB (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B => (symmDiff A B).card ≤ b)
  let candPairs : Finset (Finset (Fin n) × Finset (Fin n)) :=
    candA.biUnion (fun A => (candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩)
  let badFor (AB : Finset (Fin n) × Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π => (symmDiff (AB.1.image π) AB.2).card ≤ b)
  let badPerms : Finset (Equiv.Perm (Fin n)) := candPairs.biUnion badFor

  have hcandA_card : candA.card ≤ 2 * ballCard n (2 * b) := by
    let encA : Finset (Fin n) → Bool × Finset (Fin n) := fun A => (decide ((⟨0, hn0⟩ : Fin n) ∈ A), transOf A)
    have hencA_inj : Function.Injective encA := by
      intro A1 A2 heq
      have h0 : decide ((⟨0, hn0⟩ : Fin n) ∈ A1) = decide ((⟨0, hn0⟩ : Fin n) ∈ A2) := congrArg Prod.fst heq
      have hT : transOf A1 = transOf A2 := congrArg Prod.snd heq
      have hall : ∀ k (hk : k < n), decide ((⟨k, hk⟩ : Fin n) ∈ A1) = decide ((⟨k, hk⟩ : Fin n) ∈ A2) := by
        intro k
        induction k with
        | zero => intro _; exact h0
        | succ k' ih =>
          intro hk
          have hprev := ih (by omega)
          have hstep := Finset.ext_iff.mp hT ⟨k', by omega⟩
          simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hstep
          have hM1 : M1 ⟨k', by omega⟩ = ⟨k' + 1, hk⟩ := by
            apply Fin.ext; dsimp only [M1]; exact Nat.mod_eq_of_lt hk
          rw [hM1, hprev] at hstep
          cases h1 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A1) <;>
            cases h2 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A2) <;>
            cases h3 : decide ((⟨k', by omega⟩ : Fin n) ∈ A2) <;> simp_all
      ext i
      have hi := hall i.val i.isLt
      simpa using hi
    let target := (Finset.univ : Finset Bool) ×ˢ
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b))
    have hsub : candA.image encA ⊆ target := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨A, hA, rfl⟩ := hp
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      simp only [target, encA, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
      exact hA.1
    calc candA.card = (candA.image encA).card := (Finset.card_image_of_injective candA hencA_inj).symm
      _ ≤ target.card := Finset.card_le_card hsub
      _ = 2 * ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b)).card := by
          simp [target, Finset.card_product]
      _ ≤ 2 * ballCard n (2 * b) := Nat.mul_le_mul_left 2 card_finset_card_le

  have hcandB_card : ∀ A : Finset (Fin n), (candB A).card ≤ ballCard n b := by
    intro A
    have hinj : Function.Injective (fun B : Finset (Fin n) => symmDiff A B) := by
      intro B1 B2 heq
      have h1 := congrArg (symmDiff A) heq
      rwa [symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left] at h1
    have hsub : (candB A).image (fun B => symmDiff A B) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
      intro T hT
      rw [Finset.mem_image] at hT
      obtain ⟨B, hB, rfl⟩ := hT
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      exact hB
    calc (candB A).card = ((candB A).image (fun B => symmDiff A B)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
          Finset.card_le_card hsub
      _ ≤ ballCard n b := card_finset_card_le

  have hbadFor_bound : ∀ AB ∈ candPairs,
      2 ^ (n/8) * (badFor AB).card ≤
        (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
    intro AB hAB
    simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk] at hAB
    obtain ⟨A, hA, B, _, rfl⟩ := hAB
    simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    let candY := Finset.univ.filter (fun Y : Finset (Fin n) => Y.card = A.card ∧ (symmDiff Y B).card ≤ b)
    have hY_card : candY.card ≤ ballCard n b := by
      have hinj : Function.Injective (fun Y : Finset (Fin n) => symmDiff Y B) := by
        intro Y1 Y2 heq
        have h1 := congrArg (fun Z => symmDiff Z B) heq
        rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at h1
      have hsub : candY.image (fun Y => symmDiff Y B) ⊆
          (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
        intro T hT
        rw [Finset.mem_image] at hT
        obtain ⟨Y, hY, rfl⟩ := hT
        simp only [candY, Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
        exact hY.2
      calc candY.card = (candY.image (fun Y => symmDiff Y B)).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
            Finset.card_le_card hsub
        _ ≤ ballCard n b := card_finset_card_le
    have hbad_sub : badFor (A, B) ⊆
        candY.biUnion (fun Y => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)) := by
      intro π hπ
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, candY] at hπ ⊢
      exact ⟨A.image π, ⟨Finset.card_image_of_injective A π.injective, hπ⟩, rfl⟩
    have hchoose_mul : Nat.choose n A.card * (badFor (A, B)).card ≤
        ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
      calc Nat.choose n A.card * (badFor (A, B)).card
          ≤ Nat.choose n A.card * (∑ Y ∈ candY, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card) :=
            Nat.mul_le_mul_left (Nat.choose n A.card) (le_trans (Finset.card_le_card hbad_sub) Finset.card_biUnion_le)
        _ = ∑ Y ∈ candY, Nat.choose n A.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card := by
            rw [Finset.mul_sum]
        _ = ∑ _Y ∈ candY, Fintype.card (Equiv.Perm (Fin n)) := by
            refine Finset.sum_congr rfl fun Y hY => ?_
            exact perm_image_fiber_card A Y (Finset.mem_filter.mp hY).2.1.symm
        _ = candY.card * Fintype.card (Equiv.Perm (Fin n)) := by simp
        _ ≤ ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := Nat.mul_le_mul_right _ hY_card
    have choose := choose_lower n A.card (by have := Finset.card_le_univ A; simpa using this)
    have h₁ : 2^(n/8) ≤ Nat.choose n A.card := (Nat.pow_le_pow_right (by decide) (by omega)).trans choose
    have hmid : 2^(n/8) ≤ (n+1)*2^b*Nat.choose n A.card :=
      h₁.trans (Nat.le_mul_of_pos_left _ (by positivity))
    calc 2 ^ (n/8) * (badFor (A, B)).card
        ≤ ((n + 1) * 2 ^ b * Nat.choose n A.card) * (badFor (A, B)).card :=
          Nat.mul_le_mul_right _ hmid
      _ = (n + 1) * 2 ^ b * (Nat.choose n A.card * (badFor (A, B)).card) := by ring
      _ ≤ (n + 1) * 2 ^ b * (ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_left _ hchoose_mul
      _ = (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hpairs_card : candPairs.card ≤ 2 * ballCard n (2 * b) * ballCard n b := by
    calc candPairs.card
        ≤ ∑ A ∈ candA, ((candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ A ∈ candA, (candB A).card := Finset.sum_congr rfl fun A _ => Finset.card_map _
      _ ≤ ∑ _A ∈ candA, ballCard n b := Finset.sum_le_sum fun A _ => hcandB_card A
      _ = candA.card * ballCard n b := by simp
      _ ≤ (2 * ballCard n (2 * b)) * ballCard n b := Nat.mul_le_mul_right _ hcandA_card
  have htot_bad : 2 ^ (n/8) * badPerms.card ≤
      2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
        Fintype.card (Equiv.Perm (Fin n)) := by
    calc 2 ^ (n/8) * badPerms.card
        ≤ 2 ^ (n/8) * (∑ AB ∈ candPairs, (badFor AB).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ AB ∈ candPairs, 2 ^ (n/8) * (badFor AB).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _AB ∈ candPairs, ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Finset.sum_le_sum hbadFor_bound
      _ = candPairs.card * ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) := by simp
      _ ≤ (2 * ballCard n (2 * b) * ballCard n b) *
            ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_right _ hpairs_card
      _ = 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
            Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hcoef_lt : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b < 2 ^ (n/8 - 2) := by
    have hb1 := ballCard_le_pow2 (n := n) (r := 2 * b) (by omega)
    have hb2 := ballCard_le_pow2 (n := n) (r := b) (by omega)
    have hn1_lt : n + 1 < 2 ^ (n / 50) := by
      have hk_ge : 10000 ≤ n / 50 := by omega
      have hlin : ∀ m : ℕ, 10 ≤ m → 60 * m < 2 ^ m := by
        intro m hm
        induction m with
        | zero => omega
        | succ m' ih =>
          by_cases h10 : m' < 10
          · have : m' = 9 := by omega
            subst this; norm_num
          · have hprev := ih (by omega)
            rw [pow_succ]; omega
      have h1 := hlin (n / 50) (by omega)
      omega
    have hexp_le : 1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b) ≤ n/8 - 2 := by
      omega
    calc 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b
        < 2 * 2 ^ (n / 50) * 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
            2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by
          have hpos1 : 0 < 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
              2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by positivity
          have hstep1 : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b ≤
              2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) := by
            have hm1 : ballCard n (2 * b) * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) := Nat.mul_le_mul hb1 hb2
            have hm2 : ballCard n (2 * b) * ballCard n b * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) :=
              Nat.mul_le_mul hm1 hb2
            have hm3 := Nat.mul_le_mul_left (2 * (n + 1) * 2 ^ b) hm2
            linarith
          have hstep2 : 2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) <
              2 * 2 ^ (n / 50) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) :=
            Nat.mul_lt_mul_of_pos_right (by omega) hpos1
          linarith
      _ = 2 ^ (1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b)) := by
          simp only [pow_add, pow_one]
      _ ≤ 2 ^ (n/8 - 2) := Nat.pow_le_pow_right (by omega) hexp_le
  let U := Fintype.card (Equiv.Perm (Fin n))
  have hbadSmall : 4*badPerms.card < U := by
    have positive : 0 < U := Fintype.card_pos
    have aux := lt_of_le_of_lt htot_bad (Nat.mul_lt_mul_of_pos_right hcoef_lt positive)
    have hp : 2^(n/8) = 2^(n/8-2)*4 := by
      conv_lhs => rw [show n/8=n/8-2+2 by omega,pow_add]
    rw [hp, Nat.mul_assoc] at aux
    exact Nat.lt_of_mul_lt_mul_left aux
  have overlap0 := overlap_bound (by omega : 512≤n) M0
  have overlap1 := overlap_bound (by omega : 512≤n) M1
  let avoid := badPerms ∪ (badOverlap M0 ∪ badOverlap M1)
  have rare : avoid.card<U := by
    have a := Finset.card_union_le badPerms (badOverlap M0 ∪ badOverlap M1)
    have b' := Finset.card_union_le (badOverlap M0) (badOverlap M1)
    change _ ≤ U at overlap0 overlap1
    change (badPerms ∪ (badOverlap M0 ∪ badOverlap M1)).card<U
    omega
  have good : ∃ π : Equiv.Perm (Fin n), π ∉ avoid := by
    by_contra hall
    push_neg at hall
    have eh : avoid = Finset.univ := by ext π; simp [hall π]
    rw [eh,Finset.card_univ] at rare
    exact lt_irrefl _ rare
  obtain ⟨π,hπ⟩ := good
  have hπ_good : π∉badPerms := fun e => hπ (Finset.mem_union_left _ e)
  have zo : 128*(agrees π M0).card≤n := by
    by_contra no
    exact hπ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)))
  have oo : 128*(agrees π M1).card≤n := by
    by_contra no
    exact hπ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)))
  have nofixed (i : Fin n) : M0 i ≠ M1 i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=(i.val+1)%n at hv
    have := i.isLt
    by_cases hs : i.val+1<n
    · rw [Nat.mod_eq_of_lt hs] at hv; omega
    · rw [show i.val+1=n by omega,Nat.mod_self] at hv; omega
  have z1 : (agrees M0 M1)=∅ := by ext i; simp [agrees,nofixed]
  have comm (P Q : Equiv.Perm (Fin n)) : agrees P Q=agrees Q P := by ext i; simp [agrees,eq_comm]
  refine ⟨Mof π,?_,?_⟩
  · intro j l ne
    fin_cases j <;> fin_cases l <;> first
      | exact (ne rfl).elim
      | exact zo
      | exact oo
      | change 128*(agrees M0 M1).card≤n; simp [z1]
      | change 128*(agrees M1 M0).card≤n; rw [comm M1 M0,z1]; simp
      | change 128*(agrees M0 π).card≤n; rwa [comm M0 π]
      | change 128*(agrees M1 π).card≤n; rwa [comm M1 π]
  intro S hSlow hShigh
  have hborder_ge : b ≤ (borderOf (Mof π) S).card := by
    by_contra hlt
    have hle : (borderOf (Mof π) S).card ≤ b := by omega
    let A : Finset (Fin n) := Finset.univ.filter (fun i => (false, i) ∈ S)
    let B : Finset (Fin n) := Finset.univ.filter (fun i => (true, i) ∈ S)
    have hAB_sum : A.card + B.card = S.card := by
      have hpart : S = A.image (fun i => (false, i)) ∪ B.image (fun i => (true, i)) := by
        ext ⟨flag, i⟩
        cases flag <;> simp [A, B]
      have hdisj : Disjoint (A.image (fun i => (false, i))) (B.image (fun i => (true, i))) := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_image] at h1 h2
        obtain ⟨_, _, rfl⟩ := h1; obtain ⟨_, _, heq⟩ := h2
        exact Bool.false_ne_true.symm (Prod.mk.inj heq).1
      have hc := congrArg Finset.card hpart
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective A (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_image_of_injective B (fun _ _ h => (Prod.mk.inj h).2)] at hc
      exact hc.symm

    have hsymAB : (symmDiff A B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun i => if i ∈ A then (false, i) else (true, i)
      have hinj : Set.InjOn f ↑(symmDiff A B) := by
        intro i1 _ i2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff A B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨i, hi, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hi
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [borderOf, Finset.mem_filter]
        rcases hi with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
          exact ⟨h1, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h2]⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
          exact ⟨h2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h1]⟩
      calc (symmDiff A B).card = ((symmDiff A B).image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have hsymPi : (symmDiff (A.image π) B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun y => if y ∈ A.image π then (false, π.symm y) else (true, y)
      have hinj : Set.InjOn f ↑(symmDiff (A.image π) B) := by
        intro y1 _ y2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact π.symm.injective (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff (A.image π) B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hy
        simp only [borderOf, Finset.mem_filter]
        rcases hy with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, if_pos h1]
          rw [Finset.mem_image] at h1
          obtain ⟨i, hiA, rfl⟩ := h1
          simp only [Equiv.symm_apply_apply]
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA h2
          exact ⟨hiA, ⟨2, by omega⟩, by simp [mateOf, Mof, h2]⟩
        · simp only [f, if_neg h1]
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have hnotA : (false, π.symm y) ∉ S := fun hmem => h1 (Finset.mem_image.mpr
            ⟨π.symm y, by simp [A, hmem], by simp⟩)
          exact ⟨h2, ⟨2, by omega⟩, by simp [mateOf, Mof, hnotA]⟩
      calc (symmDiff (A.image π) B).card = ((symmDiff (A.image π) B).image f).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have htrans_le : (transOf A).card ≤ 2 * (borderOf (Mof π) S).card := by
      let T1 := (transOf A).filter (fun i => (false, i) ∈ borderOf (Mof π) S)
      let T2 := (transOf A).filter (fun i => (false, M1 i) ∈ borderOf (Mof π) S ∨ (true, M1 i) ∈ borderOf (Mof π) S)
      have hcov : transOf A ⊆ T1 ∪ T2 := by
        intro i hi
        simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [T1, T2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, transOf]
        by_cases hA1 : i ∈ A
        · have hA2 : M1 i ∉ A := by intro h; simp [hA1, h] at hi
          have hS1 : (false, i) ∈ S := (Finset.mem_filter.mp hA1).2
          have hS2 : (false, M1 i) ∉ S := fun h => hA2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hS2]⟩
          · left; refine ⟨hi, ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS1, ⟨1, by omega⟩, by simp [mateOf, Mof, hB2]⟩
        · have hA2 : M1 i ∈ A := by by_contra h; simp [hA1, h] at hi
          have hS1 : (false, i) ∉ S := fun h => hA1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hS2 : (false, M1 i) ∈ S := (Finset.mem_filter.mp hA2).2
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨1, by omega⟩, by simp [mateOf, Mof, hS1]⟩
          · right; refine ⟨hi, Or.inl ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hB2]⟩
      have hT1_le : T1.card ≤ (borderOf (Mof π) S).card := by
        have hsub : T1.image (fun i => ((false, i) : V n)) ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          exact (Finset.mem_filter.mp hi).2
        calc T1.card = (T1.image (fun i => ((false, i) : V n))).card :=
              (Finset.card_image_of_injective T1 (fun _ _ h => (Prod.mk.inj h).2)).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      have hT2_le : T2.card ≤ (borderOf (Mof π) S).card := by
        let g : Fin n → V n := fun i => if (false, M1 i) ∈ borderOf (Mof π) S then (false, M1 i) else (true, M1 i)
        have hinj : Function.Injective g := by
          intro i1 i2 heq
          dsimp only [g] at heq
          split_ifs at heq with h1 h2 h2
          · exact M1.injective (Prod.mk.inj heq).2
          · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
          · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
          · exact M1.injective (Prod.mk.inj heq).2
        have hsub : T2.image g ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          have hmem := (Finset.mem_filter.mp hi).2
          dsimp only [g]
          split_ifs with h1
          · exact h1
          · exact hmem.resolve_left h1
        calc T2.card = (T2.image g).card := (Finset.card_image_of_injective T2 hinj).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      calc (transOf A).card ≤ (T1 ∪ T2).card := Finset.card_le_card hcov
        _ ≤ T1.card + T2.card := Finset.card_union_le T1 T2
        _ ≤ 2 * (borderOf (Mof π) S).card := by omega

    have hdiff_cards : A.card ≤ B.card + (symmDiff A B).card ∧ B.card ≤ A.card + (symmDiff A B).card := by
      have h1 : A ⊆ B ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hB : x ∈ B <;> simp [hx, hB]
      have h2 : B ⊆ A ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hA : x ∈ A <;> simp [hx, hA]
      exact ⟨le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _),
        le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)⟩
    have hA_cand : A ∈ candA := by
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hB_cand : B ∈ candB A := by
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hAB_mem : (A, B) ∈ candPairs := by
      simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨A, hA_cand, B, hB_cand, rfl⟩
    have hπ_bad : π ∈ badPerms := by
      simp only [badPerms, Finset.mem_biUnion]
      refine ⟨(A, B), hAB_mem, ?_⟩
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact hπ_good hπ_bad
  exact hborder_ge
private lemma one_split {n : Nat} (M : Fin 3→Equiv.Perm (Fin n)) (S : Finset (V n))
    (h : n/5000 ≤ (borderOf M S).card) : ∃ j,n/16384 ≤ (cross (M j) S).card := by
  classical
  let f (j : Fin 3) (i : Fin n) : V n := if (false,i) ∈ S then (false,i) else (true,M j i)
  have inc : borderOf M S ⊆ Finset.univ.biUnion (fun j : Fin 3 => (cross (M j) S).image (f j)) := by
    rintro ⟨side,i⟩ hv
    obtain ⟨inside,j,outside⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_biUnion.mpr
    refine ⟨j,Finset.mem_univ _,?_⟩
    cases side with
    | false =>
      change (true,M j i)∉S at outside
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun e => outside (e.mp inside)⟩,
        by simp [f,inside]⟩
    | true =>
      change (false,(M j).symm i)∉S at outside
      apply Finset.mem_image.mpr
      refine ⟨(M j).symm i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp [f,outside]⟩
      intro e
      exact outside (e.mpr (by simpa using inside))
  have bound : (borderOf M S).card ≤ ∑ j : Fin 3,(cross (M j) S).card :=
    (Finset.card_le_card inc).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)))
  by_contra nope
  push_neg at nope
  have h0 := nope (0 : Fin 3)
  have h1 := nope (1 : Fin 3)
  have h2 := nope (2 : Fin 3)
  rw [Fin.sum_univ_three] at bound
  omega

end PEqualNP.Outside.L_pcx_301_aux

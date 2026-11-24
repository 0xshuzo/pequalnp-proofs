import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_4765_417
    (count : ∀ (n m s o q : ℕ) (F : Fin n → ℕ → Set (Fin n)), o < m+s →
      (∀ l k, k<m → (F l k).ncard ≤ 1) →
      (∀ l j, j<s → ∃ a b, max a b<m+j ∧ F l (m+j) ⊆ F l a ∪ F l b) →
      (∀ l, q+1 ≤ (F l o).ncard) →
      n*q ≤ 100*s ∨ ∃ j<s, 100 < {l : Fin n | ∀ k<m+j, ¬ F l (m+j) ⊆ F l k}.ncard)
    (heavy : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      n=q^2+q+1 → (∀ l, Fintype.card {p : Fin n // I p l}=q+1) →
      (∀ p r, p≠r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set ((Fin n → Bool) × (Fin n → Bool))),
      let m := n+n
      let one (p i : Fin n) := decide (i=p)
      let F (l : Fin n) (k : ℕ) := {p : Fin n | I p l ∧
        (one p,one l) ∈ W k ∧ ((fun x => decide (¬ I x l)),one l) ∉ W k}
      o<m+s →
      (∀ p : Fin n, W p.val = {z | z.1 p = true} ∧ W (n+p.val) = {z | z.2 p = true}) →
      (∀ j<s, ∃ a b, max a b<m+j ∧ W (m+j) ∈ [W a ∪ W b,W a,∅,W a ∩ W b]) →
      (∀ z, Fintype.card {l : Fin n // z.2 l=true} ≤ q →
        (z ∈ W o ↔ ∃ p l, I p l ∧ z.1 p=true ∧ z.2 l=true)) →
      (∃ j<s, 100 < {l : Fin n | ∀ k<m+j, ¬ F l (m+j) ⊆ F l k}.ncard) → n*q≤100*s) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           (∀ (x9 : Finset (Fin x2)), ∀ x10 ∈ x9, x1 + (2 : ℕ) ≤ x9.card + Fintype.card { x12 : Fin x2 // x3 x12 x10 ∧ ∀ x13 ∈ x9.erase x10, ¬x3 x12 x13 }) →             ∀ (x10 x11 : ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),               have x13 : ℕ := x2 + x2;               have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);               have x15 : Bool → ℕ → Set (Fin x2) := fun (x15 : Bool) (x16 : ℕ) => {x17 : Fin x2 | (if x15 = Bool.true then (x14 x17, fun (x18 : Fin x2) => Bool.false) else (fun (x18 : Fin x2) => Bool.false, x14 x17)) ∈ x12 x16};               x11 < x13 + x10 → (∀ (x17 : Fin x2), x12 ↑x17 = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.1 x17 = Bool.true} ∧ x12 (x2 + ↑x17) = {x18 : (Fin x2 → Bool) × (Fin x2 → Bool) | x18.2 x17 = Bool.true}) → (∀ x18 < x10, ∃ (x20 : ℕ) (x21 : ℕ), Max.max x20 x21 < x13 + x18 ∧ x12 (x13 + x18) ∈ [x12 x20 ∪ x12 x21, x12 x20, ∅, x12 x20 ∩ x12 x21]) → (∀ (x19 : (Fin x2 → Bool) × (Fin x2 → Bool)), Fintype.card { x20 : Fin x2 // x19.2 x20 = Bool.true } ≤ x1 → (x19 ∈ x12 x11 ↔ ∃ (x21 : Fin x2) (x22 : Fin x2), x3 x21 x22 ∧ x19.1 x21 = Bool.true ∧ x19.2 x22 = Bool.true)) → (∃ x20 < x10, ∃ (x21 : Bool) (x22 : Fin x2) (x23 : Fin x2), x22 ≠ x23 ∧ x22 ∈ x15 x21 (x13 + x20) ∧ x23 ∈ x15 x21 (x13 + x20) ∧ ¬∃ x24 < x13 + x20, ∃ x25 < x13 + x20, x15 x21 (x13 + x20) = x15 x21 x24 ∪ x15 x21 x25) → x2 * x1 ≤ (100 : ℕ) * x10 := by
  classical
  intro q n I inst hq hn deg unique _ s o W m one _ out raw step correct _
  let anti (l : Fin n) := fun x => decide (¬ I x l)
  let F (l : Fin n) (k : ℕ) : Set (Fin n) :=
    {p | I p l ∧ (one p,one l) ∈ W k ∧ (anti l,one l) ∉ W k}
  have leaves : ∀ l k, k<m → (F l k).ncard ≤ 1 := by
    intro l k hk
    by_cases left : k<n
    · let r : Fin n := ⟨k,left⟩
      have input : W k = {z | z.1 r = true} := (raw r).1
      have sub : F l k ⊆ {r} := by
        intro p hp
        have hp' := hp.2.1
        rw [input] at hp'
        change decide (r=p) = true at hp'
        exact (of_decide_eq_true hp').symm
      simpa using Set.ncard_le_ncard sub
    · let r : Fin n := ⟨k-n,by dsimp [m] at hk; omega⟩
      have eq : k=n+r.val := by dsimp [r]; omega
      have empty : F l k = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have yes := hp.2.1
        have no := hp.2.2
        rw [eq,(raw r).2] at yes no
        exact no yes
      simp [empty]
  have cover : ∀ l j, j<s → ∃ a b, max a b<m+j ∧ F l (m+j) ⊆ F l a ∪ F l b := by
    intro l j hj
    obtain ⟨a,b,lt,rule⟩ := step j hj
    refine ⟨a,b,lt,?_⟩
    intro p hp
    obtain ⟨inc,yes,no⟩ := hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rule
    rcases rule with u | copy | zero | inter
    · rw [u] at yes no
      exact yes.elim (fun h => Or.inl ⟨inc,h,fun x => no (Or.inl x)⟩)
        (fun h => Or.inr ⟨inc,h,fun x => no (Or.inr x)⟩)
    · rw [copy] at yes no
      exact Or.inl ⟨inc,yes,no⟩
    · rw [zero] at yes
      exact False.elim yes
    · rw [inter] at yes no
      by_cases aSafe : (anti l,one l) ∉ W a
      · exact Or.inl ⟨inc,yes.1,aSafe⟩
      · exact Or.inr ⟨inc,yes.2,fun h => no ⟨not_not.mp aSafe,h⟩⟩
  have roots : ∀ l, q+1 ≤ (F l o).ncard := by
    intro l
    have oneCard : Fintype.card {i : Fin n // one l i = true} = 1 := by
      rw [Fintype.card_subtype]
      have filt : Finset.univ.filter (fun i => one l i = true) = {l} := by
        ext i
        simp [one]
      rw [filt,Finset.card_singleton]
    have sparse : Fintype.card {i : Fin n // one l i = true} ≤ q := by omega
    have safe : (anti l,one l) ∉ W o := by
      intro accepted
      obtain ⟨p,t,inc,hp,ht⟩ := (correct (anti l,one l) sparse).mp accepted
      change decide (t=l) = true at ht
      have eq := of_decide_eq_true ht
      subst t
      change decide (¬ I p l) = true at hp
      exact (of_decide_eq_true hp) inc
    have full : F l o = {p : Fin n | I p l} := by
      ext p
      constructor
      · exact fun h => h.1
      · intro inc
        refine ⟨inc,(correct (one p,one l) sparse).mpr ?_,safe⟩
        exact ⟨p,l,inc,by simp [one],by simp [one]⟩
    rw [full,Set.ncard_eq_toFinset_card',←deg l,Fintype.card_subtype]
    exact le_of_eq (by congr 1; ext p; simp)
  rcases count n m s o q F out leaves cover roots with bound | many
  · exact bound
  · exact heavy q n I hn deg unique s o W out raw step correct many

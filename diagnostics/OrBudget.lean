import PEqualNP.Defs

namespace SparseGateCount

theorem frontier {α : Type} [DecidableEq α] (n s : ℕ) (A : ℕ → Finset α) (O : Finset ℕ)
    (raw : ∀ i < n, (A i).card ≤ 1)
    (gate : ∀ j < s, ∃ U : Finset ℕ, (∀ i ∈ U, i < n+j) ∧
      U.card ≤ 1+(if j ∈ O then 1 else 0) ∧ A (n+j) ⊆ U.biUnion A)
    (F : Finset ℕ) (bound : ∀ i ∈ F, i < n+s) :
    (F.biUnion A).card ≤ F.card + (O.filter (· < s)).card := by
  classical
  induction s generalizing F with
  | zero =>
    have h := Finset.card_biUnion_le_card_mul F A 1 (fun i hi => raw i (by simpa using bound i hi))
    simpa using h
  | succ s ih =>
    have cutoff : O.filter (· < s+1) = if s ∈ O then insert s (O.filter (· < s)) else O.filter (· < s) := by
      ext i
      by_cases hs : s∈O
      · simp only [if_pos hs, Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro h
          by_cases he : i=s
          · exact Or.inl he
          · exact Or.inr ⟨h.1,by omega⟩
        · rintro (rfl | h)
          · exact ⟨hs,by omega⟩
          · exact ⟨h.1,by omega⟩
      · simp only [if_neg hs,Finset.mem_filter]
        constructor
        · rintro ⟨h,hi⟩
          have hne : i ≠ s := fun he => hs (he ▸ h)
          exact ⟨h,by omega⟩
        · rintro ⟨h,hi⟩; exact ⟨h,by omega⟩
    have hcount : (O.filter (· < s+1)).card =
        (O.filter (· < s)).card + (if s∈O then 1 else 0) := by
      rw [cutoff]
      by_cases h : s∈O <;> simp [h]
    have prefix := fun j (hj : j<s) => gate j (by omega)
    by_cases mem : n+s ∈ F
    · obtain ⟨U,early,fan,cover⟩ := gate s (by omega)
      let F' := F.erase (n+s) ∪ U
      have within : ∀ i ∈ F', i < n+s := by
        intro i hi
        rcases Finset.mem_union.mp hi with h | h
        · have h1 := (Finset.mem_erase.mp h).1
          have h2 := bound i (Finset.mem_erase.mp h).2
          omega
        · exact early i h
      have contain : F.biUnion A ⊆ F'.biUnion A := by
        intro z hz
        obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp hz
        by_cases he : i=n+s
        · obtain ⟨v,hv,haveZ⟩ := Finset.mem_biUnion.mp (cover (he ▸ hit))
          exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_union_right _ hv,haveZ⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hi⟩),hit⟩
      have counts := (Finset.card_le_card contain).trans (ih prefix F' within)
      have cu := Finset.card_union_le (F.erase (n+s)) U
      change F'.card ≤ _ at cu
      have ce := Finset.card_erase_add_one mem
      omega
    · have within : ∀ i ∈ F, i < n+s := by
        intro i hi
        have hi' := bound i hi
        have ne : i ≠ n+s := fun e => mem (e ▸ hi)
        omega
      have hb := ih prefix F within
      omega

theorem sensitivity {α : Type} [Fintype α] [DecidableEq α] (n s out : ℕ)
    (O : Finset ℕ) (v : ℕ → Bool) (V : ℕ → α → Bool)
    (ready : out < n+s) (reject : v out = false) (flips : ∀ a, V out a = true)
    (raw : ∀ i < n, (Finset.univ.filter fun a : α => v i = false ∧ V i a = true).card ≤ 1)
    (gate : ∀ j < s, ∃ a b : ℕ, a < n+j ∧ b < n+j ∧
      v (n+j) = (if j∈O then v a || v b else v a && v b) ∧
      ∀ h, V (n+j) h = (if j∈O then V a h || V b h else V a h && V b h)) :
    Fintype.card α ≤ (O.filter (· < s)).card+1 := by
  classical
  let A (i : ℕ) := Finset.univ.filter fun h : α => v i = false ∧ V i h = true
  have step (j : ℕ) (hj : j < s) : ∃ U : Finset ℕ, (∀ i ∈ U, i < n+j) ∧
      U.card ≤ 1+(if j ∈ O then 1 else 0) ∧ A (n+j) ⊆ U.biUnion A := by
    obtain ⟨a,b,ha,hb,base,pert⟩ := gate j hj
    by_cases hor : j∈O
    · refine ⟨{a,b},?_,?_,?_⟩
      · intro i hi; rcases (show i=a ∨ i=b by simpa using hi) with rfl | rfl <;> assumption
      · simpa [hor] using Finset.card_insert_le a ({b} : Finset ℕ)
      · intro h hit
        obtain ⟨hn,htrue⟩ := (Finset.mem_filter.mp hit).2
        rw [base,if_pos hor] at hn
        rw [pert,if_pos hor] at htrue
        cases h₁ : v a <;> cases h₂ : v b <;> simp_all [A]
    · by_cases yes : v a = true
      · refine ⟨{b},by simpa using hb,by simp [hor],?_⟩
        intro h hit
        obtain ⟨hn,ht⟩ := (Finset.mem_filter.mp hit).2
        simp [base,hor,yes] at hn
        simp [pert,hor] at ht
        simpa [A] using (show v b=false ∧ V b h=true from ⟨hn,ht.2⟩)
      · refine ⟨{a},by simpa using ha,by simp [hor],?_⟩
        intro h hit
        obtain ⟨_,ht⟩ := (Finset.mem_filter.mp hit).2
        simp [pert,hor] at ht
        simpa [A,yes] using ht.1
  have h := frontier n s A O raw step {out} (by simpa using ready)
  have all : A out = Finset.univ := by ext a; simp [A,reject,flips]
  simpa [all,Nat.add_comm] using h

end SparseGateCount

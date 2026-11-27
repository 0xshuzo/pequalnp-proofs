import PEqualNP.Defs

namespace BlockQuotaLocal
open PEqualNP.ProofComplexity

theorem derivation_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π₁ π₂ : List (Clause V)} (h₁ : IsDerivation F π₁) (h₂ : IsDerivation F π₂) :
    IsDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem completeness_aux {V : Type} [DecidableEq V] (F : Set (Clause V)) (S : Finset V) :
    ∀ a : V → Bool,
      (∀ b : V → Bool, (∀ v, v ∉ S → b v = a v) → ∃ C ∈ F, ¬ ClauseSat b C) →
      ∃ π : List (Clause V), IsDerivation F π ∧ π.length + 1 ≤ 2 ^ (S.card + 1) ∧
        ∃ C ∈ π, (∀ l ∈ C, a l.1 ≠ l.2) ∧ ∀ l ∈ C, l.1 ∉ S := by
  induction S using Finset.induction_on with
  | empty =>
    intro a h
    obtain ⟨C, hCF, hC⟩ := h a (fun _ _ => rfl)
    refine ⟨[C], IsDerivation.ax IsDerivation.nil hCF, by simp, C, by simp, ?_, by simp⟩
    intro l hl hal
    exact hC ⟨l, hl, hal⟩
  | insert x S hx ih =>
    intro a h
    have hsub : ∀ t : Bool, ∀ b : V → Bool, (∀ v, v ∉ S → b v = Function.update a x t v) →
        ∃ C ∈ F, ¬ ClauseSat b C := by
      intro t b hb
      apply h b
      intro v hv
      have hvx : v ≠ x := fun e => hv (e ▸ Finset.mem_insert_self x S)
      have hvS : v ∉ S := fun e => hv (Finset.mem_insert_of_mem e)
      rw [hb v hvS, Function.update_of_ne hvx]
    obtain ⟨π₀, hπ₀, hlen₀, C₀, hC₀π, hC₀a, hC₀S⟩ := ih (Function.update a x false) (hsub false)
    obtain ⟨π₁, hπ₁, hlen₁, C₁, hC₁π, hC₁a, hC₁S⟩ := ih (Function.update a x true) (hsub true)
    have hpow : 2 ^ ((insert x S).card + 1) = 2 * 2 ^ (S.card + 1) := by
      rw [Finset.card_insert_of_notMem hx, pow_succ, mul_comm]
    -- a literal on a variable other than `x`, falsified by an update of `a`, is falsified by `a`
    have key : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        (∀ l ∈ C, l.1 ∉ S) → ∀ l ∈ C, l.1 ≠ x → a l.1 ≠ l.2 ∧ l.1 ∉ insert x S := by
      intro t C hCa hCS l hl hlx
      refine ⟨?_, ?_⟩
      · have := hCa l hl
        rwa [Function.update_of_ne hlx] at this
      · intro hmem
        rcases Finset.mem_insert.mp hmem with e | e
        · exact hlx e
        · exact hCS l hl e
    -- a literal on `x` in a clause falsified by the update to `t` is `(x, !t)`
    have onx : ∀ (t : Bool) (C : Clause V), (∀ l ∈ C, Function.update a x t l.1 ≠ l.2) →
        ∀ l ∈ C, l.1 = x → l = (x, !t) := by
      intro t C hCa l hl hlx
      have := hCa l hl
      rw [hlx, Function.update_self] at this
      obtain ⟨v, s⟩ := l
      simp only at hlx this
      subst hlx
      cases t <;> cases s <;> simp_all
    by_cases h₀ : (x, true) ∈ C₀
    · by_cases h₁ : (x, false) ∈ C₁
      · refine ⟨(C₀.erase (x, true) ∪ C₁.erase (x, false)) :: (π₀ ++ π₁), ?_, ?_, _,
          List.mem_cons_self, ?_, ?_⟩
        · exact IsDerivation.res (derivation_append hπ₀ hπ₁) (List.mem_append_left _ hC₀π)
            (List.mem_append_right _ hC₁π) ⟨x, h₀, h₁, rfl⟩
        · rw [hpow]; simp only [List.length_cons, List.length_append]; omega
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).1
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).1
        · intro l hl
          rcases Finset.mem_union.mp hl with hl | hl
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx false C₀ hC₀a l hl e)
            exact (key false C₀ hC₀a hC₀S l hl hlx).2
          · obtain ⟨hne, hl⟩ := Finset.mem_erase.mp hl
            have hlx : l.1 ≠ x := fun e => hne (by simpa using onx true C₁ hC₁a l hl e)
            exact (key true C₁ hC₁a hC₁S l hl hlx).2
      · have hnox : ∀ l ∈ C₁, l.1 ≠ x := by
          intro l hl e
          have := onx true C₁ hC₁a l hl e
          simp at this
          exact h₁ (this ▸ hl)
        refine ⟨π₁, hπ₁, by rw [hpow]; omega, C₁, hC₁π, ?_, ?_⟩
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).1
        · exact fun l hl => (key true C₁ hC₁a hC₁S l hl (hnox l hl)).2
    · have hnox : ∀ l ∈ C₀, l.1 ≠ x := by
        intro l hl e
        have := onx false C₀ hC₀a l hl e
        simp at this
        exact h₀ (this ▸ hl)
      refine ⟨π₀, hπ₀, by rw [hpow]; omega, C₀, hC₀π, ?_, ?_⟩
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).1
      · exact fun l hl => (key false C₀ hC₀a hC₀S l hl (hnox l hl)).2

variable {V : Type} [DecidableEq V]
private def supported (D : Clause V) (S : Finset V) := ∀ l ∈ D, l.1 ∈ S

private theorem derived_support {S : Finset V} {F : Set (Clause V)}
    (hs : ∀ D ∈ F, supported D S) {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∀ D ∈ π, supported D S := by
  induction hπ with
  | nil => simp
  | ax _ h ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl|hD
    · exact hs _ h
    · exact ih _ hD
  | res _ hC hD hr ih =>
    intro D h
    rcases List.mem_cons.mp h with rfl|h
    · obtain ⟨v,_,_,rfl⟩ := hr
      intro l hl
      rcases Finset.mem_union.mp hl with h|h
      · exact ih _ hC _ (Finset.mem_erase.mp h).2
      · exact ih _ hD _ (Finset.mem_erase.mp h).2
    · exact ih _ h

theorem compileLocal (U : Finset V) (F : Set (Clause V)) (C : Clause V)
    (hU : ∀ D ∈ F, supported D U)
    (a : V → Bool) (ha : ¬ ClauseSat a C)
    (entails : ∀ x : V → Bool, Satisfies x F → ClauseSat x C) :
    ∃ π : List (Clause V), IsDerivation F π ∧ π.length + 1 ≤ 2^(U.card+1) ∧
      (∀ D ∈ π, D.card ≤ 2*U.card) ∧ ∃ D ∈ π, D ⊆ C := by
  classical
  let S := U \ C.image Prod.fst
  have bad (b : V → Bool) (hb : ∀ v, v ∉ S → b v = a v) :
      ∃ D ∈ F, ¬ ClauseSat b D := by
    by_contra! good
    obtain ⟨l,hl,he⟩ := entails b good
    have hz : l.1 ∉ S := by
      intro hm
      exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_image_of_mem _ hl)
    exact ha ⟨l,hl,(hb l.1 hz).symm.trans he⟩
  obtain ⟨π,hπ,hcnt,D,hD,hfalse,hn⟩ := completeness_aux F S a bad
  have supp := derived_support hU hπ
  have hsc : S.card ≤ U.card := Finset.card_le_card Finset.sdiff_subset
  refine ⟨π,hπ,hcnt.trans (Nat.pow_le_pow_right (by decide) (by omega)),?_,D,hD,?_⟩
  · intro E hE
    have sub : E ⊆ U ×ˢ (Finset.univ : Finset Bool) := fun l hl =>
      Finset.mem_product.mpr ⟨supp _ hE l hl, Finset.mem_univ _⟩
    simpa [Nat.mul_comm] using Finset.card_le_card sub
  · intro l hl
    have hi : l.1 ∈ C.image Prod.fst := by
      by_contra hh
      exact hn l hl (Finset.mem_sdiff.mpr ⟨supp _ hD l hl,hh⟩)
    obtain ⟨k,hk,hkl⟩ := Finset.mem_image.mp hi
    have hks : a k.1 ≠ k.2 := fun he => ha ⟨k,hk,he⟩
    have hls := hfalse l hl
    obtain ⟨v,t⟩ := k
    obtain ⟨w,s⟩ := l
    change v = w at hkl
    subst w
    change a v ≠ t at hks
    change a v ≠ s at hls
    have eq : s = t := by cases a v <;> cases s <;> cases t <;> simp_all
    simpa [eq] using hk

end BlockQuotaLocal

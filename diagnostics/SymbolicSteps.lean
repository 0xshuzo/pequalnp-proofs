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

namespace BlockQuotaLocal
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

private theorem replay {F : Set (Clause V)} {π : List (Clause V)} (hπ : IsDerivation F π)
    {H : Set (Clause V)} (src : ∀ D ∈ H, D ∈ F ∨ D ∈ π) {τ : List (Clause V)} (hτ : IsDerivation H τ) :
    ∃ p : List (Clause V), IsDerivation F (p ++ π) ∧ p.length ≤ τ.length ∧
      (∀ D ∈ p, D ∈ τ) ∧ ∀ D ∈ τ, D ∈ p ++ π := by
  induction hτ with
  | nil => exact ⟨[],hπ,by simp,by simp,by simp⟩
  | ax _ hc ih =>
    obtain ⟨p,hp,hl,hs,ht⟩ := ih
    rcases src _ hc with h | h
    · refine ⟨_::p,.ax hp h,by simpa using hl,?_,?_⟩
      · intro D hD
        rcases List.mem_cons.mp hD with rfl|hD
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hs _ hD)
      · intro D hD
        rcases List.mem_cons.mp hD with rfl|hD
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ht _ hD)
    · refine ⟨p,hp,by simp only [List.length_cons]; omega,?_,?_⟩
      · exact fun D hD => List.mem_cons_of_mem _ (hs D hD)
      · intro D hD
        rcases List.mem_cons.mp hD with rfl|hD
        · exact List.mem_append_right _ h
        · exact ht _ hD
  | res _ hc hd hr ih =>
    obtain ⟨p,hp,hl,hs,ht⟩ := ih
    refine ⟨_::p,.res hp (ht _ hc) (ht _ hd) hr,by simpa using hl,?_,?_⟩
    · intro D hD
      rcases List.mem_cons.mp hD with rfl|hD
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs _ hD)
    · intro D hD
      rcases List.mem_cons.mp hD with rfl|hD
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ht _ hD)

def LocalProof (F : Set (Clause V)) (k : ℕ) : List (Clause V) → Prop
    | [] => True
    | C :: tail => LocalProof F k tail ∧
      ∃ U : Finset V, U.card ≤ k ∧ (∃ a : V → Bool, ¬ ClauseSat a C) ∧
        ∀ a : V → Bool, (∀ D, (D ∈ F ∨ D ∈ tail) → supported D U → ClauseSat a D) → ClauseSat a C

theorem compileChain (F : Set (Clause V)) (k : ℕ) (L : List (Clause V))
    (h : LocalProof F k L) :
    ∃ π : List (Clause V), IsDerivation F π ∧ π.length ≤ L.length * 2^(k+1) ∧
      (∀ D ∈ π, D.card ≤ 2*k) ∧ (∀ C ∈ L, ∃ D ∈ π, D ⊆ C) := by
  classical
  induction L with
  | nil => exact ⟨[],.nil,by simp,by simp,by simp⟩
  | cons C L ih =>
    obtain ⟨hl,U,hU,⟨a,ha⟩,hm⟩ := h
    obtain ⟨π,hπ,len,hw,mem⟩ := ih hl
    let H : Set (Clause V) := {D | (D ∈ F ∨ D ∈ π) ∧ supported D U}
    have ent (x : V → Bool) (hxs : Satisfies x H) : ClauseSat x C := by
      apply hm x
      intro D hd hD
      rcases hd with h|h
      · exact hxs _ ⟨Or.inl h,hD⟩
      · obtain ⟨E,hE,he⟩ := mem _ h
        have sub : supported E U := fun l m => hD l (he m)
        obtain ⟨l,hls,ht⟩ := hxs E ⟨Or.inr hE,sub⟩
        exact ⟨l,he hls,ht⟩
    obtain ⟨τ,ht,tl,w,E,hE,he⟩ := compileLocal U H C (fun _ hd => hd.2) a ha ent
    obtain ⟨p,hp,pl,hps,hpt⟩ := replay hπ (fun D (hd : D ∈ H) => hd.1) ht
    refine ⟨p++π,hp,?_,?_,?_⟩
    · have powle : 2^(U.card+1) ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [List.length_append,List.length_cons,Nat.add_mul]
      omega
    · intro D hd
      rcases List.mem_append.mp hd with hs|hs
      · exact (w D (hps _ hs)).trans (by omega)
      · exact hw _ hs
    · intro D hd
      rcases List.mem_cons.mp hd with rfl|hd
      · exact ⟨E,hpt _ hE,he⟩
      · obtain ⟨G,hG,hGD⟩ := mem _ hd
        exact ⟨G,List.mem_append_right _ hG,hGD⟩

theorem finishChain (F : Set (Clause V)) (k : ℕ) (L : List (Clause V))
    (h : LocalProof F k L) (zero : (∅ : Clause V) ∈ L) :
    ∃ π : List (Clause V), IsRefutation F π ∧ π.length ≤ L.length * 2^(k+1) ∧
      ∀ D ∈ π, D.card ≤ 2*k := by
  obtain ⟨π,hπ,len,w,mem⟩ := compileChain F k L h
  obtain ⟨D,hd,he⟩ := mem _ zero
  have eq : D = ∅ := Finset.eq_empty_of_forall_notMem fun l hl => Finset.notMem_empty l (he hl)
  exact ⟨π,⟨hπ,eq ▸ hd⟩,len,w⟩
end BlockQuotaLocal

namespace BlockQuotaLocal
open PEqualNP.ProofComplexity
variable {V : Type} [DecidableEq V]

def deny (U : Finset V) (b : ↥U → Bool) : Clause V :=
  U.attach.image (fun u => (u.val,!(b u)))

noncomputable def table (U : Finset V) (ok : (↥U → Bool) → Bool) : List (Clause V) :=
  ((Finset.univ : Finset (↥U → Bool)).filter (fun b => ok b = false)).toList.map (deny U)

theorem deny_sat (U : Finset V) (b : ↥U → Bool) (x : V → Bool) :
    ClauseSat x (deny U b) ↔ ∃ u : ↥U, x u.val ≠ b u := by
  have flip (p q : Bool) : p = (!q) ↔ p ≠ q := by cases p <;> cases q <;> decide
  constructor
  · rintro ⟨l,hl,he⟩
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hl
    exact ⟨u,(flip _ _).mp he⟩
  · rintro ⟨u,hu⟩
    exact ⟨(u.val,!(b u)), Finset.mem_image_of_mem _ (Finset.mem_attach _ u),(flip _ _).mpr hu⟩

theorem table_size (U : Finset V) (ok : (↥U → Bool) → Bool) :
    (table U ok).length ≤ 2^U.card := by
  classical
  simpa [table] using (Finset.card_filter_le (s := (Finset.univ : Finset (↥U → Bool))) (p := fun b => ok b = false))

theorem table_decodes (U : Finset V) (ok : (↥U → Bool) → Bool) (x : V → Bool) :
    (∀ D ∈ table U ok, ClauseSat x D) ↔ ok (fun u => x u.val) = true := by
  classical
  have hm (b : ↥U → Bool) (hb : ok b = false) : deny U b ∈ table U ok := by
    apply List.mem_map.mpr
    exact ⟨b, by simpa using hb,rfl⟩
  constructor
  · intro hh
    cases h : ok (fun u => x u.val) with
    | true => rfl
    | false =>
      obtain ⟨u,hu⟩ := (deny_sat _ _ _).mp (hh _ (hm _ h))
      exact (hu rfl).elim
  · intro hx D hD
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hD
    have he : ok b = false := by simpa using hb
    apply (deny_sat _ _ _).mpr
    by_contra! hh
    have eq : (fun (u : ↥U) => x u.val) = b := funext hh
    rw [eq,he] at hx
    contradiction

theorem emitTable (F : Set (Clause V)) (k : ℕ) (L : List (Clause V)) (hL : LocalProof F k L)
    (U S : Finset V) (ok : (↥U → Bool) → Bool) (bound : S.card ≤ k)
    (entails : ∀ x : V → Bool,
      (∀ D, (D ∈ F ∨ D ∈ L) → supported D S → ClauseSat x D) → ok (fun u => x u.val) = true) :
    LocalProof F k (table U ok ++ L) := by
  classical
  have aux (P : List (Clause V)) (hp : ∀ D ∈ P, D ∈ table U ok) : LocalProof F k (P++L) := by
    induction P with
    | nil => exact hL
    | cons D P ih =>
      have hd := hp D List.mem_cons_self
      obtain ⟨b,hb,hDb⟩ := List.mem_map.mp hd
      refine ⟨ih (fun E hE => hp E (List.mem_cons_of_mem _ hE)), S, bound, ?_, ?_⟩
      · let z (v : V) := if h : v ∈ U then b ⟨v,h⟩ else false
        refine ⟨z,?_⟩
        rw [← hDb,deny_sat]
        rintro ⟨u,hu⟩
        exact hu (by simp [z,u.property])
      · intro x hx
        have okx := entails x (fun E hE hs => hx E (hE.imp_right (List.mem_append_right P)) hs)
        exact (table_decodes U ok x).mpr okx D (hp D List.mem_cons_self)
  exact aux _ (fun _ h => h)
end BlockQuotaLocal

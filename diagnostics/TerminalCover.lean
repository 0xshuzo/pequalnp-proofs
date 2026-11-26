import PEqualNP.Outside.L_meta_3289

namespace PlaneTerminal
open PEqualNP.Outside.L_meta_3289

set_option maxHeartbeats 5000000 in
theorem terminal_cover {n s out : ℕ} (R : ℕ → List ℕ) (run : (Fin n → Bool) → ℕ → Bool)
    (hin : ∀ (S : Fin n → Bool) (i : Fin n), run S i.val = S i)
    (hbig : ∀ S i, n + s ≤ i → run S i = false)
    (hlen : ∀ k, (R k).length ≤ 2)
    (hg : ∀ (S S' : Fin n → Bool) (k : ℕ), n ≤ k → k < n + s → (∀ r ∈ R k, r < k → run S r = run S' r) →
      run S k = run S' k)
    (hmono : ∀ (S S' : Fin n → Bool), (∀ i, S i = true → S' i = true) → ∀ w, run S w = true → run S' w = true)
    (hsing : ∀ x : Fin n, run (pt x x) out = false)
    (hK : ∀ x y z z' : Fin n, x ≠ y → z ≠ z' → run (pt x z) out = true → run (pt x z') out = true →
      run (pt y z) out = true → run (pt y z') out = true → False)
    (X : Finset (Fin n)) (hX : ∀ x ∈ X, ∃ z, run (pt x z) out = true)
    (Two : Fin n → Prop)
    (hTwo : ∀ x, Two x → x ∈ X ∧ ∃ z z', z ≠ z' ∧ run (pt x z) out = true ∧ run (pt x z') out = true) :
    ∃ A ⊆ X, X.card + A.card ≤ s + 1 ∧ ∀ x z, x ∉ A → z ∉ A → Two x → Two z → run (pt x z) out = true → False := by
  classical
  have comm (x z : Fin n) : pt x z = pt z x := by
    funext j
    simp only [pt, or_comm]
  have ptx (x z : Fin n) : pt x z x = true := by simp [pt]
  have ptz (x z : Fin n) : pt x z z = true := by simp [pt]
  have sub (x z : Fin n) (i : Fin n) (h : pt x x i = true) : pt x z i = true := by
    simp only [pt, or_self, decide_eq_true_eq] at h
    simp [pt, h]
  have sub' (x z : Fin n) (i : Fin n) (h : pt z z i = true) : pt x z i = true := by
    simp only [pt, or_self, decide_eq_true_eq] at h
    simp [pt, h]
  have off (x z : Fin n) (i : Fin n) (h : i ≠ x) : pt x z i = pt z z i := by
    simp [pt, h]
  rcases X.eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩
  · subst hemp
    refine ⟨∅, by simp, by simp, ?_⟩
    intro x z _ _ h
    simpa using (hTwo x h).1
  obtain ⟨z0, hz0⟩ := hX x0 hx0
  have hout1 : out < n + s := by
    by_contra h
    rw [hbig _ _ (by omega)] at hz0
    exact Bool.false_ne_true hz0
  have hout0 : n ≤ out := by
    by_contra h
    have e2 := hsing ⟨out, by omega⟩
    have e3 := hin (pt (⟨out, by omega⟩ : Fin n) ⟨out, by omega⟩) ⟨out, by omega⟩
    rw [ptx] at e3
    simp only at e3
    rw [e3] at e2
    exact absurd e2 (by simp)
  let closed : Finset ℕ → Prop := fun L => out ∈ L ∧ ∀ k ∈ L, ∀ r ∈ R k, r < k → n ≤ r → r ∈ L
  obtain ⟨L, hLm, hLmin⟩ := Finset.exists_min_image ((Finset.Ico n (n + s)).powerset.filter closed)
    Finset.card ⟨Finset.Ico n (n + s), by
      refine Finset.mem_filter.mpr ⟨by simp, by simp [hout0, hout1], ?_⟩
      intro k hk r _ h1 h2
      rw [Finset.mem_Ico] at hk ⊢
      omega⟩
  rw [Finset.mem_filter, Finset.mem_powerset] at hLm
  obtain ⟨hLs, hLo, hLc⟩ := hLm
  have hLn : ∀ k ∈ L, n ≤ k := fun k h => (Finset.mem_Ico.mp (hLs h)).1
  have hLk : ∀ k ∈ L, k < n + s := fun k h => (Finset.mem_Ico.mp (hLs h)).2
  have live : ∀ g ∈ L, g ≠ out → ∃ k ∈ L, g ∈ R k ∧ g < k := by
    intro g hgL hgo
    by_contra hno
    have h := hLmin (L.erase g) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      ((Finset.erase_subset _ _).trans hLs), Finset.mem_erase.mpr ⟨fun h => hgo h.symm, hLo⟩, ?_⟩)
    · have := Finset.card_erase_lt_of_mem hgL
      omega
    · intro k hk r hr h1 h2
      have hk' := Finset.mem_of_mem_erase hk
      refine Finset.mem_erase.mpr ⟨?_, hLc k hk' r hr h1 h2⟩
      rintro rfl
      exact hno ⟨k, hk', hr, h1⟩
  have hgL : ∀ (S S' : Fin n → Bool), ∀ k ∈ L, (∀ r ∈ R k, r < k → run S r = run S' r) → run S k = run S' k :=
    fun S S' k h => hg S S' k (hLn k h) (hLk k h)
  have ag := fun D => agree L D R run hin hLn hLc hgL
  let Pos : Finset (ℕ × ℕ) := (L ×ˢ Finset.range 2).filter fun p =>
    p.2 < (R p.1).length ∧ (R p.1).getD p.2 0 < p.1
  let tgt : ℕ × ℕ → ℕ := fun p => (R p.1).getD p.2 0
  let f : ℕ → ℕ := fun w => (Pos.filter fun p => tgt p = w).card
  have posof : ∀ k ∈ L, ∀ w ∈ R k, w < k → ∃ i, (k, i) ∈ Pos.filter fun p => tgt p = w := by
    intro k hk w hw hwk
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hw
    have e : (R k).getD i 0 = w := by
      rw [List.getD_eq_getElem?_getD]
      simp [hi, hiw]
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk,
      Finset.mem_range.mpr ?_⟩, hi, ?_⟩, e⟩⟩
    · have := hlen k
      omega
    · simp only [e]
      exact hwk
  let Dom : Fin n → ℕ → Finset ℕ → Prop := fun x c D => x.val ∈ D ∧ c ∈ D ∧ (c = x.val ∨ c ∈ L) ∧
    (∀ w ∈ D, run (pt x x) w = true) ∧ ∀ w ∈ D, w ≠ c → ∀ k ∈ L, w ∈ R k → w < k → k ∈ D
  have outD : ∀ x c D, Dom x c D → out ∉ D := by
    intro x c D h ho
    have := h.2.2.2.1 out ho
    rw [hsing x] at this
    exact Bool.false_ne_true this
  have cut : ∀ x c D, Dom x c D → ∀ S S' : Fin n → Bool, (∀ i, i ≠ x → S i = S' i) → run S c = run S' c →
      run S out = run S' out := by
    intro x c D h S S' hS hc
    refine ag (D.erase c) S S' ?_ (out + 1) ?_ out (by omega) (Or.inr hLo)
      (fun ho => outD x c D h (Finset.mem_of_mem_erase ho))
    · intro i hi
      by_cases hix : i = x
      · subst hix
        have : i.val = c := by
          by_contra hne
          exact hi (Finset.mem_erase.mpr ⟨hne, h.1⟩)
        rw [← this, hin, hin] at hc
        exact hc
      · exact hS i hix
    · rintro k _ hk hkD ⟨r, hr, hrk, hrD⟩
      rw [Finset.mem_erase] at hrD
      have hkD' := h.2.2.2.2 r hrD.2 hrD.1 k hk hr hrk
      have : k = c := by
        by_contra hne
        exact hkD (Finset.mem_erase.mpr ⟨hne, hkD'⟩)
      rw [this]
      exact hc
  have rdx : ∀ x ∈ X, ∃ k ∈ L, x.val ∈ R k ∧ x.val < k := by
    intro x hx
    obtain ⟨z, hz⟩ := hX x hx
    by_contra hno
    have e := ag {x.val} (pt x z) (pt z z) ?_ (out + 1) ?_ out (by omega) (Or.inr hLo) ?_
    · rw [hz, hsing] at e
      exact absurd e (by simp)
    · intro i hi
      refine off x z i ?_
      rintro rfl
      simp at hi
    · rintro k _ hk _ ⟨r, hr, hrk, hrD⟩
      rw [Finset.mem_singleton] at hrD
      subst hrD
      exact (hno ⟨k, hk, hr, hrk⟩).elim
    · rw [Finset.mem_singleton]
      have := x.isLt
      omega
  have rdc : ∀ x c D, x ∈ X → Dom x c D → ∃ k ∈ L, c ∈ R k ∧ c < k := by
    intro x c D hx h
    rcases h.2.2.1 with e | e
    · rw [e]
      exact rdx x hx
    · refine live c e ?_
      rintro rfl
      exact outD x _ D h h.2.1
  let Term : Fin n → ℕ → Finset ℕ → Prop := fun x c D => Dom x c D ∧ (2 ≤ f c ∨ ∃ k ∈ L, c ∈ R k ∧ c < k ∧
    run (pt x x) k = false ∧ ∀ k' ∈ L, c ∈ R k' → c < k' → k' = k)
  have climb : ∀ (d : ℕ) x c D, x ∈ X → Dom x c D → n + s ≤ c + d → ∃ c' D', Term x c' D' := by
    intro d
    induction d with
    | zero =>
      intro x c D hx h hd
      obtain ⟨k, hk, _, h2⟩ := rdc x c D hx h
      have := hLk k hk
      omega
    | succ d ih =>
      intro x c D hx h hd
      by_cases h2 : 2 ≤ f c
      · exact ⟨c, D, h, Or.inl h2⟩
      obtain ⟨k, hk, hck, hlt⟩ := rdc x c D hx h
      have uni : ∀ k' ∈ L, c ∈ R k' → c < k' → k' = k := by
        intro k' hk' hck' hlt'
        obtain ⟨i, hi⟩ := posof k hk c hck hlt
        obtain ⟨i', hi'⟩ := posof k' hk' c hck' hlt'
        have : (Pos.filter fun p => tgt p = c).card ≤ 1 := by
          have : f c ≤ 1 := by omega
          exact this
        have := Finset.card_le_one.mp this _ hi _ hi'
        exact (congrArg Prod.fst this).symm
      cases hv : run (pt x x) k with
      | false => exact ⟨c, D, h, Or.inr ⟨k, hk, hck, hlt, hv, uni⟩⟩
      | true =>
        refine ih x k (insert k D) hx ⟨Finset.mem_insert_of_mem h.1, Finset.mem_insert_self _ _, Or.inr hk, ?_, ?_⟩
          (by omega)
        · intro w hw
          rcases Finset.mem_insert.mp hw with e | e
          · rw [e]
            exact hv
          · exact h.2.2.2.1 w e
        · intro w hw hwk k' hk' hr hlt'
          have hwD := (Finset.mem_insert.mp hw).resolve_left hwk
          by_cases hwc : w = c
          · subst hwc
            rw [uni k' hk' hr hlt']
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (h.2.2.2.2 w hwD hwc k' hk' hr hlt')
  have term : ∀ x, ∃ c D, x ∈ X → Term x c D := by
    intro x
    by_cases hx : x ∈ X
    · obtain ⟨c, D, h⟩ := climb (n + s) x x.val {x.val} hx ⟨by simp, by simp, Or.inl rfl, by
        intro w hw
        rw [Finset.mem_singleton] at hw
        rw [hw, hin]
        exact ptx x x, by
        intro w hw hne
        exact (hne (Finset.mem_singleton.mp hw)).elim⟩ (by omega)
      exact ⟨c, D, fun _ => h⟩
    · exact ⟨0, ∅, fun h => (hx h).elim⟩
  choose e D he using term
  have solo : ∀ x y, Two x → run (pt y y) (e x) = true → x = y := by
    intro x y hx hc
    by_contra hne
    obtain ⟨hxX, z, z', hzz, hz, hz'⟩ := hTwo x hx
    have hdx := (he x hxX).1
    have key : ∀ z, run (pt x z) out = true → run (pt y z) out = true := by
      intro z hz
      have h1 : run (pt y z) (e x) = true := hmono _ _ (sub y z) _ hc
      have h2 : run (fun i => pt y z i || decide (i = x)) (e x) = true :=
        hmono (pt y z) _ (fun i hi => by simp [hi]) _ h1
      rw [cut x (e x) (D x) hdx (pt y z) (fun i => pt y z i || decide (i = x)) (fun i hi => by simp [hi])
        (by rw [h1, h2])]
      refine hmono (pt x z) _ (fun i hi => ?_) _ hz
      simp only [pt, decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [pt, hi]
    exact hK x y z z' hne hzz hz hz' (key z hz) (key z' hz')
  have inj : ∀ x y, Two x → Two y → e x = e y → x = y := by
    intro x y hx hy hxy
    by_contra hne
    obtain ⟨hxX, z, z', hzz, hz, hz'⟩ := hTwo x hx
    have hdx := (he x hxX).1
    have hdy := (he y (hTwo y hy).1).1
    have key : ∀ z, run (pt x z) out = true → run (pt y z) out = true := by
      intro z hz
      have hc : run (pt y y) (e x) = true := by
        rw [hxy]
        exact hdy.2.2.2.1 _ hdy.2.1
      have h1 : run (pt y z) (e x) = true := hmono _ _ (sub y z) _ hc
      have h2 : run (fun i => pt y z i || decide (i = x)) (e x) = true :=
        hmono (pt y z) _ (fun i hi => by simp [hi]) _ h1
      rw [cut x (e x) (D x) hdx (pt y z) (fun i => pt y z i || decide (i = x)) (fun i hi => by simp [hi])
        (by rw [h1, h2])]
      refine hmono (pt x z) _ (fun i hi => ?_) _ hz
      simp only [pt, decide_eq_true_eq] at hi
      rcases hi with hi | hi <;> simp [pt, hi]
    exact hK x y z z' hne hzz hz hz' (key z hz) (key z' hz')
  let A : Finset (Fin n) := X.filter fun x => Two x ∧ 2 ≤ f (e x)
  refine ⟨A, Finset.filter_subset _ _, ?_, ?_⟩
  · let W0 : Finset ℕ := X.image (fun x => x.val) ∪ L.erase out
    have cX : (X.image (fun x => x.val)).card = X.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have dis : Disjoint (X.image (fun x => x.val)) (L.erase out) := by
      refine Finset.disjoint_left.mpr fun a h1 h2 => ?_
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h1
      have := hLn _ (Finset.mem_of_mem_erase h2)
      have := x.isLt
      omega
    have cW : W0.card = X.card + (L.card - 1) := by
      rw [Finset.card_union_of_disjoint dis, cX, Finset.card_erase_of_mem hLo]
    have cL : L.card ≤ s := by
      have := Finset.card_le_card hLs
      simpa using this
    have cL0 : 0 < L.card := Finset.card_pos.mpr ⟨out, hLo⟩
    have one : ∀ w ∈ W0, 1 ≤ f w := by
      intro w hw
      have : ∃ k ∈ L, w ∈ R k ∧ w < k := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
          exact rdx x hx
        · rw [Finset.mem_erase] at h
          exact live w h.2 h.1
      obtain ⟨k, hk, h1, h2⟩ := this
      obtain ⟨i, hi⟩ := posof k hk w h1 h2
      exact Finset.card_pos.mpr ⟨_, hi⟩
    have big : A.card ≤ (W0.filter fun w => 2 ≤ f w).card := by
      refine Finset.card_le_card_of_injOn e ?_ ?_
      · intro x hx
        have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
        have hd := (he x hx'.1).1
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hx'.2.2⟩)
        rcases hd.2.2.1 with h | h
        · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx'.1, h.symm⟩)
        · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, h⟩)
          intro h'
          exact outD _ _ _ hd (h' ▸ hd.2.1)
      · intro x hx y hy hxy
        exact inj x y (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2.1
          (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2.1 hxy
    have sum1 : W0.card + (W0.filter fun w => 2 ≤ f w).card ≤ ∑ w ∈ W0, f w := by
      rw [Finset.card_eq_sum_ones, Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun w hw => ?_
      have := one w hw
      split <;> omega
    have sum2 : ∑ w ∈ W0, f w ≤ Pos.card := by
      have h := Finset.card_eq_sum_card_fiberwise (f := tgt) (s := Pos.filter fun p => tgt p ∈ W0) (t := W0)
        (fun p hp => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2)
      have h2 : ∑ w ∈ W0, f w = ∑ w ∈ W0, ((Pos.filter fun p => tgt p ∈ W0).filter fun p => tgt p = w).card := by
        refine Finset.sum_congr rfl fun w hw => ?_
        refine congrArg Finset.card ?_
        ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨⟨a, b ▸ hw⟩, b⟩
        · rintro ⟨⟨a, _⟩, b⟩
          exact ⟨a, b⟩
      rw [h2, ← h]
      exact Finset.card_filter_le _ _
    have sum3 : Pos.card ≤ L.card * 2 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_range]
    omega
  · have nolt : ∀ x z cx Dx cz Dz kx kz, Dom x cx Dx → Dom z cz Dz → kx ∈ L → run (pt x x) kx = false →
        (∀ k' ∈ L, cx ∈ R k' → cx < k' → k' = kx) → (∀ k' ∈ L, cz ∈ R k' → cz < k' → k' = kz) →
        run (pt x z) out = true → ¬ kx < kz := by
      intro x z cx Dx cz Dz kx kz dx dz hkx vx ux uz hxz hlt
      have a1 : run (pt x z) kx ≠ run (pt z z) kx := by
        intro heq
        have := ag Dx (pt x z) (pt z z) ?_ (out + 1) ?_ out (by omega) (Or.inr hLo) (outD _ _ _ dx)
        · rw [hxz, hsing] at this
          exact absurd this (by simp)
        · intro i hi
          refine off x z i ?_
          rintro rfl
          exact hi dx.1
        · rintro k _ hk hkD ⟨r, hr, hrk, hrD⟩
          by_cases hrc : r = cx
          · subst hrc
            rw [ux k hk hr hrk]
            exact heq
          · exact (hkD (dx.2.2.2.2 r hrD hrc k hk hr hrk)).elim
      have a2 : run (pt z z) kx = false := by
        cases h : run (pt z z) kx with
        | false => rfl
        | true => exact (a1 (by rw [h, hmono _ _ (sub' x z) _ h])).elim
      have a3 : run (pt x z) kx = true := by
        cases h : run (pt x z) kx with
        | true => rfl
        | false => exact (a1 (by rw [h, a2])).elim
      have a4 : run (pt x z) kx = run (pt x x) kx := by
        refine ag Dz (pt x z) (pt x x) ?_ kz ?_ kx hlt (Or.inr hkx) ?_
        · intro i hi
          rw [comm x z]
          refine off z x i ?_
          rintro rfl
          exact hi dz.1
        · rintro k hkb hk hkD ⟨r, hr, hrk, hrD⟩
          by_cases hrc : r = cz
          · subst hrc
            have := uz k hk hr hrk
            omega
          · exact (hkD (dz.2.2.2.2 r hrD hrc k hk hr hrk)).elim
        · intro h
          have := dz.2.2.2.1 _ h
          rw [a2] at this
          exact Bool.false_ne_true this
      rw [a3, vx] at a4
      exact absurd a4 (by simp)
    have small : ∀ x, x ∉ A → Two x → ∃ k ∈ L, e x ∈ R k ∧ run (pt x x) k = false ∧
        ∀ k' ∈ L, e x ∈ R k' → e x < k' → k' = k := by
      intro x hxA hx
      have hxX := (hTwo x hx).1
      rcases (he x hxX).2 with h | ⟨k, h1, h2, _, h3, h4⟩
      · exact (hxA (Finset.mem_filter.mpr ⟨hxX, hx, h⟩)).elim
      · exact ⟨k, h1, h2, h3, h4⟩
    have same : ∀ x z, x ∉ A → z ∉ A → Two x → Two z → run (pt x z) out = true → ∀ k kz,
        (k ∈ L ∧ run (pt x x) k = false ∧ ∀ k' ∈ L, e x ∈ R k' → e x < k' → k' = k) →
        (kz ∈ L ∧ run (pt z z) kz = false ∧ ∀ k' ∈ L, e z ∈ R k' → e z < k' → k' = kz) → k = kz := by
      intro x z _ _ hx hz hxz k kz ⟨h1, h2, h3⟩ ⟨j1, j2, j3⟩
      have dx := (he x (hTwo x hx).1).1
      have dz := (he z (hTwo z hz).1).1
      have b1 := nolt x z (e x) (D x) (e z) (D z) k kz dx dz h1 h2 h3 j3 hxz
      have b2 := nolt z x (e z) (D z) (e x) (D x) kz k dz dx j1 j2 j3 h3 (by rw [comm z x]; exact hxz)
      omega
    intro x z hxA hzA hx hz hxz
    obtain ⟨k, hk, rx, kx, ux⟩ := small x hxA hx
    obtain ⟨j, hj, rz, kz, uz⟩ := small z hzA hz
    have keq := same x z hxA hzA hx hz hxz k j ⟨hk,kx,ux⟩ ⟨hj,kz,uz⟩
    subst j
    have dx := (he x (hTwo x hx).1).1
    have dz := (he z (hTwo z hz).1).1
    have xz : x ≠ z := by
      rintro rfl
      rw [hsing] at hxz
      contradiction
    have exz : e x ≠ e z := fun eq => xz (inj x z hx hz eq)
    have sing (w : Fin n) (ne : z ≠ w) : run (pt w w) (e z) = false := by
      cases hw : run (pt w w) (e z) with
      | false => rfl
      | true => exact (ne (solo z w hz hw)).elim
    obtain ⟨w, wz, xw⟩ : ∃ w, z ≠ w ∧ run (pt x w) out = true := by
      obtain ⟨_,u,v,uv,xu,xv⟩ := hTwo x hx
      by_cases zz : z = u
      · exact ⟨v,by simpa only [zz] using uv,xv⟩
      · exact ⟨u,zz,xu⟩
    have ezout : e z ∉ D x := by
      intro mem
      have h := dx.2.2.2.1 _ mem
      rw [sing x xz.symm] at h
      contradiction
    obtain ⟨j,hj',rj,ltj⟩ := rdc z (e z) (D z) (hTwo z hz).1 dz
    have lt : e z < k := by simpa only [uz j hj' rj ltj] using ltj
    have place : e z < n ∨ e z ∈ L := by
      rcases dz.2.2.1 with eq|mem
      · exact Or.inl (by simpa only [eq] using z.isLt)
      · exact Or.inr mem
    have before : run (pt x w) (e z) = run (pt w w) (e z) := by
      refine ag (D x) (pt x w) (pt w w) ?_ k ?_ (e z) lt place ezout
      · intro i hi
        apply off x w i
        rintro rfl
        exact hi dx.1
      · rintro t tk tL tD ⟨r,rt,lt',rD⟩
        by_cases eq : r = e x
        · subst r
          have := ux t tL rt lt'
          omega
        · exact (tD (dx.2.2.2.2 r rD eq t tL rt lt')).elim
    have args (r : ℕ) (rm : r ∈ R k) : r = e x ∨ r = e z := by
      by_contra! bad
      have sub : ({r,e x,e z} : Finset ℕ) ⊆ (R k).toFinset := by
        simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff,List.mem_toFinset]
        exact ⟨rm,rx,rz⟩
      have h := (Finset.card_le_card sub).trans (List.toFinset_card_le (R k))
      simp [bad.1,bad.2,exz] at h
      have := hlen k
      omega
    have gateEq : run (pt x w) k = run (pt x x) k := by
      apply hgL _ _ k hk
      intro r rm _
      rcases args r rm with rfl|rfl
      · have on := dx.2.2.2.1 _ dx.2.1
        rw [on,hmono _ _ (sub x w) _ on]
      · rw [before,sing w wz,sing x xz.symm]
    have offPair : run (pt x w) k = false := gateEq.trans kx
    have offW : run (pt w w) k = false := by
      cases h : run (pt w w) k with
      | false => rfl
      | true =>
        have h' := hmono _ _ (sub' x w) k h
        rw [offPair] at h'
        contradiction
    have eqOut : run (pt x w) out = run (pt w w) out := by
      refine ag (D x) (pt x w) (pt w w) ?_ (out+1) ?_ out (by omega) (Or.inr hLo) (outD _ _ _ dx)
      · intro i hi
        apply off x w i
        rintro rfl
        exact hi dx.1
      · rintro t _ tL tD ⟨r,rt,lt',rD⟩
        by_cases eq : r = e x
        · subst r
          rw [ux t tL rt lt',offPair,offW]
        · exact (tD (dx.2.2.2.2 r rD eq t tL rt lt')).elim
    rw [xw,hsing] at eqOut
    contradiction

end PlaneTerminal

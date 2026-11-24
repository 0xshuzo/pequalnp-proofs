import PEqualNP.Defs

open PEqualNP.GenericRejection PEqualNP.CircuitLowerBounds PEqualNP.TopForm
namespace SparsePlane

theorem overlap {N : ℕ} (S : Fin N → Finset (Fin N))
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    {l m : Fin N} (hne : l ≠ m) : (S l ∩ S m).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro p hp r hr
  by_contra e
  obtain ⟨u, _, hu⟩ := join p r e
  exact hne ((hu l ⟨(Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hr).1⟩).trans
    (hu m ⟨(Finset.mem_inter.mp hp).2, (Finset.mem_inter.mp hr).2⟩).symm)

theorem privateCount {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y : Finset (Fin N)) {l : Fin N} (hl : l ∉ Y) :
    q+1 ≤ Y.card + (S l ∩ zeroSet S Y).card := by
  classical
  let cap := Y.biUnion fun m => S l ∩ S m
  have hc : cap.card ≤ Y.card := by
    simpa [cap] using Finset.card_biUnion_le_card_mul Y (fun m => S l ∩ S m) 1
      (fun m hm => overlap S join (fun h => hl (h ▸ hm)))
  have incl : S l ⊆ cap ∪ (S l ∩ zeroSet S Y) := by
    intro p hp
    by_cases h : ∃ m ∈ Y, p ∈ S m
    · obtain ⟨m, hm, hpm⟩ := h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hp,hpm⟩⟩)
    · refine Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, ?_⟩)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun m hm hp' => h ⟨m,hm,hp'⟩⟩
  have hb := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  rw [weight] at hb
  omega

theorem testGeometry {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (Y Z : Finset (Fin N)) (small : Y.card ≤ q) :
    IsFalseInput S (zeroSet S Y) Z ↔ Z ⊆ Y := by
  constructor
  · intro hf l hl
    by_contra h
    have hc := privateCount S weight join Y h
    have he := Finset.disjoint_iff_inter_eq_empty.mp (hf l hl)
    rw [he] at hc
    simp only [Finset.card_empty, Nat.add_zero] at hc
    omega
  · intro inc l hl
    exact Finset.disjoint_left.mpr fun p hp hpz => (Finset.mem_filter.mp hpz).2 l (inc hl) hp

theorem erasure {q N : ℕ} (S : Fin N → Finset (Fin N))
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (p : Fin N) {Y Z : Finset (Fin N)} (hy : Y.card ≤ q) (hz : Z.card ≤ q)
    (agree : ∀ r : Fin N, r ≠ p → (r ∈ zeroSet S Y ↔ r ∈ zeroSet S Z)) :
    Y = Z := by
  classical
  have inclusion (A B : Finset (Fin N)) (ha : A.card ≤ q) (hb : B.card ≤ q)
      (he : ∀ r : Fin N, r ≠ p → (r ∈ zeroSet S A ↔ r ∈ zeroSet S B)) : A ⊆ B := by
    intro l hl
    by_contra h
    have privateP (l : Fin N) (hl : l ∈ A) :
        S l ∩ zeroSet S B ⊆ {p} := by
      intro r hr
      have both := Finset.mem_inter.mp hr
      by_contra hne
      have hrp : r ≠ p := by simpa using hne
      exact (Finset.mem_filter.mp ((he r hrp).2 both.2)).2 l hl both.1
    have bound := privateCount S weight join B h
    have one := Finset.card_le_card (privateP l hl)
    simp only [Finset.card_singleton] at one
    have hbq : B.card = q := by omega
    have hn : 0 < (S l ∩ zeroSet S B).card := by omega
    obtain ⟨r,hr⟩ := Finset.card_pos.mp hn
    have rp : r = p := Finset.mem_singleton.mp (privateP l hl hr)
    have pB : p ∈ zeroSet S B := rp ▸ (Finset.mem_inter.mp hr).2
    have rev : B ⊆ A := by
      intro m hm
      by_contra hmA
      have cnt := privateCount S weight join A hmA
      have pos : 0 < (S m ∩ zeroSet S A).card := by omega
      obtain ⟨t,ht⟩ := Finset.card_pos.mp pos
      have both := Finset.mem_inter.mp ht
      by_cases htp : t = p
      · exact (Finset.mem_filter.mp pB).2 m hm (htp ▸ both.1)
      · exact (Finset.mem_filter.mp ((he t htp).1 both.2)).2 m hm both.1
    have eq : B = A := Finset.eq_of_subset_of_card_le rev (by omega)
    exact h (eq ▸ hl)
  exact Finset.Subset.antisymm (inclusion Y Z hy hz agree)
    (inclusion Z Y hz hy fun r hr => (agree r hr).symm)

theorem optimumDecodedSupport {q N : ℕ} (S : Fin N → Finset (Fin N))
    (hN : q+1 < N)
    (weight : ∀ l, (S l).card = q+1)
    (join : ∀ p r : Fin N, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l)
    (l : Fin N) :
    ∃ (T : Finset (Fin N)) (decode : Finset (Fin N) → Bool),
      (T ∩ S l).card = q ∧
      (∀ X X' : Finset (Fin N), (∀ p ∈ T, p ∈ X ↔ p ∈ X') → decode X = decode X') ∧
      ∀ Y : Finset (Fin N), Y.card ≤ q → decode (zeroSet S Y) = decide (l ∉ Y) := by
  classical
  have pos : 0 < (S l).card := by rw [weight]; omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp pos
  let T : Finset (Fin N) := Finset.univ.erase p
  let dec (X : Finset (Fin N)) := decide (∃ Y : Finset (Fin N), Y.card ≤ q ∧ l ∉ Y ∧
    ∀ r : Fin N, r ≠ p → (r ∈ X ↔ r ∈ zeroSet S Y))
  refine ⟨T,dec,?_,?_,?_⟩
  · have hset : T ∩ S l = (S l).erase p := by ext r; simp [T, and_comm]
    rw [hset]
    have hc := Finset.card_erase_add_one hp
    rw [weight] at hc
    omega
  · intro X X' eq
    have hx (r : Fin N) (hr : r ≠ p) := eq r (by simp [T,hr])
    change decide _ = decide _
    apply decide_congr
    constructor
    · rintro ⟨Y,hy,hl,he⟩
      exact ⟨Y,hy,hl,fun r hr => (hx r hr).symm.trans (he r hr)⟩
    · rintro ⟨Y,hy,hl,he⟩
      exact ⟨Y,hy,hl,fun r hr => (hx r hr).trans (he r hr)⟩
  · intro Y hy
    by_cases h : l ∈ Y
    · have no : ¬ ∃ U : Finset (Fin N), U.card ≤ q ∧ l ∉ U ∧
          ∀ r : Fin N, r ≠ p → (r ∈ zeroSet S Y ↔ r ∈ zeroSet S U) := by
        rintro ⟨U,hu,hl,he⟩
        exact hl (erasure S weight join p hy hu he ▸ h)
      simp [dec,no,h]
    · have yes : ∃ U : Finset (Fin N), U.card ≤ q ∧ l ∉ U ∧
          ∀ r : Fin N, r ≠ p → (r ∈ zeroSet S Y ↔ r ∈ zeroSet S U) :=
        ⟨Y,hy,h,fun _ _ => Iff.rfl⟩
      simp [dec,yes,h]

end SparsePlane

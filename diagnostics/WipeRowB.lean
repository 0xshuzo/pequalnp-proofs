import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166_research

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev LiteralSat (a : V → Bool) (l : Literal V) : Prop := a l.1 = l.2

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

theorem colAx_comm (i k : Row) (j : Hole) : colAx i k j = colAx k i j :=
  Finset.pair_comm ((i, j), false) ((k, j), false)

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem collisionNoPos {N : C} (hN : Coll N) (v : V) : (v, true) ∉ N := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem collisionOther {N : C} {v : V} (hN : Coll N) (hv : (v, false) ∈ N) :
    ∃ u : V, u ≠ v ∧ (u, false) ∈ N := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  rcases hv' with rfl | rfl
  · exact ⟨(k, j), fun e => hik (congrArg Prod.fst e).symm, by simp [colAx]⟩
  · exact ⟨(i, j), fun e => hik (congrArg Prod.fst e), by simp [colAx]⟩

theorem collisionNonempty {N : C} (hN : Coll N) : N ≠ ∅ := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem col_same_hole {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) : v.2 = u.2 := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl <;> rfl

theorem col_eq_colAx {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) (huv : u ≠ v) :
    v.1 ≠ u.1 ∧ v.2 = u.2 ∧ N = colAx v.1 u.1 u.2 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl
  · exact (huv rfl).elim
  · exact ⟨hik, rfl, rfl⟩
  · exact ⟨hik.symm, rfl, colAx_comm i k j⟩
  · exact (huv rfl).elim

theorem negLeft {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ P) :
    (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hu⟩)

theorem negRight {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ N)
    (hne : u ≠ v) : (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simpa using hne, hu⟩)

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 5 4 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

theorem indispensablePHP {B : C} : B ∈ PHP 5 4 ↔
    (∃ r : Row, B = rowAx r Finset.univ) ∨ Collision Finset.univ Finset.univ B := by
  change ((∃ r : Row, B = rowAx r Finset.univ) ∨
    (∃ i k : Row, ∃ j : Hole, i ≠ k ∧ B = colAx i k j)) ↔ _
  constructor
  · rintro (hr | ⟨i, k, j, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _, hik, he⟩
  · rintro (hr | ⟨i, _, k, _, j, _, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, k, j, hik, he⟩

theorem indispensableSatRow {a : V → Bool} {J : Finset Hole} {r : Row} {j : Hole}
    (hj : j ∈ J) (h : a (r, j) = true) : ClauseSat a (rowAx r J) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, hj, rfl⟩, h⟩

theorem indispensableSatCol {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

def ValidMatch (i k : Row) (j : Hole) (f : Row → Hole) : Prop :=
  (∀ r, r ≠ i → r ≠ k → f r ≠ j) ∧
  (∀ r₁ r₂, r₁ ≠ i → r₁ ≠ k → r₂ ≠ i → r₂ ≠ k → f r₁ = f r₂ → r₁ = r₂)

def validMatchB (i k : Row) (j : Hole) (f : Row → Hole) : Bool :=
  ((List.finRange 5).all fun r => decide (r = i) || decide (r = k) || decide (f r ≠ j)) &&
  ((List.finRange 5).all fun r₁ => (List.finRange 5).all fun r₂ =>
    decide (r₁ = i) || decide (r₁ = k) || decide (r₂ = i) || decide (r₂ = k) ||
    decide (f r₁ ≠ f r₂) || decide (r₁ = r₂))

theorem validMatch_of_bool {i k : Row} {j : Hole} {f : Row → Hole}
    (h : validMatchB i k j f = true) : ValidMatch i k j f := by
  unfold validMatchB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_⟩
  · intro r hri hrk
    rcases h.1 r with (h1 | h2) | h3
    · exact (hri h1).elim
    · exact (hrk h2).elim
    · exact h3
  · intro r₁ r₂ h1i h1k h2i h2k heq
    rcases h.2 r₁ r₂ with (((((h1 | h2) | h3) | h4) | h5) | h6)
    · exact (h1i h1).elim
    · exact (h1k h2).elim
    · exact (h2i h3).elim
    · exact (h2k h4).elim
    · exact (h5 heq).elim
    · exact h6

def colModel (i k : Row) (j : Hole) (f : Row → Hole) : V → Bool :=
  fun w => if w.1 = i ∨ w.1 = k then decide (w.2 = j) else decide (f w.1 = w.2)

theorem colModel_unsat {i k : Row} {j : Hole} {f : Row → Hole} :
    ¬ ClauseSat (colModel i k j f) (colAx i k j) := by
  rintro ⟨l, hl, hal⟩
  simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl <;> simp [colModel] at hal

theorem colModel_sat_other {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, D ≠ colAx i k j → ClauseSat (colModel i k j f) D := by
  intro D hD hne
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | ⟨r, _, s, _, q, _, hrs, rfl⟩
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · apply indispensableSatCol
    rintro ⟨hr, hs⟩
    by_cases hri : r = i ∨ r = k <;> by_cases hsi : s = i ∨ s = k
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      subst hr
      apply hne
      rcases hri with hri' | hri' <;> rcases hsi with hsi' | hsi'
      · exact (hrs (hri'.trans hsi'.symm)).elim
      · rw [hri', hsi']
      · rw [hri', hsi']; exact colAx_comm k i q
      · exact (hrs (hri'.trans hsi'.symm)).elim
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hsi
      exact hf.1 s hsi.1 hsi.2 (hs.trans hr)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri
      exact hf.1 r hri.1 hri.2 (hr.trans hs)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri hsi
      exact hrs (hf.2 r s hri.1 hri.2 hsi.1 hsi.2 (hr.trans hs.symm))

theorem colModel_sat_rows {i k : Row} {j : Hole} {f : Row → Hole}
    (_hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat (colModel i k j f) D := by
  intro D hD hnc
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | hc
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · exact (hnc hc).elim

theorem colModel_sat_cols {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D, Coll D → D ≠ colAx i k j → ClauseSat (colModel i k j f) D :=
  fun D hD hne => colModel_sat_other hf D (collisionPHP hD) hne

theorem exists_validMatch (i k : Row) (hik : i ≠ k) (j : Hole) :
    ∃ f : Row → Hole, ValidMatch i k j f := by
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hc : (((Finset.univ : Finset Row).erase i).erase k).card =
      ((Finset.univ : Finset Hole).erase j).card := by
    rw [Finset.card_erase_of_mem hkm, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
  let e : ↥(((Finset.univ : Finset Row).erase i).erase k) ≃
      ↥((Finset.univ : Finset Hole).erase j) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  refine ⟨fun r => if hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k
      then (e ⟨r, hr⟩).1 else 0, ?_, ?_⟩
  · intro r hri hrk
    have hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
    simp only [hr, ↓reduceDIte]
    exact (Finset.mem_erase.mp (e ⟨r, hr⟩).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    have hr₁ : r₁ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩
    have hr₂ : r₂ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩
    simp only [hr₁, hr₂, ↓reduceDIte] at heq
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_map (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) (hqj : q₀ ≠ j) :
    ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ = q₀ := by
  let A : Finset Row := (((Finset.univ : Finset Row).erase i).erase k).erase r₀
  let B : Finset Hole := ((Finset.univ : Finset Hole).erase j).erase q₀
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hrm : r₀ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
    Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
  have hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j :=
    Finset.mem_erase.mpr ⟨hqj, Finset.mem_univ _⟩
  have hc : A.card = B.card := by
    dsimp only [A, B]
    rw [Finset.card_erase_of_mem hrm, Finset.card_erase_of_mem hkm,
      Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem (Finset.mem_univ j)]
    decide +kernel
  let e : ↥A ≃ ↥B := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let f : Row → Hole := fun r =>
    if r = r₀ then q₀ else if hr : r ∈ A then (e ⟨r, hr⟩).1 else 0
  refine ⟨f, ⟨?_, ?_⟩, by simp [f]⟩
  · intro r hri' hrk'
    by_cases hr0 : r = r₀
    · simp [f, hr0, hqj]
    · have hrA : r ∈ A := Finset.mem_erase.mpr
        ⟨hr0, Finset.mem_erase.mpr ⟨hrk', Finset.mem_erase.mpr ⟨hri', Finset.mem_univ _⟩⟩⟩
      simp only [f, hr0, hrA, ↓reduceIte, ↓reduceDIte]
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (e ⟨r, hrA⟩).2).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    by_cases h1 : r₁ = r₀ <;> by_cases h2 : r₂ = r₀
    · exact h1.trans h2.symm
    · have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₂, hr₂A⟩).2).1 heq.symm).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₁, hr₁A⟩).2).1 heq).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_avoid (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) : ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ ≠ q₀ := by
  have hne : (((Finset.univ : Finset Hole).erase j).erase q₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hc : (((Finset.univ : Finset Hole).erase j).erase q₀).card = 0 := by simp [he]
    have h1 : ((Finset.univ : Finset Hole).erase j).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
    have h2 : (((Finset.univ : Finset Hole).erase j).erase q₀).card ≥ 2 := by
      have := Finset.card_erase_le (a := q₀) (s := (Finset.univ : Finset Hole).erase j)
      by_cases hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j
      · rw [Finset.card_erase_of_mem hqm, h1]
      · rw [Finset.erase_eq_of_notMem hqm, h1]; omega
    omega
  obtain ⟨q₁, hq₁⟩ := hne
  have hq₁q₀ : q₁ ≠ q₀ := (Finset.mem_erase.mp hq₁).1
  have hq₁j : q₁ ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hq₁).2).1
  obtain ⟨f, hf, hfr⟩ := exists_validMatch_map i k r₀ hik hri hrk j q₁ hq₁j
  exact ⟨f, hf, hfr.symm ▸ hq₁q₀⟩

theorem indispensableRowModel (i : Row) :
    ∃ a : V → Bool, ¬ ClauseSat a (rowAx i Finset.univ) ∧
      ∀ R ∈ PHP 5 4, R ≠ rowAx i Finset.univ → ClauseSat a R := by
  have hc : ((Finset.univ : Finset Row).erase i).card = (Finset.univ : Finset Hole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; decide +kernel
  let e : ↥((Finset.univ : Finset Row).erase i) ≃ ↥(Finset.univ : Finset Hole) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let a : V → Bool := fun w =>
    if hr : w.1 ∈ (Finset.univ : Finset Row).erase i then decide ((e ⟨w.1, hr⟩ : Hole) = w.2)
    else false
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    have hnot : i ∉ (Finset.univ : Finset Row).erase i := Finset.notMem_erase i Finset.univ
    simp only [a, hnot, ↓reduceDIte] at hal
    cases hal
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, j, _, hrs, rfl⟩
    · have hri : r ≠ i := fun he => hne (congrArg (fun r => rowAx r Finset.univ) he)
      have hr : r ∈ (Finset.univ : Finset Row).erase i := Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩
      exact indispensableSatRow (Finset.mem_univ (e ⟨r, hr⟩).1) (by simp only [a, hr, ↓reduceDIte, decide_true])
    · apply indispensableSatCol
      rintro ⟨hr, hs⟩
      by_cases hri : r ∈ (Finset.univ : Finset Row).erase i <;>
        by_cases hsi : s ∈ (Finset.univ : Finset Row).erase i
      · simp only [a, hri, hsi, ↓reduceDIte, decide_eq_true_eq] at hr hs
        exact hrs (congrArg Subtype.val (e.injective (Subtype.ext (hr.trans hs.symm))))
      · simp only [a, hsi, ↓reduceDIte] at hs; cases hs
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr

theorem critical {B : C} (hB : B ∈ PHP 5 4) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 5 4, D ≠ B → ClauseSat a D := by
  rcases indispensablePHP.mp hB with ⟨i, rfl⟩ | ⟨i, _, k, _, j, _, hik, rfl⟩
  · exact indispensableRowModel i
  · obtain ⟨f, hf⟩ := exists_validMatch i k hik j
    exact ⟨colModel i k j f, colModel_unsat, colModel_sat_other hf⟩

def holeColBank (j : Hole) : Finset C :=
  ((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)).image
    (fun p => colAx p.1 p.2 j)

theorem mem_holeColBank {j : Hole} {B : C} :
    B ∈ holeColBank j ↔ ∃ i k : Row, i ≠ k ∧ B = colAx i k j := by
  unfold holeColBank
  constructor
  · intro hB
    obtain ⟨⟨i, k⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, k, ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, k, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem holeColBank_card (j : Hole) : (holeColBank j).card = 10 := by
  have hinj : Set.InjOn (fun p : Row × Row => colAx p.1 p.2 j)
      (((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)) : Set _) := by
    intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    have m2 : ((k1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold holeColBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Coll B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _,
      ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, _, k, _, j, _, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem collisionBank_card : collisionBank.card = 40 := by
  have hinj : Set.InjOn (fun p : Row × Row × Hole => colAx p.1 p.2.1 p.2.2)
      (((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)) : Set _) := by
    intro ⟨i1, k1, j1⟩ h1 ⟨i2, k2, j2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    have m2 : ((k1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold collisionBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def axiomBank : Finset C :=
  (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) ∪ collisionBank

theorem mem_axiomBank (B : C) : B ∈ axiomBank ↔ B ∈ PHP 5 4 := by
  rw [indispensablePHP]
  simp only [axiomBank, Finset.mem_union, mem_collisionBank, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h

theorem axiomBank_card : axiomBank.card = 45 := by
  have hdisj : Disjoint (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) collisionBank := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hB1
    have hc : Coll (rowAx r Finset.univ) := (mem_collisionBank _).mp hB2
    exact collisionNoPos hc (r, 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hrow : (Finset.univ.image (fun r : Row => rowAx r Finset.univ)).card = 5 := by
    have hinj : Function.Injective (fun r : Row => rowAx r Finset.univ) := by
      intro r1 r2 heq
      dsimp only at heq
      have hm : ((r1, (0 : Hole)), true) ∈ rowAx r2 Finset.univ :=
        heq ▸ Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨_, _, he⟩ := Finset.mem_image.mp hm
      exact (Prod.mk.inj (Prod.mk.inj he).1).1.symm
    rw [Finset.card_image_of_injective _ hinj]
    decide +kernel
  unfold axiomBank
  rw [Finset.card_union_of_disjoint hdisj, hrow, collisionBank_card]

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

inductive Step where
  | ax (R : C)
  | col (N : C) (v u : V) (R : C)
  | non (v : V) (R : C)
  deriving DecidableEq

def clauseOf : Step → C
  | Step.ax R => R
  | Step.col _ _ _ R => R
  | Step.non _ R => R

inductive ValidTrace : List Step → Prop
  | nil : ValidTrace []
  | ax {tr : List Step} {R : C} :
      ValidTrace tr → R ∈ PHP 5 4 → ValidTrace (Step.ax R :: tr)
  | col {tr : List Step} {P N R : C} {v u : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      Coll N → (v, true) ∈ P → (v, false) ∈ N →
      u ≠ v → (u, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.col N v u R :: tr)
  | non {tr : List Step} {P N R : C} {v : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      ¬ Coll N → (v, true) ∈ P → (v, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.non v R :: tr)

theorem of_isDerivation {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃ tr : List Step, tr.map clauseOf = π ∧ ValidTrace tr := by
  classical
  induction h with
  | nil => exact ⟨[], rfl, ValidTrace.nil⟩
  | @ax π R _ hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    exact ⟨Step.ax R :: tr, by simp [clauseOf, hmap], ValidTrace.ax htr hR⟩
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    obtain ⟨v, hp, hn, heq⟩ := hR
    by_cases hcol : Coll N
    · obtain ⟨u, huv, hu⟩ := collisionOther hcol hn
      exact ⟨Step.col N v u R :: tr, by simp [clauseOf, hmap],
        ValidTrace.col htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn huv hu heq⟩
    · exact ⟨Step.non v R :: tr, by simp [clauseOf, hmap],
        ValidTrace.non htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn heq⟩

theorem ValidTrace.tail {s : Step} {tr : List Step} (h : ValidTrace (s :: tr)) : ValidTrace tr := by
  cases h <;> assumption

theorem ValidTrace.drop {tr : List Step} (h : ValidTrace tr) : ∀ k : ℕ, ValidTrace (tr.drop k) := by
  induction tr with
  | nil => intro k; simp [ValidTrace.nil]
  | cons s tl ih =>
    intro k
    cases k with
    | zero => exact h
    | succ k' => exact ih h.tail k'

theorem ValidTrace.col_mem_info {tr : List Step} (h : ValidTrace tr) {N : C} {v u : V} {R : C}
    (hm : Step.col N v u R ∈ tr) :
    Coll N ∧ (v, false) ∈ N ∧ (u, false) ∈ N ∧ u ≠ v ∧ N ∈ holeColBank u.2 := by
  induction h with
  | nil => cases hm
  | ax _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'
  | @col tr' P N' R' v' u' _ _ _ hcol _ hn huv hu _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
      obtain ⟨hne, hhole, hax⟩ := col_eq_colAx hcol hn hu huv
      exact ⟨hcol, hn, hu, huv, mem_holeColBank.mpr ⟨v.1, u.1, hne, hax⟩⟩
    · exact ih hm'
  | non _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'


def Bad (a : V → Bool) (tr : List Step) : Prop :=
  ∃ N v u R, Step.col N v u R ∈ tr ∧ ¬Coll R ∧ ¬ClauseSat a N ∧ ¬ClauseSat a R

theorem Bad.cons {a : V → Bool} {tr : List Step} (b : Bad a tr) (s : Step) :
    Bad a (s::tr) := by
  rcases b with ⟨N,v,u,R,m,n,q,h⟩
  exact ⟨N,v,u,R,List.mem_cons_of_mem _ m,n,q,h⟩

theorem boundary {tr : List Step} (h : ValidTrace tr) (a : V → Bool)
    (rows : ∀ D ∈ PHP 5 4, ¬Coll D → ClauseSat a D) :
    ∀ Q ∈ tr.map clauseOf, ¬Coll Q → ¬ClauseSat a Q → Bad a tr := by
  induction h with
  | nil => simp
  | ax prev hx ih =>
    intro Q mem n f
    rcases List.mem_cons.mp mem with eq|tail
    · subst Q
      exact (f (rows _ hx n)).elim
    · exact (ih Q tail n f).cons _
  | @col tr P N R v u prev pp nn nc pv nv ne nu eq ih =>
    intro Q mem n f
    rcases List.mem_cons.mp mem with he|tail
    · subst Q
      change ¬ClauseSat a R at f
      by_cases hn : ClauseSat a N
      · have no : ¬ClauseSat a P := fun hp => f (satResolve eq hp hn)
        exact (ih P pp (fun hc => collisionNoPos hc v pv) no).cons _
      · exact ⟨N,v,u,R,by simp,n,hn,f⟩
    · exact (ih Q tail n f).cons _
  | @non tr P N R v prev pp nn nc pv nv eq ih =>
    intro Q mem n f
    rcases List.mem_cons.mp mem with he|tail
    · subst Q
      change ¬ClauseSat a R at f
      by_cases hn : ClauseSat a N
      · have no : ¬ClauseSat a P := fun hp => f (satResolve eq hp hn)
        exact (ih P pp (fun hc => collisionNoPos hc v pv) no).cons _
      · exact (ih N nn nc hn).cons _
    · exact (ih Q tail n f).cons _

def dense (S : Finset Hole) (w : V) : Bool := decide (w.2 ∈ S)
theorem denseBoundary {tr : List Step} (valid : ValidTrace tr) (empty : (∅:C)∈tr.map clauseOf)
    (S : Finset Hole) (nonempty : S.Nonempty) :
    ∃ N v u R, Step.col N v u R ∈ tr ∧ ¬Coll R ∧
      u.2 ∈ S ∧ ∀ w : V, (w,true)∈R → w.2 ∉ S := by
  obtain ⟨j,hj⟩ := nonempty
  have rows : ∀ D ∈ PHP 5 4, ¬Coll D → ClauseSat (dense S) D := by
    intro D hd hn
    rcases indispensablePHP.mp hd with ⟨i,rfl⟩|hc
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [dense,hj])
    · exact (hn hc).elim
  obtain ⟨N,v,u,R,hm,n,fn,fr⟩ := boundary valid _ rows _ empty
    (fun hc => collisionNonempty hc rfl) (emptyUnsat _)
  have hu := (valid.col_mem_info hm).2.2.1
  refine ⟨N,v,u,R,hm,n,?_,?_⟩
  · by_contra hh
    exact fn ⟨(u,false),hu,by simp [dense,hh]⟩
  · intro w hw hs
    exact fr ⟨(w,true),hw,by simp [dense,hs]⟩

def SameChild (tr : List Step) (B : C) : Prop :=
  ∀ v u R v' u' R', Step.col B v u R ∈ tr → Step.col B v' u' R' ∈ tr → R=R'

theorem single_false {tr : List Step} (valid : ValidTrace tr) (empty : (∅:C)∈tr.map clauseOf)
    {i k : Row} {j : Hole} {v u : V} {R : C}
    (hm : Step.col (colAx i k j) v u R ∈ tr) (single : SameChild tr (colAx i k j))
    {f : Row → Hole} (hf : ValidMatch i k j f) : ¬ ClauseSat (colModel i k j f) R := by
  obtain ⟨B,w,z,T,t,_,fb,ft⟩ := boundary valid _ (colModel_sat_rows hf) _ empty
    (fun hc => collisionNonempty hc rfl) (emptyUnsat _)
  have eb : B=colAx i k j := by
    by_contra ne
    exact fb (colModel_sat_cols hf _ (valid.col_mem_info t).1 ne)
  subst B
  rw [single _ _ _ _ _ _ hm t]
  exact ft

theorem avoiding (i k : Row) (j : Hole) (diff : i≠k) (w : V)
    (a : w≠(i,j)) (b : w≠(k,j)) :
    ∃ f : Row → Hole, ValidMatch i k j f ∧ colModel i k j f w=false := by
  by_cases h : w.1=i ∨ w.1=k
  · obtain ⟨f,hf⟩ := exists_validMatch i k diff j
    have ne : w.2≠j := by
      intro e
      rcases h with r|r
      · exact a (Prod.ext r e)
      · exact b (Prod.ext r e)
    exact ⟨f,hf,by simp [colModel,h,ne]⟩
  · obtain ⟨f,hf,ne⟩ := exists_validMatch_avoid i k w.1 diff (fun q=>h (Or.inl q)) (fun q=>h (Or.inr q)) j w.2
    exact ⟨f,hf,by simp [colModel,h,ne]⟩

theorem raw_result {tr : List Step} (valid : ValidTrace tr)
    {N : C} {v u : V} {R : C} (mem : Step.col N v u R ∈ tr) :
    ∃ P ∈ tr.map clauseOf, (v,true)∈P ∧ R=P.erase (v,true) ∪ N.erase (v,false) := by
  induction valid with
  | nil => cases mem
  | ax _ _ ih =>
    rcases List.mem_cons.mp mem with eq|m
    · cases eq
    · obtain ⟨P,p,h,e⟩ := ih m
      exact ⟨P,List.mem_cons_of_mem _ p,h,e⟩
  | col _ pp _ _ pv _ _ _ eq ih =>
    rcases List.mem_cons.mp mem with e|m
    · cases e
      exact ⟨_,List.mem_cons_of_mem _ pp,pv,eq⟩
    · obtain ⟨P,p,h,e⟩ := ih m
      exact ⟨P,List.mem_cons_of_mem _ p,h,e⟩
  | non _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp mem with e|m
    · cases e
    · obtain ⟨P,p,h,e⟩ := ih m
      exact ⟨P,List.mem_cons_of_mem _ p,h,e⟩

theorem first_unit_or_repeat {tr : List Step} (valid : ValidTrace tr)
    (empty : (∅:C)∈tr.map clauseOf) :
    ∃ N v u R, Step.col N v u R ∈ tr ∧ ¬Coll R ∧
      (∀ w : V, (w,true)∉R) ∧ (SameChild tr N → R={(u,false)}) := by
  obtain ⟨N,v,u,R,hm,nc,_,neg⟩ := denseBoundary valid empty Finset.univ ⟨0,Finset.mem_univ _⟩
  have np (w : V) : (w,true)∉R := fun m => neg w m (Finset.mem_univ _)
  refine ⟨N,v,u,R,hm,nc,np,?_⟩
  intro unique
  obtain ⟨coll,hv,hu,une,_⟩ := valid.col_mem_info hm
  obtain ⟨dif,same,en⟩ := col_eq_colAx coll hv hu une
  obtain ⟨P,_,_,eq⟩ := raw_result valid hm
  have uneg : (u,false)∈R := by
    rw [eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simpa using une,hu⟩)
  have only (w : V) (wm : (w,false)∈R) : w=v ∨ w=u := by
    by_contra hn
    have hv' : w≠(v.1,u.2) := by simpa [← same] using (fun e=>hn (Or.inl e) : w≠v)
    have hu' : w≠(u.1,u.2) := (fun e=>hn (Or.inr e) : w≠u)
    obtain ⟨f,hf,off⟩ := avoiding v.1 u.1 u.2 dif w hv' hu'
    have bad := single_false valid empty (en ▸ hm) (en ▸ unique) hf
    exact bad ⟨(w,false),wm,off⟩
  have vnot : (v,false)∉R := by
    intro vv
    apply nc
    have sameSet : R=N := by
      ext lit
      obtain ⟨w,b⟩ := lit
      cases b
      · constructor
        · intro h
          rcases only w h with rfl|rfl <;> assumption
        · intro h
          have wmem : w = (v.1,u.2) ∨ w = (u.1,u.2) := by simpa [en,colAx] using h
          rcases wmem with e|e
          · have : w=v := by simpa [← same] using e
            simpa [this] using vv
          · simpa [e] using uneg
      · simp [np w,collisionNoPos coll w]
    exact sameSet ▸ coll
  ext lit
  obtain ⟨w,b⟩ := lit
  cases b
  · simp only [Finset.mem_singleton,Prod.mk.injEq,and_true]
    constructor
    · intro h
      rcases only w h with e|e
      · exact (vnot (e ▸ h)).elim
      · exact e
    · rintro rfl; exact uneg
  · simp [np w]

-- A result is narrow when two different positive literals are missing in every row.
end PEqualNP.Outside.L_pcx_166_research
namespace PEqualNP.Outside.L_pcx_166_research

open PEqualNP.ProofComplexity

def shadow (v u : V) (l : PEqualNP.ProofComplexity.Literal V) : Prop :=
  if l.2 then l.1=v ∨ l.1=u ∨ (l.1.1≠v.1 ∧ l.1.1≠u.1 ∧ l.1.2≠u.2)
  else l.1≠v ∧ l.1≠u

theorem shadowWitness {v u : V} (dif : v.1≠u.1) (same : v.2=u.2)
    {l : PEqualNP.ProofComplexity.Literal V} (s : shadow v u l) :
    ∃ f, ValidMatch v.1 u.1 u.2 f ∧ LiteralSat (colModel v.1 u.1 u.2 f) l := by
  rcases l with ⟨w,b⟩
  cases b with
  | false =>
    change w≠v ∧ w≠u at s
    obtain ⟨f,hf,off⟩ := avoiding v.1 u.1 u.2 dif w
      (fun e=>s.1 (by simpa [←same] using e)) (fun e=>s.2 (by simpa using e))
    exact ⟨f,hf,off⟩
  | true =>
    change w=v ∨ w=u ∨ (w.1≠v.1 ∧ w.1≠u.1 ∧ w.2≠u.2) at s
    rcases s with eq|eq|⟨a,b,c⟩
    · subst w
      obtain ⟨f,hf⟩ := exists_validMatch v.1 u.1 dif u.2
      exact ⟨f,hf,by simp [LiteralSat,colModel,same]⟩
    · subst w
      obtain ⟨f,hf⟩ := exists_validMatch v.1 u.1 dif u.2
      exact ⟨f,hf,by simp [LiteralSat,colModel]⟩
    · obtain ⟨f,hf,yes⟩ := exists_validMatch_map v.1 u.1 w.1 dif a b u.2 w.2 c
      exact ⟨f,hf,by simp [LiteralSat,colModel,a,b,yes]⟩

def safeBoards (a : V → Bool) : Prop :=
  (∀ r : Row, ∃ h : Hole, a (r,h)=true) ∧
  ∀ v u : V, v.1≠u.1 → v.2=u.2 → a u=true → a v=true →
    ∃ k : Hole, k≠v.2 ∧ a (v.1,k)=true
def repairB (v u : V) (k : Hole) (x : V) : Bool :=
  if x.1=u.1 then decide (x.2=u.2)
  else if x.1=v.1 then decide (x.2=k)
  else decide (x.2≠u.2 ∧ x.2≠k)
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem goodRepair : ∀ v u : V, v.1≠u.1 → v.2=u.2 → ∀ k : Hole, k≠v.2 →
    safeBoards (repairB v u k) := by
  rintro ⟨r,h⟩ ⟨s,j⟩ rs same k ne
  change h=j at same
  subst j
  have free : ∀ i j g : Hole, ∃ w : Hole, w≠i ∧ w≠j ∧ w≠g := by decide +kernel
  have only : ∀ (a b p q : Row) (i j g : Hole), a≠b → i≠j → p≠q →
      repairB (a,i) (b,i) j (p,g)=true → repairB (a,i) (b,i) j (q,g)=true →
      p≠a ∧ p≠b := by
    unfold repairB
    decide +kernel
  constructor
  · intro p
    by_cases ueq : p=s
    · exact ⟨h,by simp [repairB,ueq]⟩
    by_cases veq : p=r
    · exact ⟨k,by simp [repairB,ueq,veq,show r≠s from rs]⟩
    obtain ⟨w,wh,wk,_⟩ := free h k h
    exact ⟨w,by simp [repairB,ueq,veq,wh,wk]⟩
  · rintro ⟨p,g⟩ ⟨q,x⟩ pq hg uon von
    change g=x at hg
    subst x
    have oo := only r s p q h k g rs (Ne.symm ne) pq von uon
    obtain ⟨w,wh,wk,wg⟩ := free h k g
    exact ⟨w,wg,by simp [repairB,oo.1,oo.2,wh,wk]⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem repairSource : ∀ v u : V, v.1≠u.1 → v.2=u.2 → ∀ k : Hole, k≠v.2 →
    ∀ l : PEqualNP.ProofComplexity.Literal V, LiteralSat (repairB v u k) l →
      l≠(v,false) → shadow v u l ∨ l=((v.1,k),true) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ ne eq k diff ⟨⟨r,h⟩,sign⟩
  change i=j at eq
  subst j
  change a≠b at ne
  change k≠i at diff
  by_cases rb : r=b <;> by_cases ra : r=a <;> by_cases hi : h=i <;> by_cases hk : h=k <;>
    cases sign <;> simp_all [LiteralSat,repairB,shadow,Prod.ext_iff]


def wipe (a : V → Bool) (v w : V) : Bool := if w=v then false else a w

theorem wipe_le {a : V → Bool} {v w : V} (on : wipe a v w=true) : a w=true := by
  by_cases eq : w=v
  · simp [wipe,eq] at on
  · simpa [wipe,eq] using on

theorem wipeSafe {a : V → Bool} (safe : safeBoards a) (v : V)
    (stable : ∀ h : Hole, h≠v.2 → a (v.1,h)=true →
      (∃ r : Row, r≠v.1 ∧ a (r,h)=true) →
      ∃ k : Hole, k≠h ∧ k≠v.2 ∧ a (v.1,k)=true)
    (other : ∃ k : Hole, k≠v.2 ∧ a (v.1,k)=true) : safeBoards (wipe a v) := by
  constructor
  · intro r
    by_cases eq : r=v.1
    · subst r
      obtain ⟨k,ne,on⟩ := other
      exact ⟨k,by simp [wipe,show (v.1,k)≠v from fun e=>ne (congrArg Prod.snd e),on]⟩
    · obtain ⟨k,on⟩ := safe.1 r
      exact ⟨k,by simp [wipe,show (r,k)≠v from fun e=>eq (congrArg Prod.fst e),on]⟩
  · intro x y d e yon xon
    have xa := wipe_le xon
    have ya := wipe_le yon
    by_cases atV : x.1=v.1
    · have hne : x.2≠v.2 := by
        intro j
        have eq := Prod.ext atV j
        simp [wipe,eq] at xon
      have xx : (v.1,x.2)=x := Prod.ext atV.symm rfl
      have yy : (y.1,x.2)=y := Prod.ext rfl e
      obtain ⟨k,kh,kv,on⟩ := stable x.2 hne (xx.symm ▸ xa)
        ⟨y.1,fun s=>d (atV.trans s.symm),yy.symm ▸ ya⟩
      refine ⟨k,kh,?_⟩
      have nv : (x.1,k)≠v := fun w=>kv (congrArg Prod.snd w)
      rw [wipe,if_neg nv,atV]
      exact on
    · obtain ⟨k,kh,on⟩ := safe.2 x y d e ya xa
      have nv : (x.1,k)≠v := fun w=>atV (congrArg Prod.fst w)
      exact ⟨k,kh,by simp [wipe,nv,on]⟩

theorem gateForcesUnsafeWipe {P N R : C} {v : V} {a : V → Bool}
    (clean : (v,false)∉P) (eq : R=P.erase (v,true) ∪ N.erase (v,false))
    (parent : ∀ b, safeBoards b → ClauseSat b P)
    (bad : ¬ClauseSat a R) : ¬safeBoards (wipe a v) := by
  intro safe
  obtain ⟨⟨w,b⟩,mem,on⟩ := parent _ safe
  by_cases isv : w=v
  · subst w
    cases b
    · exact clean mem
    · change wipe a v v=true at on
      simp [wipe] at on
  · have pair : (w,b)≠(v,true) := fun e=>isv (congrArg Prod.fst e)
    have rm : (w,b)∈R := by rw [eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨pair,mem⟩)
    exact bad ⟨(w,b),rm,by simpa [LiteralSat,wipe,isv] using on⟩

theorem exactTwoRow {P N R : C} {v u : V} {a : V → Bool}
    (coll : Coll N) (nv : (v,false)∈N) (nu : (u,false)∈N) (ne : u≠v)
    (clean : (v,false)∉P) (eq : R=P.erase (v,true) ∪ N.erase (v,false))
    (parent : ∀ b, safeBoards b → ClauseSat b P)
    (good : safeBoards a) (bad : ¬ClauseSat a R) :
    ∃ h : Hole, h≠v.2 ∧
      (∀ k : Hole, a (v.1,k)=true ↔ k=v.2 ∨ k=h) ∧
      ∃ r : Row, r≠v.1 ∧ a (r,h)=true := by
  classical
  have ns : ¬ClauseSat a N := fun hn => bad (satResolve eq (parent a good) hn)
  obtain ⟨dif,same,_⟩ := col_eq_colAx coll nv nu ne
  have tu : a u=true := by cases h : a u <;> first | rfl | exact (ns ⟨(u,false),nu,h⟩).elim
  have tv : a v=true := by cases h : a v <;> first | rfl | exact (ns ⟨(v,false),nv,h⟩).elim
  have other := good.2 v u dif same tu tv
  have failed := gateForcesUnsafeWipe clean eq parent bad
  by_contra no
  apply failed
  apply wipeSafe good v ?_ other
  intro h nh ah share
  by_contra noSpare
  apply no
  refine ⟨h,nh,?_,share⟩
  intro k
  constructor
  · intro on
    by_cases eq : k=v.2
    · exact Or.inl eq
    by_cases kh : k=h
    · exact Or.inr kh
    exact (noSpare ⟨k,kh,eq,on⟩).elim
  · rintro (rfl|rfl)
    · exact tv
    · exact ah

end PEqualNP.Outside.L_pcx_166_research

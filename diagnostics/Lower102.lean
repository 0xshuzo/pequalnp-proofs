import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_164_lower101

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def NegsIn (S : Finset V) (R : C) : Prop :=
  ∀ v : V, (v, false) ∈ R → v ∈ S

def Hits (S : Finset V) (R : C) : Prop :=
  ∃ v : V, (v, false) ∈ R ∧ v ∈ S

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

def Controls (π : List C) (U : Finset C) (S : Finset V) : Prop :=
  ∀ (U' : Finset C) (S' : Finset V), U ⊆ U' → S ⊆ S' →
  ∀ a : V → Bool, (∀ B ∈ PHP 5 4, ¬ Coll B → ClauseSat a B) →
    (∀ B ∈ U', Coll B → Hits S' B → ClauseSat a B) →
    ∀ R ∈ π, ¬ Coll R → NegsIn S' R → ClauseSat a R

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

theorem controlStep {π : List C} {U : Finset C} {S : Finset V} {v : V} {P N R : C}
    (h : Controls π U S) (hP : P ∈ π) (hN : N ∈ π)
    (hp : (v, true) ∈ P) (hn : (v, false) ∈ N)
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) :
    ∀ (U' : Finset C) (S' : Finset V), U ⊆ U' → S ⊆ S' →
    (Coll N → N ∈ U') → (¬ Coll N → v ∈ S') →
    ∀ a : V → Bool, (∀ B ∈ PHP 5 4, ¬ Coll B → ClauseSat a B) →
      (∀ B ∈ U', Coll B → Hits S' B → ClauseSat a B) →
      ∀ Q ∈ R :: π, ¬ Coll Q → NegsIn S' Q → ClauseSat a Q := by
  classical
  intro U' S' hU hS hmark hpivot a hrows hcols Q hQ hnQ hneg
  have ih := h U' S' hU hS a hrows hcols
  rcases List.mem_cons.mp hQ with rfl | hQ
  · have sP : ClauseSat a P :=
      ih P hP (fun hcol => collisionNoPos hcol v hp) (fun u hu => hneg u (negLeft hR hu))
    have sN : ClauseSat a N := by
      by_cases hcol : Coll N
      · obtain ⟨u, huv, hu⟩ := collisionOther hcol hn
        exact hcols N (hmark hcol) hcol ⟨u, hu, hneg u (negRight hR hu huv)⟩
      · refine ih N hN hcol (fun u hu => ?_)
        by_cases hu' : u = v
        · simpa [hu'] using hpivot hcol
        · exact hneg u (negRight hR hu hu')
    exact satResolve hR sP sN
  · exact ih Q hQ hnQ hneg

theorem collect {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃ (A U : Finset C) (S : Finset V), A.card + U.card + S.card ≤ π.length ∧
      Absorbs π A ∧ Controls π U S := by
  classical
  induction h with
  | nil =>
    refine ⟨∅, ∅, ∅, by simp, ?_, ?_⟩
    · simp [Absorbs]
    · simp [Controls]
  | @ax π R _ hR ih =>
    obtain ⟨A, U, S, hbudget, hs, hc⟩ := ih
    refine ⟨insert R A, U, S, ?_, ?_, ?_⟩
    · have := Finset.card_insert_le R A
      simp only [List.length_cons]
      omega
    · intro a ha Q hQ
      rcases List.mem_cons.mp hQ with hEq | hQ
      · subst Q
        exact ha R (Finset.mem_insert_self _ _) hR
      · exact hs a (fun B hB hB' => ha B (Finset.mem_insert_of_mem hB) hB') Q hQ
    · intro U' S' hU hS a hrows hcols Q hQ hnc hneg
      rcases List.mem_cons.mp hQ with hEq | hQ
      · subst Q
        exact hrows R hR hnc
      · exact hc U' S' hU hS a hrows hcols Q hQ hnc hneg
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨v, hp, hn, heq⟩ := hR
    obtain ⟨A, U, S, hbudget, hs, hc⟩ := ih
    have ha : Absorbs (R :: π) A := by
      intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact satResolve heq (hs a hA P hP) (hs a hA N hN)
      · exact hs a hA Q hQ
    have hstep := controlStep hc hP hN hp hn heq
    by_cases hm : Coll N
    · refine ⟨A, insert N U, S, ?_, ha, ?_⟩
      · have := Finset.card_insert_le N U
        simp only [List.length_cons]
        omega
      · intro U' S' hU hS
        exact hstep U' S' ((Finset.subset_insert N U).trans hU) hS
          (fun _ => hU (Finset.mem_insert_self _ _)) (fun h => (h hm).elim)
    · refine ⟨A, U, insert v S, ?_, ha, ?_⟩
      · have := Finset.card_insert_le v S
        simp only [List.length_cons]
        omega
      · intro U' S' hU hS
        exact hstep U' S' hU ((Finset.subset_insert v S).trans hS)
          (fun h => (hm h).elim) (fun _ => hS (Finset.mem_insert_self _ _))

theorem coverSize (S : Finset V)
    (hS : ∀ B : C, Coll B → Hits S B) : 16 ≤ S.card := by
  have hle : (Sᶜ).card ≤ (Finset.univ : Finset Hole).card := by
    apply Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_univ _)
    intro v hv w hw hej
    have hv' : v ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp hv)
    have hw' : w ∉ S := Finset.mem_compl.mp (Finset.mem_coe.mp hw)
    by_contra hne
    have hij : v.1 ≠ w.1 := fun h => hne (Prod.ext h hej)
    have hB : Coll (colAx v.1 w.1 v.2) :=
      ⟨v.1, Finset.mem_univ _, w.1, Finset.mem_univ _, v.2, Finset.mem_univ _, hij, rfl⟩
    obtain ⟨u, hu, huS⟩ := hS _ hB
    have hu' : u = (v.1, v.2) ∨ u = (w.1, v.2) := by simpa [colAx] using hu
    rcases hu' with h | h
    · have heq : u = v := h.trans (Prod.eta v)
      exact hv' (heq ▸ huS)
    · have heq : u = w := h.trans (Prod.ext rfl hej)
      exact hw' (heq ▸ huS)
  have hsum := Finset.card_add_card_compl S
  have hV : Fintype.card V = 20 := by decide +kernel
  have hH : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
  omega

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 5 4 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

private theorem indispensableMatching {B : Finset Row} {K : Finset Hole}
    (h : B.card = K.card) : ∃ a : V → Bool,
    (∀ r ∈ B, ∃ j ∈ K, a (r, j) = true) ∧
    (∀ {r j}, a (r, j) = true → r ∈ B ∧ j ∈ K) ∧
    (∀ {r s j}, a (r, j) = true → a (s, j) = true → r = s) := by
  let e : ↥B ≃ ↥K := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using h)
  let a : V → Bool := fun w =>
    if hr : w.1 ∈ B then decide ((e ⟨w.1, hr⟩ : Hole) = w.2) else false
  have ha (r : Row) (j : Hole) : a (r, j) = true ↔
      ∃ hr : r ∈ B, (e ⟨r, hr⟩ : Hole) = j := by
    by_cases hr : r ∈ B
    · have he : a (r, j) = true ↔ (e ⟨r, hr⟩ : Hole) = j := by simp [a, hr]
      exact he.trans ⟨fun h' => ⟨hr, h'⟩, fun ⟨_, h'⟩ => h'⟩
    · simp [a, hr]
  refine ⟨a, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨e ⟨r, hr⟩, (e ⟨r, hr⟩).property, (ha r _).2 ⟨hr, rfl⟩⟩
  · intro r j ht
    obtain ⟨hr, hj⟩ := (ha r j).1 ht
    exact ⟨hr, hj ▸ (e ⟨r, hr⟩).property⟩
  · intro r s j hr hs
    obtain ⟨hrB, hrj⟩ := (ha r j).1 hr
    obtain ⟨hsB, hsj⟩ := (ha s j).1 hs
    have he : e ⟨r, hrB⟩ = e ⟨s, hsB⟩ := Subtype.ext (hrj.trans hsj.symm)
    exact congrArg Subtype.val (e.injective he)

private theorem indispensableSatRow {a : V → Bool} {J : Finset Hole} {r : Row} {j : Hole}
    (hj : j ∈ J) (h : a (r, j) = true) : ClauseSat a (rowAx r J) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, hj, rfl⟩, h⟩

private theorem indispensableSatCol {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

private theorem indispensablePHP {B : C} : B ∈ PHP 5 4 ↔
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

private theorem indispensableRowModel (i : Row) :
    ∃ a : V → Bool, ¬ ClauseSat a (rowAx i Finset.univ) ∧
      ∀ R ∈ PHP 5 4, R ≠ rowAx i Finset.univ → ClauseSat a R := by
  have hc : ((Finset.univ : Finset Row).erase i).card = (Finset.univ : Finset Hole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; decide +kernel
  obtain ⟨a, hrow, hmem, hinj⟩ := indispensableMatching hc
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    change l ∈ (Finset.univ : Finset Hole).image (fun j => ((i, j), true)) at hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.notMem_erase i Finset.univ (hmem hal).1
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, j, _, hrs, rfl⟩
    · have hri : r ≠ i := fun he => hne (congrArg (fun r => rowAx r Finset.univ) he)
      obtain ⟨j, hj, haj⟩ := hrow r (Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩)
      exact indispensableSatRow hj haj
    · exact indispensableSatCol (fun ⟨hr, hs⟩ => hrs (hinj hr hs))

private theorem indispensableColModel {i k : Row} (j : Hole) (hik : i ≠ k) :
    ∃ a : V → Bool, ¬ ClauseSat a (colAx i k j) ∧
      ∀ R ∈ PHP 5 4, R ≠ colAx i k j → ClauseSat a R := by
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hc : (((Finset.univ : Finset Row).erase i).erase k).card =
      ((Finset.univ : Finset Hole).erase j).card := by
    rw [Finset.card_erase_of_mem hkm, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
  obtain ⟨b, hbrow, hbmem, hbinj⟩ := indispensableMatching hc
  let a : V → Bool := fun w =>
    if (w.1 = i ∨ w.1 = k) ∧ w.2 = j then true else b w
  have ha (r : Row) (q : Hole) : a (r, q) = true ↔
      ((r = i ∨ r = k) ∧ q = j) ∨ b (r, q) = true := by
    by_cases h : (r = i ∨ r = k) ∧ q = j <;> simp [a, h]
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have htrue : a (i, j) = true := (ha i j).2 (Or.inl ⟨Or.inl rfl, rfl⟩)
      have hbad : true = false := htrue.symm.trans hal
      cases hbad
    · have htrue : a (k, j) = true := (ha k j).2 (Or.inl ⟨Or.inr rfl, rfl⟩)
      have hbad : true = false := htrue.symm.trans hal
      cases hbad
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, q, _, hrs, rfl⟩
    · by_cases he : r = i ∨ r = k
      · exact indispensableSatRow (Finset.mem_univ j) ((ha r j).2 (Or.inl ⟨he, rfl⟩))
      · have hr' : r ∈ (Finset.univ.erase i).erase k := Finset.mem_erase.mpr
          ⟨fun h => he (Or.inr h), Finset.mem_erase.mpr ⟨fun h => he (Or.inl h), Finset.mem_univ _⟩⟩
        obtain ⟨q, _, hbr⟩ := hbrow r hr'
        exact indispensableSatRow (Finset.mem_univ q) ((ha r q).2 (Or.inr hbr))
    · apply indispensableSatCol
      intro hboth
      rcases (ha r q).1 hboth.1 with ⟨hr, hq⟩ | hr <;>
        rcases (ha s q).1 hboth.2 with ⟨hs, hq'⟩ | hs
      · apply hne
        rcases hr with hri | hrk <;> rcases hs with hsi | hsk
        · exact (hrs (hri.trans hsi.symm)).elim
        · rw [hri, hsk, hq]
        · simpa only [hrk, hsi, hq, colAx] using
            (Finset.pair_comm ((k, j), false) ((i, j), false))
        · exact (hrs (hrk.trans hsk.symm)).elim
      · exact (Finset.mem_erase.mp (hbmem hs).2).1 hq
      · exact (Finset.mem_erase.mp (hbmem hr).2).1 hq'
      · exact hrs (hbinj hr hs)

theorem critical {B : C} (hB : B ∈ PHP 5 4) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 5 4, D ≠ B → ClauseSat a D := by
  rcases indispensablePHP.mp hB with ⟨i, rfl⟩ | ⟨i, _, k, _, j, _, hik, rfl⟩
  · exact indispensableRowModel i
  · exact indispensableColModel j hik

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Collision Finset.univ Finset.univ B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _,
      ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, _, k, _, j, _, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · refine Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, ?_⟩
      exact Finset.pair_comm ((k, j), false) ((i, j), false)

theorem collisionBank_card : collisionBank.card = 40 := by decide +kernel

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

theorem axiomBank_card : axiomBank.card = 45 := by decide +kernel

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

theorem requiredCollisions {π : List C} {U : Finset C} {S : Finset V}
    (hc : Controls π U S) (he : (∅ : C) ∈ π) :
    ∀ B : C, Coll B → B ∈ U ∧ Hits S B := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical (collisionPHP hB)
  have hr : ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat a D := by
    intro D hDP hDC
    exact hrest D hDP (fun e => hDC (e.symm ▸ hB))
  have hu : ∀ D ∈ U, Coll D → Hits S D → ClauseSat a D := by
    intro D hDU hDC hDS
    apply hrest D (collisionPHP hDC)
    intro e
    subst D
    exact hm ⟨hDU, hDS⟩
  have hneg : NegsIn S ∅ := by
    intro v hv
    simp at hv
  exact emptyUnsat a (hc U S (fun _ h => h) (fun _ h => h) a hr hu ∅ he
    (fun h => collisionNonempty h rfl) hneg)

theorem refutationLower {π : List C} (hπ : IsRefutation (PHP 5 4) π) :
    101 ≤ π.length := by
  obtain ⟨A, U, S, hsum, ha, hc⟩ := collect hπ.1
  have hab := Finset.card_le_card (requiredAxioms ha hπ.2)
  rw [axiomBank_card] at hab
  have hcov := requiredCollisions hc hπ.2
  have hub : collisionBank ⊆ U := fun B hB => (hcov B ((mem_collisionBank B).mp hB)).1
  have hun := Finset.card_le_card hub
  rw [collisionBank_card] at hun
  have hsn := coverSize S (fun B hB => (hcov B hB).2)
  omega

end PEqualNP.Outside.L_pcx_164_lower101

theorem PEqualNP.Outside.L_pcx_164_lower101.result : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 100) := by
  rintro ⟨π, hπ, hlen⟩
  have := PEqualNP.Outside.L_pcx_164_lower101.refutationLower hπ
  omega


namespace PEqualNP.Outside.L_pcx_164_lower101
open PEqualNP.ProofComplexity

inductive Budget : List C → Nat → Nat → Prop
  | nil : Budget [] 0 0
  | ax {π R c t} (h : Budget π c t) (hr : R ∈ PHP 5 4) : Budget (R::π) c t
  | raw {π P N R c t} (h : Budget π c t) (p : P ∈ π) (n : N ∈ π)
      (r : IsResolvent P N R) (cc : Coll N) : Budget (R::π) (c+1) t
  | other {π P N R c t} (h : Budget π c t) (p : P ∈ π) (n : N ∈ π)
      (r : IsResolvent P N R) (cc : ¬Coll N) : Budget (R::π) c (t+1)

theorem assignBudget {π : List C} (h : IsDerivation (PHP 5 4) π) : ∃ c t, Budget π c t := by
  induction h with
  | nil => exact ⟨0,0,.nil⟩
  | ax _ hr ih =>
    obtain ⟨c,t,b⟩ := ih
    exact ⟨c,t,.ax b hr⟩
  | @res π P N R _ p n r ih =>
    obtain ⟨c,t,b⟩ := ih
    by_cases cc : Coll N
    · exact ⟨c+1,t,.raw b p n r cc⟩
    · exact ⟨c,t+1,.other b p n r cc⟩

theorem separate {π : List C} {c t : Nat} (b : Budget π c t) :
    ∃ (A U : Finset C) (S : Finset V),
      A.card + c + t ≤ π.length ∧ U.card ≤ c ∧ S.card ≤ t ∧ Absorbs π A ∧ Controls π U S := by
  induction b with
  | nil => exact ⟨∅,∅,∅,by simp,by simp,by simp,by simp [Absorbs],by simp [Controls]⟩
  | @ax π R c t b hr ih =>
    obtain ⟨A,U,S,ha,hu,hs,abs,con⟩ := ih
    refine ⟨insert R A,U,S,?_,hu,hs,?_,?_⟩
    · have := Finset.card_insert_le R A
      simp only [List.length_cons]
      omega
    · intro a ha Q hQ
      rcases List.mem_cons.mp hQ with eq | mem
      · subst Q
        exact ha R (Finset.mem_insert_self _ _) hr
      · exact abs a (fun B hB hB' => ha B (Finset.mem_insert_of_mem hB) hB') Q mem
    · intro U' S' hU hS a hrows hcols Q hQ hnc hneg
      rcases List.mem_cons.mp hQ with eq | mem
      · subst Q
        exact hrows R hr hnc
      · exact con U' S' hU hS a hrows hcols Q mem hnc hneg
  | @raw π P N R c t b p n rr cc ih =>
    obtain ⟨A,U,S,ha,hu,hs,abs,con⟩ := ih
    obtain ⟨v,hp,hn,he⟩ := rr
    refine ⟨A,insert N U,S,?_,?_,hs,?_,?_⟩
    · simp only [List.length_cons]; omega
    · have := Finset.card_insert_le N U; omega
    · intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | e
      · exact satResolve he (abs a hA P p) (abs a hA N n)
      · exact abs a hA Q e
    · intro U' S' hU hS
      exact controlStep con p n hp hn he U' S' ((Finset.subset_insert N U).trans hU)
        hS (fun _ => hU (Finset.mem_insert_self _ _)) (fun e => (e cc).elim)
  | @other π P N R c t b p n rr cc ih =>
    obtain ⟨A,U,S,ha,hu,hs,abs,con⟩ := ih
    obtain ⟨v,hp,hn,he⟩ := rr
    refine ⟨A,U,insert v S,?_,hu,?_,?_,?_⟩
    · simp only [List.length_cons]; omega
    · have := Finset.card_insert_le v S; omega
    · intro a hA Q hQ
      rcases List.mem_cons.mp hQ with rfl | e
      · exact satResolve he (abs a hA P p) (abs a hA N n)
      · exact abs a hA Q e
    · intro U' S' hU hS
      exact controlStep con p n hp hn he U' S' hU ((Finset.subset_insert v S).trans hS)
        (fun h => (cc h).elim) (fun _ => hS (Finset.mem_insert_self _ _))

theorem splitCount {π : List C} {c t : Nat} (b : Budget π c t) (endMem : (∅ : C) ∈ π) :
    45+c+t ≤ π.length ∧ 40 ≤ c ∧ 16 ≤ t := by
  obtain ⟨A,U,S,ha,hu,hs,abs,con⟩ := separate b
  have hA := Finset.card_le_card (requiredAxioms abs endMem)
  rw [axiomBank_card] at hA
  have claim := requiredCollisions con endMem
  have subset : collisionBank ⊆ U := fun B hB => (claim B ((mem_collisionBank B).mp hB)).1
  have hU := Finset.card_le_card subset
  rw [collisionBank_card] at hU
  have hS := coverSize S (fun B hB => (claim B hB).2)
  omega

theorem rawRepeatBranch {π : List C} {c t : Nat} (b : Budget π c t) (endMem : (∅ : C) ∈ π)
    (extra : Nat) (hc : 40+extra ≤ c) : 101+extra ≤ π.length := by
  have := splitCount b endMem
  omega

theorem soleOutput {P N : C} {v w : V} (diff : w ≠ v) (hp : (w,true) ∈ P)
    (hn : N = {((w,false) : V × Bool),(v,false)})
    (res : ({(v,false)} : C) = P.erase (w,true) ∪ N.erase (w,false)) :
    P = {(w,true)} ∨ P = {(w,true),(v,false)} := by
  have small (l : V × Bool) (hl : l ∈ P) : l = (w,true) ∨ l = (v,false) := by
    by_cases e : l=(w,true)
    · exact Or.inl e
    · have hm : l ∈ ({(v,false)} : C) := by
        rw [res]
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hl⟩)
      exact Or.inr (Finset.mem_singleton.mp hm)
  by_cases neg : (v,false) ∈ P
  · right
    ext l
    constructor
    · intro h; simpa using small l h
    · intro h
      rcases (show l = (w,true) ∨ l = (v,false) by simpa using h) with rfl | rfl
      · exact hp
      · exact neg
  · left
    ext l
    constructor
    · intro h
      rcases small l h with eq | eq
      · exact Finset.mem_singleton.mpr eq
      · exact False.elim (neg (eq ▸ h))
    · intro h
      obtain rfl := Finset.mem_singleton.mp h
      exact hp

theorem negativeTerminal {P N : C} {v : V} (hc : Coll N) (hr : IsResolvent P N {(v,false)}) :
    ∃ w : V, w ≠ v ∧ w.2=v.2 ∧ N = {(w,false),(v,false)} ∧
      (P = {(w,true)} ∨ P = {(w,true),(v,false)}) := by
  obtain ⟨i,_,k,_,j,_,ik,rfl⟩ := hc
  obtain ⟨w,hp,hn,he⟩ := hr
  have casesW : w=(i,j) ∨ w=(k,j) := by simpa [colAx] using hn
  have proveOther (a b : V) (ne : b ≠ a) (hb : (b,false) ∈ colAx i k j) (wa : w=a) : b=v := by
    have different : (b,false) ≠ (w,false) := fun e => ne ((congrArg Prod.fst e).trans wa)
    have isMem : (b,false) ∈ ({(v,false)} : C) := by
      rw [he]
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨different,hb⟩)
    exact congrArg Prod.fst (Finset.mem_singleton.mp isMem)
  have neq : (i,j) ≠ (k,j) := fun h => ik (congrArg Prod.fst h)
  rcases casesW with rfl | rfl
  · obtain rfl := proveOther (i,j) (k,j) (Ne.symm neq) (by simp [colAx]) rfl
    exact ⟨(i,j),neq,rfl,rfl,soleOutput neq hp rfl he⟩
  · obtain rfl := proveOther (k,j) (i,j) neq (by simp [colAx]) rfl
    have swap : colAx i k j = {(((k,j) : V),false),((i,j),false)} := Finset.pair_comm _ _
    exact ⟨(k,j),Ne.symm neq,rfl,swap,soleOutput (Ne.symm neq) hp swap he⟩

end PEqualNP.Outside.L_pcx_164_lower101


namespace PEqualNP.Outside.L_pcx_164_box

open PEqualNP.ProofComplexity
abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev Occ := Hole → Row
abbrev Box := Row × Row × Hole

def occ (a : Occ) (v : V) : Bool := decide (a v.2 = v.1)
def Bad (a : Occ) (R : C) : Prop := ¬ClauseSat (occ a) R
def upd (a : Occ) (h : Hole) (r : Row) : Occ := fun j => if j=h then r else a j
def Twin (v : V) (e : Row) (a : Occ) : Prop :=
  a v.2 = e ∧ (∀ r : Row, (∃ j, a j=r) ↔ r≠v.1) ∧
    (∀ r : Row, (∃ j, upd a v.2 v.1 j=r) ↔ r≠e)
def inside (s : Box) (a : Occ) : Prop :=
  ∀ j : Hole, s.1=s.2.1 ∨ j≠s.2.2 → a j≠s.1 ∧ a j≠s.2.1
def Hull (s : Box) (R : C) := ∀ a, Bad a R → inside s a
def sel (b : Bool) (a : Occ) (v : V) := if b then upd a v.2 v.1 else a
def missingRow (b : Bool) (v : V) (e : Row) := if b then e else v.1

def fill (v : V) (e q : Row) (j : Hole) : Occ := fun k =>
  if k=v.2 then e else if k=j then q else
    ((List.finRange 5).filter (fun r => r != v.1 && r != e && r != q)).getD
      (((List.finRange 4).filter (fun l => l != v.2 && l != j)).idxOf k) 0

instance (v : V) (e : Row) (a : Occ) : Decidable (Twin v e a) := by unfold Twin; infer_instance
def fillCheck (v : V) (e q : Row) (j : Hole) : Bool :=
  if v.1≠e ∧ q≠v.1 ∧ q≠e ∧ j≠v.2 then
    decide (Twin v e (fill v e q j)) && decide (fill v e q j j=q) else true

set_option maxHeartbeats 0 in
theorem fillVerified : ∀ (w : Row) (h : Hole) (e q : Row) (j : Hole),
    fillCheck (w,h) e q j=true := by decide +kernel

theorem fillOK : ∀ (v : V) (e q : Row) (j : Hole), v.1≠e → q≠v.1 → q≠e → j≠v.2 →
    Twin v e (fill v e q j) ∧ fill v e q j j=q := by
  intro v e q j ne qw qe jh
  have ok := fillVerified v.1 v.2 e q j
  simpa [fillCheck,ne,qw,qe,jh] using ok

theorem otherRow : ∀ w e : Row, ∃ q : Row, q≠w ∧ q≠e := by decide +kernel
theorem otherHole : ∀ h g : Hole, ∃ j : Hole, j≠h ∧ j≠g := by decide +kernel

theorem someTwin (v : V) (e : Row) (ne : v.1≠e) : ∃ a, Twin v e a := by
  obtain ⟨q,qw,qe⟩ := otherRow v.1 e
  obtain ⟨j,jh,_⟩ := otherHole v.2 v.2
  exact ⟨_,(fillOK v e q j ne qw qe jh).1⟩

theorem missingSel {v : V} {e : Row} {a : Occ} (ha : Twin v e a) (b : Bool) (r : Row) :
    (∃ j, sel b a v j=r) ↔ r ≠ missingRow b v e := by
  cases b with
  | false => exact ha.2.1 r
  | true => exact ha.2.2 r

theorem boxEverywhere {s : Box} {v : V} {e : Row} (ne : v.1≠e) (b : Bool)
    (contain : ∀ a, Twin v e a → inside s (sel b a v)) :
    ∀ a, inside s a → ∀ j, j≠v.2 → a j≠missingRow b v e := by
  obtain ⟨one,twin⟩ := someTwin v e ne
  by_cases diagonal : s.1=s.2.1
  · have eq : s.1=missingRow b v e := by
      by_contra diff
      obtain ⟨j,hj⟩ := (missingSel twin b s.1).2 diff
      exact (contain one twin j (Or.inl diagonal)).1 hj
    intro a ha j _
    exact eq ▸ (ha j (Or.inl diagonal)).1
  · obtain ⟨k,kv,ks⟩ := otherHole v.2 s.2.2
    have excluded (r : Row) (member : r=s.1 ∨ r=s.2.1) : r=v.1 ∨ r=e := by
      by_contra no
      have rw' : r≠v.1 := fun h => no (Or.inl h)
      have re : r≠e := fun h => no (Or.inr h)
      obtain ⟨t,hk⟩ := fillOK v e r k ne rw' re kv
      have val : sel b (fill v e r k) v k=r := by
        cases b <;> simpa [sel,upd,kv] using hk
      have c := contain _ t k (Or.inr ks)
      rcases member with h|h
      · exact c.1 (val.trans h)
      · exact c.2 (val.trans h)
    have a1 := excluded s.1 (Or.inl rfl)
    have a2 := excluded s.2.1 (Or.inr rfl)
    have both : (s.1=v.1 ∧ s.2.1=e) ∨ (s.1=e ∧ s.2.1=v.1) := by grind
    have hMatch : s.2.2=v.2 := by
      by_contra fail
      have c := contain one twin v.2 (Or.inr (Ne.symm fail))
      have f : sel b one v v.2 = (if b then v.1 else e) := by
        cases b <;> simp [sel,upd,twin.1]
      rcases both with h|h <;> cases b <;> simp_all
    intro a ha j jv
    have c := ha j (Or.inr (fun eq => jv (eq.trans hMatch)))
    rcases both with h|h <;> cases b <;> simp_all [missingRow]

theorem mixBad {a z : Occ} {R : C} (ha : Bad a R) (hz : Bad z R) (h : Hole) :
    Bad (upd a h (z h)) R := by
  rintro ⟨l,hl,sat⟩
  rcases l with ⟨⟨p,j⟩,sg⟩
  change decide (upd a h (z h) j=p)=sg at sat
  by_cases e : j=h
  · subst j
    exact hz ⟨((p,h),sg),hl,by simpa [occ,upd] using sat⟩
  · exact ha ⟨((p,j),sg),hl,by simpa [occ,upd,e] using sat⟩

theorem routeLeft {P N R : C} {v : V} {a : Occ}
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Bad a R)
    (bit : a v.2≠v.1) : Bad a P := by
  rintro ⟨z,hz,yes⟩
  have diff : z≠(v,true) := by
    rintro rfl
    change decide (a v.2=v.1)=true at yes
    exact bit (of_decide_eq_true yes)
  exact hr ⟨z,by rw [eq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨diff,hz⟩),yes⟩

theorem routeRight {P N R : C} {v : V} {a : Occ}
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (hr : Bad a R)
    (bit : a v.2=v.1) : Bad a N := by
  rintro ⟨z,hz,yes⟩
  have diff : z≠(v,false) := by
    rintro rfl
    change decide (a v.2=v.1)=false at yes
    simp [bit] at yes
  exact hr ⟨z,by rw [eq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨diff,hz⟩),yes⟩

def Mandatory (v : V) (e : Row) (R : C) :=
  ∀ a, Twin v e a → Bad a R ∧ Bad (upd a v.2 v.1) R

theorem mergeHull {P N R : C} {v : V} {e : Row} (ne : v.1≠e)
    (eq : R=P.erase (v,true) ∪ N.erase (v,false)) (forced : Mandatory v e R)
    {left right : Box} (lh : Hull left P) (rh : Hull right N) : Hull (v.1,e,v.2) R := by
  have lc := boxEverywhere (s:=left) ne false (by
    intro a t
    exact lh a (routeLeft eq (forced a t).1 (fun yes => ne (yes.symm.trans t.1))))
  have rc := boxEverywhere (s:=right) ne true (by
    intro a t
    exact rh _ (routeRight (a := upd a v.2 v.1) eq (forced a t).2 (by simp [upd])))
  obtain ⟨z,zt⟩ := someTwin v e ne
  intro a hbad j hj
  have diff := hj.resolve_left ne
  have a0 := mixBad hbad (forced z zt).1 v.2
  have a1 := mixBad hbad (forced z zt).2 v.2
  have p := routeLeft eq a0 (by simpa [upd,zt.1] using Ne.symm ne)
  have n := routeRight eq a1 (by simp [upd])
  exact ⟨by simpa [upd,diff,missingRow] using lc _ (lh _ p) j diff,
    by simpa [upd,diff,missingRow] using rc _ (rh _ n) j diff⟩

end PEqualNP.Outside.L_pcx_164_box

namespace PEqualNP.Outside.L_pcx_164_box
open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_164_lower101 (Coll Budget Controls controlStep requiredCollisions coverSize Hits colAx)

inductive Log : List C → List (V × C) → Prop
  | nil : Log [] []
  | ax {π E R} (l : Log π E) (h : R ∈ PHP 5 4) : Log (R::π) E
  | raw {π E P N R v} (l : Log π E) (p : P ∈ π) (n : N ∈ π) (c : Coll N)
      (hp : (v,true) ∈ P) (hn : (v,false) ∈ N) (eq : R=P.erase (v,true) ∪ N.erase (v,false)) :
      Log (R::π) E
  | other {π E P N R v} (l : Log π E) (p : P ∈ π) (n : N ∈ π) (c : ¬Coll N)
      (hp : (v,true) ∈ P) (hn : (v,false) ∈ N) (eq : R=P.erase (v,true) ∪ N.erase (v,false)) :
      Log (R::π) ((v,R)::E)

theorem logOfBudget {π : List C} {c t : Nat} (b : Budget π c t) : ∃ E, Log π E ∧ E.length=t := by
  induction b with
  | nil => exact ⟨[],.nil,rfl⟩
  | ax _ h ih =>
    obtain ⟨E,l,hl⟩ := ih
    exact ⟨E,.ax l h,hl⟩
  | raw _ p n res col ih =>
    obtain ⟨E,l,hl⟩ := ih
    obtain ⟨v,hp,hn,eq⟩ := res
    exact ⟨E,.raw l p n col hp hn eq,hl⟩
  | other _ p n res col ih =>
    obtain ⟨E,l,hl⟩ := ih
    obtain ⟨v,hp,hn,eq⟩ := res
    exact ⟨(v,_)::E,.other l p n col hp hn eq,by simp [hl]⟩

def cells (E : List (V × C)) : Finset V := (E.map Prod.fst).toFinset

theorem logControl {π : List C} {E : List (V × C)} (l : Log π E) :
    Controls π Finset.univ (cells E) := by
  induction l with
  | nil => simp [Controls]
  | ax _ h ih =>
    intro U S hU hS a hrows hcols Q hQ hnc hneg
    rcases List.mem_cons.mp hQ with eq | mem
    · subst Q
      exact hrows _ h hnc
    · exact ih U S hU hS a hrows hcols Q mem hnc hneg
  | raw _ p n c hp hn eq ih =>
    intro U S hU hS
    exact controlStep ih p n hp hn eq U S hU hS (fun _ => hU (Finset.mem_univ _)) (fun no => (no c).elim)
  | @other π E P N R v _ p n c hp hn eq ih =>
    intro U S hU hS
    have hs : insert v (cells E) ⊆ S := by simpa [cells] using hS
    exact controlStep ih p n hp hn eq U S hU ((Finset.subset_insert v _).trans hs)
      (fun is => (c is).elim) (fun _ => hs (Finset.mem_insert_self _ _))

theorem cellsLe (E : List (V×C)) : (cells E).card ≤ E.length := by
  simpa [cells] using (List.toFinset_card_le (E.map Prod.fst))

theorem onlyClause (E : List (V×C)) (eq : E.length ≤ (cells E).card) (w : V) (A B : C)
    (a : (w,A) ∈ E) (b : (w,B) ∈ E) : A=B := by
  induction E with
  | nil => simp at a
  | cons z tail ih =>
    have hle := cellsLe tail
    have hcard : (cells (z::tail)).card = (insert z.1 (cells tail)).card := by simp [cells]
    have fresh : z.1 ∉ cells tail := by
      intro mem
      rw [hcard,Finset.insert_eq_of_mem mem] at eq
      simp only [List.length_cons] at eq
      omega
    rw [hcard,Finset.card_insert_of_notMem fresh] at eq
    simp only [List.length_cons] at eq
    have no (W : C) (h : (z.1,W) ∈ tail) : False :=
      fresh (List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,h,rfl⟩))
    rcases List.mem_cons.mp a with e1 | p <;> rcases List.mem_cons.mp b with e2 | q
    · exact congrArg Prod.snd (e1.trans e2.symm)
    · subst z; exact (no B q).elim
    · subst z; exact (no A p).elim
    · exact ih (by omega) p q

theorem omitted {S : Finset V} (card : S.card=16) (cover : ∀ B : C, Coll B → Hits S B)
    (j : Hole) : ∃ r : Row, (r,j) ∉ S := by
  have inject : Set.InjOn Prod.snd (↑(Sᶜ) : Set V) := by
    intro v hv w hw e
    have nv : v ∉ S := Finset.mem_compl.mp hv
    have nw : w ∉ S := Finset.mem_compl.mp hw
    by_contra ne
    have d : v.1≠w.1 := fun a => ne (Prod.ext a e)
    obtain ⟨u,hu,member⟩ := cover (colAx v.1 w.1 v.2)
      ⟨v.1,Finset.mem_univ _,w.1,Finset.mem_univ _,v.2,Finset.mem_univ _,d,rfl⟩
    rcases (show u=(v.1,v.2) ∨ u=(w.1,v.2) by simpa [colAx] using hu) with ha|ha
    · exact nv ((ha.trans (Prod.eta v)) ▸ member)
    · exact nw ((ha.trans (Prod.ext rfl e)) ▸ member)
  have size := Finset.card_add_card_compl S
  have total : Fintype.card V=20 := by decide
  have hc : (Sᶜ).card=4 := by omega
  have full : (Sᶜ).image Prod.snd = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [Finset.card_image_of_injOn inject,hc]; decide)
  have mem : j ∈ (Sᶜ).image Prod.snd := full ▸ Finset.mem_univ _
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp mem
  exact ⟨v.1,Finset.mem_compl.mp hv⟩

theorem rawGood (a : Occ) {N : C} (c : Coll N) : ClauseSat (occ a) N := by
  obtain ⟨i,_,k,_,j,_,ik,rfl⟩ := c
  by_cases q : a j=i
  · have nq : a j≠k := fun e => ik (q.symm.trans e)
    exact ⟨((k,j),false),by simp [colAx],by simp [occ,nq]⟩
  · exact ⟨((i,j),false),by simp [colAx],by simp [occ,q]⟩

theorem leftRaw {P N R : C} {w : V} {a : Occ} (c : Coll N)
    (eq : R=P.erase (w,true) ∪ N.erase (w,false)) (bad : Bad a R) : Bad a P := by
  by_cases bit : a w.2=w.1
  · exact (routeRight eq bad bit (rawGood a c)).elim
  · exact routeLeft eq bad bit

theorem rowBad {i : Row} {a : Occ}
    (h : Bad a (Finset.univ.image (fun j : Hole => ((i,j),true)))) : ∀ j, a j≠i := by
  intro j eq
  exact h ⟨((i,j),true),Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,by simp [occ,eq]⟩

theorem axSeparate {v : V} {e : Row} (ne : v.1≠e) {a : Occ} (tw : Twin v e a)
    {R : C} (hr : R ∈ PHP 5 4) : ¬(Bad a R ∧ Bad (upd a v.2 v.1) R) := by
  rintro ⟨bad0,bad1⟩
  rcases hr with ⟨r,rfl⟩ | ⟨i,k,j,hik,rfl⟩
  · by_cases same : r=v.1
    · obtain ⟨x,hx⟩ := (tw.2.2 r).2 (same ▸ ne)
      exact rowBad bad1 x hx
    · obtain ⟨x,hx⟩ := (tw.2.1 r).2 same
      exact rowBad bad0 x hx
  · exact bad0 (rawGood a ⟨i,Finset.mem_univ _,k,Finset.mem_univ _,j,Finset.mem_univ _,hik,rfl⟩)

theorem distinguishing {π : List C} {E : List (V×C)} (lg : Log π E) {a b : Occ}
    (ax : ∀ R ∈ PHP 5 4, ¬(Bad a R ∧ Bad b R)) :
    ∀ R ∈ π, Bad a R → Bad b R →
      ∃ w Q, (w,Q) ∈ E ∧ (¬(a w.2=w.1 ↔ b w.2=w.1)) ∧ Bad a Q ∧ Bad b Q := by
  induction lg with
  | nil => simp
  | ax _ h ih =>
    intro R hr ba bb
    rcases List.mem_cons.mp hr with rfl | old
    · exact (ax _ h ⟨ba,bb⟩).elim
    · exact ih _ old ba bb
  | raw _ p n c hp hn eq ih =>
    intro R hr ba bb
    rcases List.mem_cons.mp hr with rfl | old
    · exact ih _ p (leftRaw c eq ba) (leftRaw c eq bb)
    · exact ih _ old ba bb
  | @other π E P N T v _ p n c hp hn eq ih =>
    intro R hr ba bb
    have lift (Q : C) (old : Q∈π) (x : Bad a Q) (y : Bad b Q) :
        ∃ w D, (w,D) ∈ (v,T)::E ∧ (¬(a w.2=w.1 ↔ b w.2=w.1)) ∧ Bad a D ∧ Bad b D := by
      obtain ⟨w,D,mem,h1,h2,h3⟩ := ih _ old x y
      exact ⟨w,D,List.mem_cons_of_mem _ mem,h1,h2,h3⟩
    rcases List.mem_cons.mp hr with eR|old
    · subst R
      by_cases same : a v.2=v.1 ↔ b v.2=v.1
      · by_cases bit : a v.2=v.1
        · exact lift N n (routeRight eq ba bit) (routeRight eq bb (same.mp bit))
        · exact lift P p (routeLeft eq ba bit) (routeLeft eq bb (fun k => bit (same.mpr k)))
      · exact ⟨v,T,List.mem_cons_self,same,ba,bb⟩
    · exact lift R old ba bb

theorem allForced {π : List C} {E : List (V×C)} (lg : Log π E) (he : (∅:C) ∈ π)
    (len : E.length ≤ (cells E).card) {v : V} {R : C} (mem : (v,R)∈E) {e : Row}
    (miss : (e,v.2) ∉ cells E) : Mandatory v e R := by
  have has (w : V) (Q : C) (h : (w,Q) ∈ E) : w ∈ cells E :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,h,rfl⟩)
  have ne : v.1≠e := by
    intro eq
    exact miss (show (e,v.2)∈cells E by simpa [eq] using has v R mem)
  intro a tw
  have empty (z : Occ) : Bad z (∅ : C) := by rintro ⟨l,hl,_⟩; simp at hl
  obtain ⟨w,Q,hw,diff,ba,bb⟩ := distinguishing lg (fun _ h => axSeparate ne tw h) ∅ he
    (empty a) (empty (upd a v.2 v.1))
  have no : ¬(a w.2=w.1 ↔ upd a v.2 v.1 w.2=w.1) := diff
  have col : w.2=v.2 := by
    by_contra neq
    exact no (by simp [upd,neq])
  have row : w.1=v.1 := by
    by_contra neq
    have other : w.1≠e := fun e0 => miss ((Prod.ext e0 col) ▸ has w Q hw)
    exact no (by simp [upd,col,tw.1,Ne.symm neq,Ne.symm other])
  have same : w=v := Prod.ext row col
  subst w
  have qr := onlyClause E len v Q R hw mem
  exact qr ▸ ⟨ba,bb⟩

end PEqualNP.Outside.L_pcx_164_box

namespace PEqualNP.Outside.L_pcx_164_box

open PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_164_lower101 (Budget requiredCollisions coverSize splitCount assignBudget)

theorem rawHull {R : C} (hr : R ∈ PHP 5 4) : ∃ s : Box, Hull s R := by
  rcases hr with ⟨i,rfl⟩ | ⟨i,k,j,ne,rfl⟩
  · refine ⟨(i,i,0),?_⟩
    intro a bad j _
    exact ⟨rowBad bad j,rowBad bad j⟩
  · refine ⟨(i,i,j),?_⟩
    intro a bad
    exact (bad (rawGood a ⟨i,Finset.mem_univ _,k,Finset.mem_univ _,j,Finset.mem_univ _,ne,rfl⟩)).elim

theorem closedHulls {π : List C} {E : List (V×C)} (l : Log π E)
    (f : ∀ v R, (v,R)∈E → ∃ e : Row, v.1≠e ∧ Mandatory v e R) :
    ∀ R ∈ π, ∃ s : Box, Hull s R := by
  induction l with
  | nil => simp
  | ax _ h ih =>
    intro R hr
    rcases List.mem_cons.mp hr with rfl|old
    · exact rawHull h
    · exact ih f _ old
  | raw _ p n c hp hn eq ih =>
    intro R hr
    rcases List.mem_cons.mp hr with rfl|old
    · obtain ⟨s,good⟩ := ih f _ p
      exact ⟨s,fun a bad => good a (leftRaw c eq bad)⟩
    · exact ih f _ old
  | @other π E P N T v _ p n c hp hn eq ih =>
    have sub := ih (fun w Q hm => f w Q (List.mem_cons_of_mem _ hm))
    intro R hr
    rcases List.mem_cons.mp hr with eR|old
    · subst R
      obtain ⟨e,ne,must⟩ := f v T List.mem_cons_self
      obtain ⟨s,sh⟩ := sub P p
      obtain ⟨z,zh⟩ := sub N n
      exact ⟨(v.1,e,v.2),mergeHull ne eq must sh zh⟩
    · exact sub R old

theorem seventeen {π : List C} {E : List (V×C)} (lg : Log π E) (he : (∅:C)∈π) : 17 ≤ E.length := by
  by_contra low
  have cover := requiredCollisions (logControl lg) he
  have hits := fun B hc => (cover B hc).2
  have bot := coverSize (cells E) hits
  have top := cellsLe E
  have pc : (cells E).card=16 := by omega
  have exactL : E.length≤(cells E).card := by omega
  obtain ⟨s,full⟩ := closedHulls lg (fun v R mem => by
    obtain ⟨e,miss⟩ := omitted pc hits v.2
    have hv : v ∈ cells E := List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,mem,rfl⟩)
    have ne : v.1≠e := by
      rintro eq
      exact miss ((Prod.ext eq (rfl : v.2=v.2)) ▸ hv)
    exact ⟨e,ne,allForced lg he exactL mem miss⟩) ∅ he
  let a : Occ := fun _ => s.1
  have bad : Bad a (∅:C) := by rintro ⟨z,hz,_⟩; simp at hz
  obtain ⟨j,_,dj⟩ := otherHole s.2.2 s.2.2
  exact (full a bad j (Or.inr dj)).1 rfl

theorem boundWithRepeats {π : List C} {c t : Nat} (b : Budget π c t) (he : (∅:C)∈π)
    (d : Nat) (reads : 40+d ≤ c) : 102+d ≤ π.length := by
  obtain ⟨E,log,len⟩ := logOfBudget b
  have := seventeen log he
  have base := (splitCount b he).1
  omega

theorem lower102 {π : List C} (ref : IsRefutation (PHP 5 4) π) : 102 ≤ π.length := by
  obtain ⟨c,t,counts⟩ := assignBudget ref.1
  exact boundWithRepeats counts ref.2 0 (by have := (splitCount counts ref.2).2.1; omega)

end PEqualNP.Outside.L_pcx_164_box

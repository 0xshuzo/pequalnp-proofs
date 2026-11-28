import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.GroupTheory.Perm.Centralizer

namespace PEqualNP.Outside.L_lib_931

def cores {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ((H.product H).image (fun z => z.1 ∩ z.2)).filter (fun c => c.card = 2)

def ordinary {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ \ (cores H).biUnion id

def base {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.filter (fun R => R ⊆ ordinary H)

def outer {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) : Finset (Fin n) :=
  (H.filter (fun R => c ⊆ R)).biUnion id \ c

abbrev Valid {n : Nat} (H : Finset (Finset (Fin n))) (M : Finset (Finset (Fin n))) : Prop :=
  (∀ g ∈ M, g.card = 2) ∧
  (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
  (∀ R ∈ H, ∃ g ∈ M, g ⊆ R)

def rowsOf {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.filter (fun R => c ⊆ R)

lemma mem_cores_iff {n : Nat} {H : Finset (Finset (Fin n))} (hH3 : ∀ R ∈ H, R.card = 3)
    {c : Finset (Fin n)} :
    c ∈ cores H ↔ c.card = 2 ∧ ∃ R₁ ∈ H, ∃ R₂ ∈ H, R₁ ≠ R₂ ∧ R₁ ∩ R₂ = c := by
  simp only [cores, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨R₁, R₂, ⟨h1, h2⟩, rfl⟩, hc⟩
    refine ⟨hc, R₁, h1, R₂, h2, ?_, rfl⟩
    intro heq
    subst heq
    rw [Finset.inter_self, hH3 R₁ h1] at hc
    omega
  · rintro ⟨hc, R₁, h1, R₂, h2, _, rfl⟩
    exact ⟨⟨R₁, R₂, ⟨h1, h2⟩, rfl⟩, hc⟩

lemma rowsOf_card_and_eq {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (rowsOf H c).card = 2 ∧ ∀ u ∈ c, H.filter (fun R => u ∈ R) = rowsOf H c := by
  rcases (mem_cores_iff hH3).mp hc with ⟨hcc, R₁, h1, R₂, h2, hne, hinter⟩
  have hsub1 : c ⊆ R₁ := hinter ▸ Finset.inter_subset_left
  have hsub2 : c ⊆ R₂ := hinter ▸ Finset.inter_subset_right
  have h1m : R₁ ∈ rowsOf H c := Finset.mem_filter.mpr ⟨h1, hsub1⟩
  have h2m : R₂ ∈ rowsOf H c := Finset.mem_filter.mpr ⟨h2, hsub2⟩
  have hge : 2 ≤ (rowsOf H c).card := by
    have hpair : ({R₁, R₂} : Finset _) ⊆ rowsOf H c := by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl <;> assumption
    have hpc : ({R₁, R₂} : Finset _).card = 2 := Finset.card_pair hne
    exact hpc ▸ Finset.card_le_card hpair
  have hsub_u : ∀ u ∈ c, rowsOf H c ⊆ H.filter (fun R => u ∈ R) := by
    intro u hu R hR
    simp only [rowsOf, Finset.mem_filter] at hR ⊢
    exact ⟨hR.1, hR.2 hu⟩
  obtain ⟨u₀, hu₀⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
  have hle : (rowsOf H c).card ≤ 2 :=
    (Finset.card_le_card (hsub_u u₀ hu₀)).trans (hdeg u₀)
  have hcard : (rowsOf H c).card = 2 := le_antisymm hle hge
  refine ⟨hcard, fun u hu => ?_⟩
  exact (Finset.eq_of_subset_of_card_le (hsub_u u hu) (by rw [hcard]; exact hdeg u)).symm

lemma cores_pairwise_disjoint {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c₁ c₂ : Finset (Fin n)} (h1 : c₁ ∈ cores H) (h2 : c₂ ∈ cores H) (hne : c₁ ≠ c₂) :
    Disjoint c₁ c₂ := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  apply hne
  have eq1 := (rowsOf_card_and_eq hH3 hdeg h1).2 u hu1
  have eq2 := (rowsOf_card_and_eq hH3 hdeg h2).2 u hu2
  have hrows : rowsOf H c₁ = rowsOf H c₂ := eq1.symm.trans eq2
  have hc1 := ((mem_cores_iff hH3).mp h1).1
  have hc2 := ((mem_cores_iff hH3).mp h2).1
  rcases Finset.card_eq_two.mp (rowsOf_card_and_eq hH3 hdeg h1).1 with ⟨R₁, R₂, hRne, hReq⟩
  have hR1m : R₁ ∈ rowsOf H c₁ := by rw [hReq]; simp
  have hR2m : R₂ ∈ rowsOf H c₁ := by rw [hReq]; simp
  have hR1H : R₁ ∈ H := (Finset.mem_filter.mp hR1m).1
  have hR2H : R₂ ∈ H := (Finset.mem_filter.mp hR2m).1
  have h1sub : c₁ ⊆ R₁ ∩ R₂ :=
    Finset.subset_inter (Finset.mem_filter.mp hR1m).2 (Finset.mem_filter.mp hR2m).2
  have h2sub : c₂ ⊆ R₁ ∩ R₂ := by
    rw [hrows] at hR1m hR2m
    exact Finset.subset_inter (Finset.mem_filter.mp hR1m).2 (Finset.mem_filter.mp hR2m).2
  have hinter_le : (R₁ ∩ R₂).card ≤ 2 := by
    by_contra hgt
    have hge3 : 3 ≤ (R₁ ∩ R₂).card := by omega
    have heq1 : R₁ ∩ R₂ = R₁ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hH3 R₁ hR1H]; exact hge3)
    have heq2 : R₁ ∩ R₂ = R₂ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hH3 R₂ hR2H]; exact hge3)
    exact hRne (heq1.symm.trans heq2)
  have e1 : c₁ = R₁ ∩ R₂ := Finset.eq_of_subset_of_card_le h1sub (by rw [hc1]; exact hinter_le)
  have e2 : c₂ = R₁ ∩ R₂ := Finset.eq_of_subset_of_card_le h2sub (by rw [hc2]; exact hinter_le)
  exact e1.trans e2.symm

lemma core_unique_of_subset {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {R c₁ c₂ : Finset (Fin n)} (hR : R ∈ H)
    (h1 : c₁ ∈ cores H) (h2 : c₂ ∈ cores H) (hs1 : c₁ ⊆ R) (hs2 : c₂ ⊆ R) : c₁ = c₂ := by
  by_contra hne
  have hdisj := cores_pairwise_disjoint hH3 hdeg h1 h2 hne
  have hunion : (c₁ ∪ c₂).card ≤ R.card := Finset.card_le_card (Finset.union_subset hs1 hs2)
  rw [Finset.card_union_of_disjoint hdisj, ((mem_cores_iff hH3).mp h1).1,
      ((mem_cores_iff hH3).mp h2).1, hH3 R hR] at hunion
  omega

lemma mem_base_or_exists_core {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {R : Finset (Fin n)} (hR : R ∈ H) :
    R ∈ base H ∨ ∃ c ∈ cores H, c ⊆ R := by
  by_cases hsub : R ⊆ ordinary H
  · exact Or.inl (Finset.mem_filter.mpr ⟨hR, hsub⟩)
  · right
    rw [Finset.not_subset] at hsub
    rcases hsub with ⟨u, huR, huord⟩
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
      Finset.mem_biUnion, id_eq] at huord
    rcases huord with ⟨c, hc, huc⟩
    have hRmem : R ∈ rowsOf H c := by
      rw [← (rowsOf_card_and_eq hH3 hdeg hc).2 u huc]
      exact Finset.mem_filter.mpr ⟨hR, huR⟩
    exact ⟨c, hc, (Finset.mem_filter.mp hRmem).2⟩

lemma core_structure {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    ∃ x y, x ≠ y ∧ x ∈ ordinary H ∧ y ∈ ordinary H ∧
      outer H c = {x, y} ∧ rowsOf H c = {insert x c, insert y c} := by
  have hcc := ((mem_cores_iff hH3).mp hc).1
  rcases Finset.card_eq_two.mp (rowsOf_card_and_eq hH3 hdeg hc).1 with ⟨R₁, R₂, hRne, hReq⟩
  have hR1m : R₁ ∈ rowsOf H c := by rw [hReq]; simp
  have hR2m : R₂ ∈ rowsOf H c := by rw [hReq]; simp
  have hR1H : R₁ ∈ H := (Finset.mem_filter.mp hR1m).1
  have hR2H : R₂ ∈ H := (Finset.mem_filter.mp hR2m).1
  have hc1 : c ⊆ R₁ := (Finset.mem_filter.mp hR1m).2
  have hc2 : c ⊆ R₂ := (Finset.mem_filter.mp hR2m).2
  have h1diff : (R₁ \ c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hc1, hH3 R₁ hR1H, hcc]
  have h2diff : (R₂ \ c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hc2, hH3 R₂ hR2H, hcc]
  rcases Finset.card_eq_one.mp h1diff with ⟨x, hx⟩
  rcases Finset.card_eq_one.mp h2diff with ⟨y, hy⟩
  have hxR1 : x ∈ R₁ ∧ x ∉ c := by
    have : x ∈ R₁ \ c := by rw [hx]; simp
    exact Finset.mem_sdiff.mp this
  have hyR2 : y ∈ R₂ ∧ y ∉ c := by
    have : y ∈ R₂ \ c := by rw [hy]; simp
    exact Finset.mem_sdiff.mp this
  have hR1eq : R₁ = insert x c := by
    ext u
    by_cases huc : u ∈ c
    · simp [huc, hc1 huc]
    · have : u ∈ R₁ \ c ↔ u = x := by rw [hx]; simp
      simp only [Finset.mem_sdiff, huc, not_false_eq_true, and_true] at this
      simp [this, huc]
  have hR2eq : R₂ = insert y c := by
    ext u
    by_cases huc : u ∈ c
    · simp [huc, hc2 huc]
    · have : u ∈ R₂ \ c ↔ u = y := by rw [hy]; simp
      simp only [Finset.mem_sdiff, huc, not_false_eq_true, and_true] at this
      simp [this, huc]
  have hxy : x ≠ y := by
    intro h
    apply hRne
    rw [hR1eq, hR2eq, h]
  have hord : ∀ z R, R ∈ H → c ⊆ R → z ∈ R → z ∉ c → z ∈ ordinary H := by
    intro z R hRH hcR hzR hzc
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      id_eq, not_exists, not_and]
    intro c' hc' hzc'
    have hRm' : R ∈ rowsOf H c' := by
      rw [← (rowsOf_card_and_eq hH3 hdeg hc').2 z hzc']
      exact Finset.mem_filter.mpr ⟨hRH, hzR⟩
    have hc'eq := core_unique_of_subset hH3 hdeg hRH hc hc' hcR (Finset.mem_filter.mp hRm').2
    exact hzc (hc'eq ▸ hzc')
  refine ⟨x, y, hxy, hord x R₁ hR1H hc1 hxR1.1 hxR1.2, hord y R₂ hR2H hc2 hyR2.1 hyR2.2, ?_, ?_⟩
  · ext u
    simp only [outer, Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_insert,
      Finset.mem_singleton]
    change (∃ R ∈ rowsOf H c, u ∈ R) ∧ u ∉ c ↔ u = x ∨ u = y
    rw [hReq, hR1eq, hR2eq]
    constructor
    · rintro ⟨⟨R, hR, huR⟩, huc⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · simp only [Finset.mem_insert, huc, or_false] at huR; exact Or.inl huR
      · simp only [Finset.mem_insert, huc, or_false] at huR; exact Or.inr huR
    · rintro (h | h)
      · rw [h]; exact ⟨⟨insert x c, by simp, by simp⟩, hxR1.2⟩
      · rw [h]; exact ⟨⟨insert y c, by simp, by simp⟩, hyR2.2⟩
  · rw [hReq, hR1eq, hR2eq]

lemma outer_card_two {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (outer H c).card = 2 := by
  rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, _, _, hout, _⟩
  rw [hout, Finset.card_pair hxy]

lemma outer_subset_ordinary {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    outer H c ⊆ ordinary H := by
  rcases core_structure hH3 hdeg hc with ⟨x, y, _, hx, hy, hout, _⟩
  rw [hout]
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl <;> assumption

lemma base_linear {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    {R₁ R₂ : Finset (Fin n)} (h1 : R₁ ∈ base H) (h2 : R₂ ∈ base H) (hne : R₁ ≠ R₂) :
    (R₁ ∩ R₂).card ≤ 1 := by
  by_contra hgt
  have h1H : R₁ ∈ H := (Finset.mem_filter.mp h1).1
  have h2H : R₂ ∈ H := (Finset.mem_filter.mp h2).1
  have h1ord : R₁ ⊆ ordinary H := (Finset.mem_filter.mp h1).2
  have hle2 : (R₁ ∩ R₂).card ≤ 2 := by
    by_contra hgt2
    have hge3 : 3 ≤ (R₁ ∩ R₂).card := by omega
    have e1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hH3 R₁ h1H]; exact hge3)
    have e2 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (by rw [hH3 R₂ h2H]; exact hge3)
    exact hne (e1.symm.trans e2)
  have hcard2 : (R₁ ∩ R₂).card = 2 := by omega
  have hcore : R₁ ∩ R₂ ∈ cores H := (mem_cores_iff hH3).mpr ⟨hcard2, R₁, h1H, R₂, h2H, hne, rfl⟩
  obtain ⟨u, hu⟩ : (R₁ ∩ R₂).Nonempty := Finset.card_pos.mp (by omega)
  have huord : u ∈ ordinary H := h1ord (Finset.mem_inter.mp hu).1
  simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
  exact huord.2 ⟨R₁ ∩ R₂, hcore, hu⟩

lemma card_biUnion_pairs {n : Nat} {M : Finset (Finset (Fin n))}
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) :
    (M.biUnion id).card = 2 * M.card := by
  rw [Finset.card_biUnion (t := id) (fun g hg h hh hne => hdisj g hg h hh hne)]
  simp only [id_eq]
  rw [Finset.sum_const_nat (fun g hg => h2 g hg), mul_comm]

def CoreMatchings {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun P =>
    P.card = 2 ∧
    (∀ g ∈ P, g.card = 2 ∧ (g ∩ c).card = 1 ∧ (g ∩ outer H c).card = 1) ∧
    (∀ g ∈ P, ∀ h ∈ P, g ≠ h → Disjoint g h)

def Mcore {n : Nat} (M : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  M.filter (fun g => ¬ Disjoint g c)

lemma coreMatchings_explicit {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (CoreMatchings H c).card = 2 ∧
    ∀ P ∈ CoreMatchings H c,
      P.biUnion id = c ∪ outer H c ∧
      (∀ R ∈ rowsOf H c, ∃ g ∈ P, g ⊆ R) ∧
      (∀ g ∈ P, ¬ Disjoint g c ∧ g ⊆ c ∪ outer H c) := by
  have hcc : c.card = 2 := ((mem_cores_iff hH3).mp hc).1
  rcases Finset.card_eq_two.mp hcc with ⟨a, b, hab, hceq⟩
  rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, hxord, hyord, hout, hrows⟩
  have hdisj_co : Disjoint c (outer H c) := Finset.disjoint_sdiff
  have hax : a ≠ x := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : a ∈ c) (by rw [hout, ← h]; simp)
  have hay : a ≠ y := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : a ∈ c) (by rw [hout, ← h]; simp)
  have hbx : b ≠ x := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : b ∈ c) (by rw [hout, ← h]; simp)
  have hby : b ≠ y := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : b ∈ c) (by rw [hout, ← h]; simp)
  set P₁ : Finset (Finset (Fin n)) := {{a, x}, {b, y}}
  set P₂ : Finset (Finset (Fin n)) := {{a, y}, {b, x}}
  have hP12ne : P₁ ≠ P₂ := by
    intro h
    have hm : ({a, x} : Finset (Fin n)) ∈ P₂ := h ▸ (by simp [P₁])
    simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h2
    · have : x ∈ ({a, y} : Finset (Fin n)) := h1 ▸ (by simp)
      simp [hax.symm, hxy] at this
    · have : a ∈ ({b, x} : Finset (Fin n)) := h2 ▸ (by simp)
      simp [hab, hax] at this
  have hP1mem : P₁ ∈ CoreMatchings H c := by
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : ({a, x} : Finset (Fin n)) ≠ {b, y} := by
      intro h; have : a ∈ ({b, y} : Finset (Fin n)) := h ▸ (by simp); simp [hab, hay] at this
    refine ⟨Finset.card_pair hne, fun g hg => ?_, fun g hg h hh hne' => ?_⟩
    · simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨Finset.card_pair hax, ?_, ?_⟩
        · have : ({a, x} : Finset (Fin n)) ∩ c = {a} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hax
                · exact absurd h2.symm hbx
            · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({a, x} : Finset (Fin n)) ∩ outer H c = {x} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hax
                · exact absurd h2 hay
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
      · refine ⟨Finset.card_pair hby, ?_, ?_⟩
        · have : ({b, y} : Finset (Fin n)) ∩ c = {b} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hay
                · exact absurd h2.symm hby
            · rintro rfl; exact ⟨Or.inl rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({b, y} : Finset (Fin n)) ∩ outer H c = {y} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hbx
                · exact absurd h2 hby
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
    · simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne'
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h
        · exact hay h
        · exact hbx h.symm
        · exact hxy h
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h.symm
        · exact hbx h
        · exact hay h.symm
        · exact hxy h.symm
      · exact absurd rfl hne'
  have hP2mem : P₂ ∈ CoreMatchings H c := by
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : ({a, y} : Finset (Fin n)) ≠ {b, x} := by
      intro h; have : a ∈ ({b, x} : Finset (Fin n)) := h ▸ (by simp); simp [hab, hax] at this
    refine ⟨Finset.card_pair hne, fun g hg => ?_, fun g hg h hh hne' => ?_⟩
    · simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨Finset.card_pair hay, ?_, ?_⟩
        · have : ({a, y} : Finset (Fin n)) ∩ c = {a} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hay
                · exact absurd h2.symm hby
            · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({a, y} : Finset (Fin n)) ∩ outer H c = {y} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hax
                · exact absurd h2 hay
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
      · refine ⟨Finset.card_pair hbx, ?_, ?_⟩
        · have : ({b, x} : Finset (Fin n)) ∩ c = {b} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hax
                · exact absurd h2.symm hbx
            · rintro rfl; exact ⟨Or.inl rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({b, x} : Finset (Fin n)) ∩ outer H c = {x} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hbx
                · exact absurd h2 hby
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
    · simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne'
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h
        · exact hax h
        · exact hby h.symm
        · exact hxy h.symm
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h.symm
        · exact hby h
        · exact hax h.symm
        · exact hxy h
      · exact absurd rfl hne'
  have hCM_eq : CoreMatchings H c = {P₁, P₂} := by
    ext P
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hP
      simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      rcases hP with ⟨hP2, hspec, hdisj⟩
      rcases Finset.card_eq_two.mp hP2 with ⟨g₁, g₂, hgne, hPeq⟩
      have hg1 : g₁ ∈ P := by rw [hPeq]; simp
      have hg2 : g₂ ∈ P := by rw [hPeq]; simp
      have hpair_form : ∀ g ∈ P, ∃ p ∈ c, ∃ q ∈ outer H c, g = {p, q} := by
        intro g hg
        rcases hspec g hg with ⟨hg2', hgc, hgo⟩
        rcases Finset.card_eq_one.mp hgc with ⟨p, hp⟩
        rcases Finset.card_eq_one.mp hgo with ⟨q, hq⟩
        have hpm : p ∈ g ∩ c := by rw [hp]; simp
        have hqm : q ∈ g ∩ outer H c := by rw [hq]; simp
        have hpq : p ≠ q := fun h => Finset.disjoint_left.mp hdisj_co
          (Finset.mem_inter.mp hpm).2 (h ▸ (Finset.mem_inter.mp hqm).2)
        have hsub : ({p, q} : Finset (Fin n)) ⊆ g := by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact (Finset.mem_inter.mp hpm).1
          · exact (Finset.mem_inter.mp hqm).1
        refine ⟨p, (Finset.mem_inter.mp hpm).2, q, (Finset.mem_inter.mp hqm).2, ?_⟩
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hpq, hg2'])).symm
      rcases hpair_form g₁ hg1 with ⟨p₁, hp1c, q₁, hq1o, hg1eq⟩
      rcases hpair_form g₂ hg2 with ⟨p₂, hp2c, q₂, hq2o, hg2eq⟩
      have hd12 : Disjoint g₁ g₂ := hdisj g₁ hg1 g₂ hg2 hgne
      have hp12 : p₁ ≠ p₂ := fun h => Finset.disjoint_left.mp hd12
        (by rw [hg1eq]; simp : p₁ ∈ g₁) (by rw [hg2eq, ← h]; simp)
      have hq12 : q₁ ≠ q₂ := fun h => Finset.disjoint_left.mp hd12
        (by rw [hg1eq]; simp : q₁ ∈ g₁) (by rw [hg2eq, ← h]; simp)
      rw [hceq] at hp1c hp2c
      rw [hout] at hq1o hq2o
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp1c hp2c hq1o hq2o
      rcases hp1c with rfl | rfl <;> rcases hp2c with rfl | rfl
      · exact absurd rfl hp12
      · rcases hq1o with rfl | rfl <;> rcases hq2o with rfl | rfl
        · exact absurd rfl hq12
        · left; rw [hPeq, hg1eq, hg2eq]
        · right; rw [hPeq, hg1eq, hg2eq]
        · exact absurd rfl hq12
      · rcases hq1o with rfl | rfl <;> rcases hq2o with rfl | rfl
        · exact absurd rfl hq12
        · right; rw [hPeq, hg1eq, hg2eq, Finset.pair_comm]
        · left; rw [hPeq, hg1eq, hg2eq, Finset.pair_comm]
        · exact absurd rfl hq12
      · exact absurd rfl hp12
    · rintro (rfl | rfl)
      · exact hP1mem
      · exact hP2mem
  refine ⟨by rw [hCM_eq, Finset.card_pair hP12ne], fun P hP => ?_⟩
  rw [hCM_eq] at hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · ext u; rw [hout, hceq]; simp [P₁, or_assoc, or_comm, or_left_comm]
    · intro R hR; rw [hrows] at hR; simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · refine ⟨{a, x}, by simp [P₁], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self x c
      · refine ⟨{b, y}, by simp [P₁], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self y c
    · intro g hg; simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : a ∈ ({a, x} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : b ∈ ({b, y} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
  · refine ⟨?_, ?_, ?_⟩
    · ext u; rw [hout, hceq]; simp [P₂, or_assoc, or_comm, or_left_comm]
    · intro R hR; rw [hrows] at hR; simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · refine ⟨{b, x}, by simp [P₂], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self x c
      · refine ⟨{a, y}, by simp [P₂], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self y c
    · intro g hg; simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : a ∈ ({a, y} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : b ∈ ({b, x} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto

lemma mcore_behavior {n : Nat} {H M : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h)
    {c : Finset (Fin n)} (hc : c ∈ cores H)
    (hcov : ∀ R ∈ rowsOf H c, ∃ g ∈ M, g ⊆ R) :
    (c ∈ M ∧ Mcore M c = {c}) ∨ (c ∉ M ∧ Mcore M c ∈ CoreMatchings H c) := by
  by_cases hcM : c ∈ M
  · left
    refine ⟨hcM, ?_⟩
    ext g
    simp only [Mcore, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hgM, hnd⟩
      by_contra hne
      exact hnd (hdisj g hgM c hcM hne)
    · rintro h
      rw [h]
      have hcc := ((mem_cores_iff hH3).mp hc).1
      obtain ⟨u, hu⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨hcM, fun hd => Finset.disjoint_left.mp hd hu hu⟩
  · right
    refine ⟨hcM, ?_⟩
    have hcc := ((mem_cores_iff hH3).mp hc).1
    rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, _, _, hout, hrows⟩
    have hdisj_co : Disjoint c (outer H c) := Finset.disjoint_sdiff
    have hxnc : x ∉ c := fun h => Finset.disjoint_left.mp hdisj_co h (by rw [hout]; simp)
    have hync : y ∉ c := fun h => Finset.disjoint_left.mp hdisj_co h (by rw [hout]; simp)
    have hR1m : insert x c ∈ rowsOf H c := by rw [hrows]; simp
    have hR2m : insert y c ∈ rowsOf H c := by rw [hrows]; simp
    rcases hcov _ hR1m with ⟨g₁, hg1M, hg1R1⟩
    rcases hcov _ hR2m with ⟨g₂, hg2M, hg2R2⟩
    have hg1c : g₁ ≠ c := fun h => hcM (h ▸ hg1M)
    have hg2c : g₂ ≠ c := fun h => hcM (h ▸ hg2M)
    have hxg1 : x ∈ g₁ := by
      by_contra hxn
      have hsub : g₁ ⊆ c := fun u hu => by
        rcases Finset.mem_insert.mp (hg1R1 hu) with rfl | huc
        · exact absurd hu hxn
        · exact huc
      exact hg1c (Finset.eq_of_subset_of_card_le hsub (by rw [h2 g₁ hg1M, hcc]))
    have hyg2 : y ∈ g₂ := by
      by_contra hyn
      have hsub : g₂ ⊆ c := fun u hu => by
        rcases Finset.mem_insert.mp (hg2R2 hu) with rfl | huc
        · exact absurd hu hyn
        · exact huc
      exact hg2c (Finset.eq_of_subset_of_card_le hsub (by rw [h2 g₂ hg2M, hcc]))
    have hg12ne : g₁ ≠ g₂ := by
      intro heq
      have hxR2 : x ∈ insert y c := hg2R2 (heq ▸ hxg1)
      rcases Finset.mem_insert.mp hxR2 with h | h
      · exact hxy h
      · exact hxnc h
    have hd12 : Disjoint g₁ g₂ := hdisj g₁ hg1M g₂ hg2M hg12ne
    have hg1_ic : (g₁ ∩ c).card = 1 := by
      have heq : g₁ ∩ c = g₁.erase x := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hu1, huc⟩; exact ⟨fun h => hxnc (h ▸ huc), hu1⟩
        · rintro ⟨hux, hu1⟩
          rcases Finset.mem_insert.mp (hg1R1 hu1) with h | huc
          · exact absurd h hux
          · exact ⟨hu1, huc⟩
      rw [heq, Finset.card_erase_of_mem hxg1, h2 g₁ hg1M]
    have hg2_ic : (g₂ ∩ c).card = 1 := by
      have heq : g₂ ∩ c = g₂.erase y := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hu2, huc⟩; exact ⟨fun h => hync (h ▸ huc), hu2⟩
        · rintro ⟨huy, hu2⟩
          rcases Finset.mem_insert.mp (hg2R2 hu2) with h | huc
          · exact absurd h huy
          · exact ⟨hu2, huc⟩
      rw [heq, Finset.card_erase_of_mem hyg2, h2 g₂ hg2M]
    have hg1_io : (g₁ ∩ outer H c).card = 1 := by
      have heq : g₁ ∩ outer H c = {x} := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_singleton, hout, Finset.mem_insert]
        constructor
        · rintro ⟨hu1, rfl | rfl⟩
          · rfl
          · rcases Finset.mem_insert.mp (hg1R1 hu1) with h | huc
            · exact absurd h.symm hxy
            · exact absurd huc hync
        · rintro rfl; exact ⟨hxg1, Or.inl rfl⟩
      rw [heq, Finset.card_singleton]
    have hg2_io : (g₂ ∩ outer H c).card = 1 := by
      have heq : g₂ ∩ outer H c = {y} := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_singleton, hout, Finset.mem_insert]
        constructor
        · rintro ⟨hu2, rfl | rfl⟩
          · rcases Finset.mem_insert.mp (hg2R2 hu2) with h | huc
            · exact absurd h hxy
            · exact absurd huc hxnc
          · rfl
        · rintro rfl; exact ⟨hyg2, Or.inr rfl⟩
      rw [heq, Finset.card_singleton]
    have hc_sub : c ⊆ g₁ ∪ g₂ := by
      have hsub : (g₁ ∩ c) ∪ (g₂ ∩ c) ⊆ c :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hdi : Disjoint (g₁ ∩ c) (g₂ ∩ c) :=
        hd12.mono Finset.inter_subset_left Finset.inter_subset_left
      have heq : (g₁ ∩ c) ∪ (g₂ ∩ c) = c :=
        Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_union_of_disjoint hdi, hg1_ic, hg2_ic, hcc])
      rw [← heq]
      exact Finset.union_subset (Finset.inter_subset_left.trans Finset.subset_union_left)
        (Finset.inter_subset_left.trans Finset.subset_union_right)
    have hMcore_eq : Mcore M c = {g₁, g₂} := by
      ext g
      simp only [Mcore, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hgM, hnd⟩
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨u, hug, huc⟩
        rcases Finset.mem_union.mp (hc_sub huc) with hu1 | hu2
        · left; by_contra hne; exact Finset.disjoint_left.mp (hdisj g hgM g₁ hg1M hne) hug hu1
        · right; by_contra hne; exact Finset.disjoint_left.mp (hdisj g hgM g₂ hg2M hne) hug hu2
      · rintro (h | h)
        · rw [h]
          obtain ⟨u, hu⟩ : (g₁ ∩ c).Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨hg1M, fun hd => Finset.disjoint_left.mp hd (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2⟩
        · rw [h]
          obtain ⟨u, hu⟩ : (g₂ ∩ c).Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨hg2M, fun hd => Finset.disjoint_left.mp hd (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2⟩
    rw [hMcore_eq]
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.card_pair hg12ne, fun g hg => ?_, fun g hg h hh hne => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with h | h
      · rw [h]; exact ⟨h2 g₁ hg1M, hg1_ic, hg1_io⟩
      · rw [h]; exact ⟨h2 g₂ hg2M, hg2_ic, hg2_io⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne
      · exact hd12
      · exact hd12.symm
      · exact absurd rfl hne

variable {n : Nat}
abbrev Dj (M : Finset (Finset (Fin n))) : Prop := ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

abbrev Bm (U : Finset (Fin n)) (H : Finset (Finset (Fin n))) (s : ℕ)
    (M : Finset (Finset (Fin n))) : Prop :=
  Dj M ∧ (∀ e ∈ M, e.card = 2 ∧ e ⊆ U) ∧ (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧ M.card = s

theorem disj_of_sub {e X U : Finset (Fin n)} (h : e ⊆ U \ X) : Disjoint e X :=
  Finset.disjoint_of_subset_left h Finset.sdiff_disjoint

theorem decomp (U : Finset (Fin n)) (H : Finset (Finset (Fin n))) (s : ℕ)
    (P : Finset (Finset (Fin n))) (hP : ∀ e ∈ P, e.card = 2 ∧ e ⊆ U) (hPd : Dj P) :
    (Finset.univ.filter (fun M => Bm U H s M ∧ P ⊆ M)).card =
      if P.card ≤ s then
        (Finset.univ.filter (Bm (U \ P.biUnion id)
          ((H.filter (fun R => ¬ ∃ e ∈ P, e ⊆ R)).image (fun R => R \ P.biUnion id))
          (s - P.card))).card
      else 0 := by
  split_ifs with hle
  · apply Finset.card_nbij' (fun M => M \ P) (fun M' => M' ∪ P)
    · intro M hM
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
      obtain ⟨⟨hd, hedge, hhit, hcard⟩, hPM⟩ := hM
      have hdisj : ∀ e ∈ M \ P, Disjoint e (P.biUnion id) := by
        intro e he
        obtain ⟨heM, heP⟩ := Finset.mem_sdiff.mp he
        rw [Finset.disjoint_biUnion_right]
        intro f hf
        exact hd e heM f (hPM hf) (fun h => heP (h ▸ hf))
      refine ⟨fun e he f hf hne => hd e (Finset.mem_sdiff.mp he).1 f (Finset.mem_sdiff.mp hf).1 hne,
        ?_, ?_, ?_⟩
      · intro e he
        refine ⟨(hedge e (Finset.mem_sdiff.mp he).1).1, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨(hedge e (Finset.mem_sdiff.mp he).1).2 hx,
          fun hxb => Finset.disjoint_left.mp (hdisj e he) hx hxb⟩
      · intro R' hR'
        obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hR'
        obtain ⟨hRH, hRP⟩ := Finset.mem_filter.mp hR
        obtain ⟨e, heM, heR⟩ := hhit R hRH
        have heP : e ∉ P := fun h => hRP ⟨e, h, heR⟩
        have he : e ∈ M \ P := Finset.mem_sdiff.mpr ⟨heM, heP⟩
        refine ⟨e, he, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨heR hx, fun hxb => Finset.disjoint_left.mp (hdisj e he) hx hxb⟩
      · rw [Finset.card_sdiff_of_subset hPM, hcard]
    · intro M' hM'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM' ⊢
      obtain ⟨hd, hedge, hhit, hcard⟩ := hM'
      have hdisj : ∀ e ∈ M', ∀ f ∈ P, Disjoint e f := by
        intro e he f hf
        have h1 : Disjoint e (P.biUnion id) := disj_of_sub (hedge e he).2
        exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hf) h1
      have hnot : ∀ e ∈ M', e ∉ P := by
        intro e he hP'
        have h1 := hdisj e he e hP'
        have h2 := (hedge e he).1
        have : e = ∅ := Finset.disjoint_self_iff_empty _ |>.mp h1
        rw [this] at h2
        simp at h2
      refine ⟨⟨?_, ?_, ?_, ?_⟩, Finset.subset_union_right⟩
      · intro e he f hf hne
        rcases Finset.mem_union.mp he with he | he <;> rcases Finset.mem_union.mp hf with hf | hf
        · exact hd e he f hf hne
        · exact hdisj e he f hf
        · exact (hdisj f hf e he).symm
        · exact hPd e he f hf hne
      · intro e he
        rcases Finset.mem_union.mp he with he | he
        · exact ⟨(hedge e he).1, (hedge e he).2.trans Finset.sdiff_subset⟩
        · exact hP e he
      · intro R hR
        by_cases hRP : ∃ e ∈ P, e ⊆ R
        · obtain ⟨e, he, heR⟩ := hRP
          exact ⟨e, Finset.mem_union_right _ he, heR⟩
        · obtain ⟨e, he, heR⟩ := hhit (R \ P.biUnion id)
            (Finset.mem_image.mpr ⟨R, Finset.mem_filter.mpr ⟨hR, hRP⟩, rfl⟩)
          exact ⟨e, Finset.mem_union_left _ he, heR.trans Finset.sdiff_subset⟩
      · rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr (fun e he heP => hnot e he heP)),
          hcard]
        omega
    · intro M hM
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM
      exact Finset.sdiff_union_of_subset hM.2
    · intro M' hM'
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hM'
      obtain ⟨hd, hedge, hhit, hcard⟩ := hM'
      have hnot : Disjoint M' P := by
        rw [Finset.disjoint_left]
        intro e he hP'
        have h1 : Disjoint e (P.biUnion id) := disj_of_sub (hedge e he).2
        have h1' := Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hP') h1
        have : e = ∅ := (Finset.disjoint_self_iff_empty _).mp h1'
        have h2 := (hedge e he).1
        rw [this] at h2
        simp at h2
      exact Finset.union_sdiff_cancel_right hnot
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro M _ h
    exact hle ((Finset.card_le_card h.2).trans h.1.2.2.2.le)

def leftU (H S : Finset (Finset (Fin n))) := ordinary H \ S.biUnion (outer H)
def reduced (H S : Finset (Finset (Fin n))) := (base H).image (fun R => R ∩ leftU H S)
def tagged (H M : Finset (Finset (Fin n))) := (cores H).filter (fun c => c ∉ M)

theorem reduced_linear {H : Finset (Finset (Fin n))}
    (ht : ∀ R ∈ H, R.card = 3) (S : Finset (Finset (Fin n))) :
    ∀ R ∈ reduced H S, ∀ T ∈ reduced H S, R ≠ T → (R ∩ T).card ≤ 1 := by
  intro R hR T hT hne
  obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
  have hn : A ≠ B := fun h => hne (congrArg (fun Z => Z ∩ leftU H S) h)
  apply le_trans (Finset.card_le_card (t := A ∩ B) ?_) (base_linear ht hA hB hn)
  intro i hi
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).1,
    (Finset.mem_inter.mp (Finset.mem_inter.mp hi).2).1⟩

theorem core_factors {H M : Finset (Finset (Fin n))}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (v : Valid H M) {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (CoreMatchings H c).card = 2 ∧
    (if c ∈ tagged H M then Mcore M c ∈ CoreMatchings H c else Mcore M c = {c}) := by
  refine ⟨(coreMatchings_explicit ht hd hc).1, ?_⟩
  have h := mcore_behavior ht hd v.1 v.2.1 hc
    (fun R hR => v.2.2 R (Finset.mem_filter.mp hR).1)
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simpa [tagged,hc,h1] using h2


abbrev Names (n : Nat) := Finset (Fin n)
abbrev Family (n : Nat) := Finset (Names n)
abbrev Assignment (n : Nat) := Names n → Family n

def options (H S : Family n) (c : Names n) : Finset (Family n) :=
  if c ∈ S then CoreMatchings H c else if c ∈ cores H then {{c}} else {∅}

def choices (H S : Family n) : Finset (Assignment n) := Fintype.piFinset (options H S)
def pins (H : Family n) (a : Assignment n) : Family n := (cores H).biUnion a

theorem options_card {H S : Family n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) : (choices H S).card = 2 ^ S.card := by
  rw [choices, Fintype.card_piFinset]
  have h (c : Names n) : (options H S c).card = if c ∈ S then 2 else 1 := by
    by_cases hc : c ∈ S
    · simpa [options,hc] using (coreMatchings_explicit ht hd (hs hc)).1
    · by_cases hc' : c ∈ cores H <;> simp [options,hc,hc']
  simp_rw [h]
  rw [Finset.prod_ite]
  simp

theorem mem_ord_no_core {H : Family n} {x : Fin n} (hx : x ∈ ordinary H)
    {c : Names n} (hc : c ∈ cores H) : x ∉ c := by
  intro h
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_biUnion.mpr ⟨c,hc,h⟩)

theorem local_data {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (ha : a ∈ choices H S) {c : Names n} (hc : c ∈ cores H) :
    (a c).card = (if c ∈ S then 2 else 1) ∧
    (a c).biUnion id = (if c ∈ S then c ∪ outer H c else c) ∧
    (∀ g ∈ a c, g.card = 2 ∧ ¬Disjoint g c ∧ g ⊆ c ∪ ordinary H) ∧
    ∀ R ∈ rowsOf H c, ∃ g ∈ a c, g ⊆ R := by
  have hop := (Fintype.mem_piFinset.mp ha) c
  by_cases h : c ∈ S
  · have hp : a c ∈ CoreMatchings H c := by simpa [options,h] using hop
    have hb := ((coreMatchings_explicit ht hd hc).2 (a c) hp)
    have hm := Finset.mem_filter.mp hp
    simp only [if_pos h]
    refine ⟨hm.2.1,hb.1,?_,hb.2.1⟩
    intro g hg
    exact ⟨(hm.2.2.1 g hg).1,(hb.2.2 g hg).1,
      (hb.2.2 g hg).2.trans (Finset.union_subset Finset.subset_union_left ((outer_subset_ordinary ht hd hc).trans Finset.subset_union_right))⟩
  · have hu : a c = {c} := by simpa [options,h,hc] using hop
    have hc2 := ((mem_cores_iff ht).mp hc).1
    have hn : c.Nonempty := Finset.card_pos.mp (by omega)
    simp only [if_neg h,hu,Finset.card_singleton,Finset.singleton_biUnion,id_eq,true_and]
    constructor
    · intro g hg
      obtain rfl := Finset.mem_singleton.mp hg
      exact ⟨hc2, fun hdis => hn.ne_empty ((Finset.disjoint_self_iff_empty _).mp hdis),
        Finset.subset_union_left⟩
    · intro R hR
      exact ⟨c,Finset.mem_singleton_self _,(Finset.mem_filter.mp hR).2⟩

theorem pin_support {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) (ha : a ∈ choices H S) :
    (pins H a).biUnion id = (cores H).biUnion id ∪ S.biUnion (outer H) := by
  ext u
  constructor
  · intro hu
    obtain ⟨g,hg,hug⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨c,hc,hgc⟩ := Finset.mem_biUnion.mp hg
    have h := Finset.mem_biUnion.mpr ⟨g,hgc,hug⟩
    change u ∈ (a c).biUnion id at h
    rw [(local_data ht hd ha hc).2.1] at h
    by_cases hm : c ∈ S
    · rw [if_pos hm] at h
      rcases Finset.mem_union.mp h with h|h
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c,hc,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c,hm,h⟩)
    · rw [if_neg hm] at h
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c,hc,h⟩)
  · intro hu
    have localMem {c : Names n} (hc : c ∈ cores H) (h : u ∈ (a c).biUnion id) :
        u ∈ (pins H a).biUnion id := by
      obtain ⟨g,hg,hu'⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_biUnion.mpr ⟨c,hc,hg⟩,hu'⟩
    rcases Finset.mem_union.mp hu with h|h
    · obtain ⟨c,hc,huc⟩ := Finset.mem_biUnion.mp h
      apply localMem hc
      rw [(local_data ht hd ha hc).2.1]
      split <;> first | exact Finset.mem_union_left _ huc | exact huc
    · obtain ⟨c,hc,huc⟩ := Finset.mem_biUnion.mp h
      apply localMem (hs hc)
      rw [(local_data ht hd ha (hs hc)).2.1, if_pos hc]
      exact Finset.mem_union_right _ huc

theorem pin_unique {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (ha : a ∈ choices H S) {c d : Names n} (hc : c ∈ cores H) (hd' : d ∈ cores H)
    {g : Names n} (hgc : g ∈ a c) (hgd : ¬ Disjoint g d) : c = d := by
  by_contra hn
  obtain ⟨u,hug,hud⟩ := Finset.not_disjoint_iff.mp hgd
  rcases Finset.mem_union.mp (((local_data ht hd ha hc).2.2.1 g hgc).2.2 hug) with hu|hu
  · exact Finset.disjoint_left.mp (cores_pairwise_disjoint ht hd hc hd' hn) hu hud
  · exact mem_ord_no_core hu hd' hud

theorem pin_card {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) (ha : a ∈ choices H S) : (pins H a).card = (cores H).card + S.card := by
  rw [pins,Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun c hc => (local_data ht hd ha hc).1)]
    rw [Finset.sum_ite]
    have hA : (cores H).filter (fun x => x ∈ S) = S := by
      ext x
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun hx => ⟨hs hx,hx⟩⟩
    have hB : (cores H).filter (fun x => x ∉ S) = cores H \ S := by ext; simp
    simp only [hA,hB,Finset.sum_const,Finset.card_sdiff_of_subset hs,smul_eq_mul,mul_one]
    have := Finset.card_le_card hs
    omega
  · intro c hc d hd' hne
    apply Finset.disjoint_left.mpr
    intro g hg hh
    exact hne (pin_unique ht hd ha hc hd' hg (((local_data ht hd ha hd').2.2.1 g hh).2.1))

theorem pair_union_exact {A : Family n} (h : ∀ g ∈ A, g.card = 2) :
    (A.biUnion id).card ≤ 2*A.card ∧ ((A.biUnion id).card = 2*A.card → Dj A) := by
  induction A using Finset.induction_on with
  | empty => simp [Dj]
  | @insert g A hg ih =>
    have hA := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    have hc := h g (Finset.mem_insert_self g A)
    have hsum := Finset.card_union_add_card_inter g (A.biUnion id)
    simp only [Finset.biUnion_insert,id_eq,Finset.card_insert_of_notMem hg]
    constructor
    · omega
    · intro eq
      have hsat : (A.biUnion id).card = 2*A.card := by omega
      have he : (g ∩ A.biUnion id).card = 0 := by omega
      have hdis : Disjoint g (A.biUnion id) :=
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp he)
      intro x hx y hy hne
      rcases Finset.mem_insert.mp hx with hxg|hxa <;> rcases Finset.mem_insert.mp hy with hyg|hya
      · exact (hne (hxg.trans hyg.symm)).elim
      · subst x
        exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hya) hdis
      · subst y
        exact (Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hxa) hdis).symm
      · exact hA.2 hsat x hxa y hya hne

theorem pin_sizes {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (ha : a ∈ choices H S) : ∀ g ∈ pins H a, g.card = 2 := by
  intro g hg
  rcases Finset.mem_biUnion.mp hg with ⟨c,hc,hg⟩
  exact ((local_data ht hd ha hc).2.2.1 g hg).1

theorem pin_disjoint_iff {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) (ha : a ∈ choices H S) :
    Dj (pins H a) ↔ (S.biUnion (outer H)).card = 2*S.card := by
  have hbase : ((cores H).biUnion id).card = 2*(cores H).card :=
    card_biUnion_pairs (fun _ hc => ((mem_cores_iff ht).mp hc).1)
      (fun _ h1 _ h2 hne => cores_pairwise_disjoint ht hd h1 h2 hne)
  have hdj : Disjoint ((cores H).biUnion id) (S.biUnion (outer H)) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    obtain ⟨c,hc,huc⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨d,hd',hud⟩ := Finset.mem_biUnion.mp hv
    exact mem_ord_no_core (outer_subset_ordinary ht hd (hs hd') hud) hc huc
  have hub : ((pins H a).biUnion id).card = 2*(cores H).card + (S.biUnion (outer H)).card := by
    rw [pin_support ht hd hs ha,Finset.card_union_of_disjoint hdj,hbase]
  have hp := pin_card ht hd hs ha
  constructor
  · intro h
    have := card_biUnion_pairs (pin_sizes ht hd ha) h
    omega
  · intro h
    apply (pair_union_exact (pin_sizes ht hd ha)).2
    omega

theorem pin_residual {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) (ha : a ∈ choices H S) :
    Finset.univ \ (pins H a).biUnion id = leftU H S ∧
    (H.filter (fun R => ¬ ∃ e ∈ pins H a, e ⊆ R)).image (fun R => R \ (pins H a).biUnion id) =
      reduced H S := by
  have hleft : Finset.univ \ (pins H a).biUnion id = leftU H S := by
    rw [pin_support ht hd hs ha]
    ext u
    simp [leftU,ordinary,not_or]
  refine ⟨hleft,?_⟩
  have hf : H.filter (fun R => ¬ ∃ e ∈ pins H a, e ⊆ R) = base H := by
    ext R
    constructor
    · intro hR
      obtain ⟨hH,hn⟩ := Finset.mem_filter.mp hR
      rcases mem_base_or_exists_core ht hd hH with hb|⟨c,hc,hcr⟩
      · exact hb
      · obtain ⟨g,hg,hgr⟩ := (local_data ht hd ha hc).2.2.2 R (Finset.mem_filter.mpr ⟨hH,hcr⟩)
        exact (hn ⟨g,Finset.mem_biUnion.mpr ⟨c,hc,hg⟩,hgr⟩).elim
    · intro hR
      obtain ⟨hH,hord⟩ := Finset.mem_filter.mp hR
      apply Finset.mem_filter.mpr
      refine ⟨hH,?_⟩
      rintro ⟨g,hg,hgR⟩
      obtain ⟨c,hc,hgc⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨u,hug,huc⟩ := Finset.not_disjoint_iff.mp (((local_data ht hd ha hc).2.2.1 g hgc).2.1)
      exact mem_ord_no_core (hord (hgR hug)) hc huc
  rw [hf]
  unfold reduced
  apply Finset.image_congr
  intro R _
  rw [← hleft]
  ext u
  simp

def allMatch (s : Nat) (H : Family n) := Finset.univ.filter (Bm Finset.univ H s)
def residualCount (U : Names n) (F : Family n) (s : Nat) := (Finset.univ.filter (Bm U F s)).card
def perBranch (H S : Family n) (s : Nat) :=
  if (S.biUnion (outer H)).card = 2*S.card ∧ (cores H).card+S.card ≤ s then
    residualCount (leftU H S) (reduced H S) (s-(cores H).card-S.card) else 0

theorem pinned_fiber {H S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hs : S ⊆ cores H) (ha : a ∈ choices H S) (s : Nat) :
    ((allMatch s H).filter (fun M => pins H a ⊆ M)).card = perBranch H S s := by
  have hsrc : (allMatch s H).filter (fun M => pins H a ⊆ M) =
      Finset.univ.filter (fun M => Bm Finset.univ H s M ∧ pins H a ⊆ M) := by
    ext; simp [allMatch]
  rw [hsrc]
  have hc := pin_card ht hd hs ha
  by_cases hout : (S.biUnion (outer H)).card = 2*S.card
  · have hdis := (pin_disjoint_iff ht hd hs ha).mpr hout
    rw [decomp _ _ _ _ (fun e he => ⟨pin_sizes ht hd ha e he,Finset.subset_univ e⟩) hdis]
    obtain ⟨l,r⟩ := pin_residual ht hd hs ha
    rw [l,r,hc]
    simp [perBranch,residualCount,hout,Nat.sub_sub]
  · rw [Finset.card_eq_zero.mpr ?_]
    · simp [perBranch,hout]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro M hm
    obtain ⟨hM,hsub⟩ := (Finset.mem_filter.mp hm).2
    apply hout ((pin_disjoint_iff ht hd hs ha).mp ?_)
    exact fun g hg e he hne => hM.1 g (hsub hg) e (hsub he) hne

def pick (H M : Family n) : Assignment n := fun c => if c ∈ cores H then Mcore M c else ∅

theorem picked {H M : Family n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hm : Valid H M) :
    pick H M ∈ choices H (tagged H M) ∧ pins H (pick H M) ⊆ M := by
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro c
    by_cases hc : c ∈ cores H
    · have hf := (core_factors ht hd hm hc).2
      by_cases h : c ∈ tagged H M
      · rw [if_pos h] at hf
        simpa [options,pick,h,hc] using hf
      · rw [if_neg h] at hf
        simpa [options,pick,h,hc] using hf
    · have hh : c ∉ tagged H M := fun h => hc (Finset.mem_filter.mp h).1
      simp [pick,options,hc,hh]
  · intro g hg
    obtain ⟨c,hc,hgc⟩ := Finset.mem_biUnion.mp hg
    have hh : g ∈ Mcore M c := by simpa [pick,hc] using hgc
    exact (Finset.mem_filter.mp hh).1

theorem unique_assignment {H M S : Family n} {a : Assignment n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hm : Valid H M) (hs : S ⊆ cores H) (ha : a ∈ choices H S)
    (hp : pins H a ⊆ M) : a = pick H M ∧ S = tagged H M := by
  have hb : ∀ c ∈ cores H, a c = Mcore M c := by
    intro c hc
    have loc := local_data ht hd ha hc
    have into : a c ⊆ M := fun _ hg => hp (Finset.mem_biUnion.mpr ⟨c,hc,hg⟩)
    ext g
    constructor
    · intro h
      exact Finset.mem_filter.mpr ⟨into h,(loc.2.2.1 g h).2.1⟩
    · intro h
      obtain ⟨hg,hn⟩ := Finset.mem_filter.mp h
      obtain ⟨u,hug,huc⟩ := Finset.not_disjoint_iff.mp hn
      have hu : u ∈ (a c).biUnion id := by
        rw [loc.2.1]
        split <;> first | exact Finset.mem_union_left _ huc | exact huc
      obtain ⟨e,he,hue⟩ := Finset.mem_biUnion.mp hu
      by_cases heq : g = e
      · exact heq ▸ he
      · exact (Finset.disjoint_left.mp (hm.2.1 g hg e (into he) heq) hug hue).elim
  constructor
  · funext c
    by_cases hc : c ∈ cores H
    · simpa [pick,hc] using hb c hc
    · have hS : c ∉ S := fun h => hc (hs h)
      have hh := (Fintype.mem_piFinset.mp ha) c
      simpa [options,pick,hS,hc] using hh
  · ext c
    by_cases hc : c ∈ cores H
    · have k1 := (local_data ht hd ha hc).1
      have h2 := (local_data ht hd (picked ht hd hm).1 hc).1
      rw [hb c hc] at k1
      simp only [pick,if_pos hc] at h2
      by_cases h : c ∈ S <;> by_cases h' : c ∈ tagged H M <;> simp_all
    · have hS : c ∉ S := fun h => hc (hs h)
      simp [tagged,hc,hS]

theorem indicator_unique {H M : Family n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hm : Valid H M) :
    ∑ S ∈ (cores H).powerset, ∑ a ∈ choices H S, (if pins H a ⊆ M then 1 else 0 : Nat) = 1 := by
  have hp := picked ht hd hm
  rw [Finset.sum_eq_single (tagged H M)]
  · rw [Finset.sum_eq_single (pick H M)]
    · simp [hp.2]
    · intro a ha hn
      apply if_neg
      exact fun h => hn (unique_assignment ht hd hm (Finset.filter_subset _ _) ha h).1
    · exact fun h => (h hp.1).elim
  · intro S hS hn
    apply Finset.sum_eq_zero
    intro a ha
    apply if_neg
    exact fun h => hn (unique_assignment ht hd hm (Finset.mem_powerset.mp hS) ha h).2
  · exact fun h => (h (Finset.mem_powerset.mpr (Finset.filter_subset _ _))).elim

theorem allMatch_valid {H M : Family n} {s : Nat} (hm : M ∈ allMatch s H) : Valid H M := by
  obtain ⟨hd,hg,hR,_⟩ := (Finset.mem_filter.mp hm).2
  exact ⟨fun e he => (hg e he).1,hd,hR⟩

theorem branch_sum {H : Family n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (s : Nat) : (allMatch s H).card =
    ∑ S ∈ (cores H).powerset, 2^S.card * perBranch H S s := by
  classical
  let u := allMatch s H
  let b := fun (S : Family n) (a : Assignment n) (M : Family n) => if pins H a ⊆ M then (1:Nat) else 0
  have hsum (S : Family n) (a : Assignment n) :
      (∑ M ∈ u, b S a M) = (u.filter (fun M => pins H a ⊆ M)).card := by
    simp [b]
  calc
    u.card = ∑ M ∈ u, (1:Nat) := by simp
    _ = ∑ M ∈ u, ∑ S ∈ (cores H).powerset, ∑ a ∈ choices H S, b S a M :=
      Finset.sum_congr rfl (fun _ hM => (indicator_unique ht hd (allMatch_valid hM)).symm)
    _ = ∑ S ∈ (cores H).powerset, ∑ M ∈ u, ∑ a ∈ choices H S, b S a M := Finset.sum_comm
    _ = ∑ S ∈ (cores H).powerset, ∑ a ∈ choices H S, ∑ M ∈ u, b S a M :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ S ∈ (cores H).powerset, 2^S.card * perBranch H S s := by
      apply Finset.sum_congr rfl
      intro S hS
      have hs := Finset.mem_powerset.mp hS
      rw [Finset.sum_congr rfl (fun a ha => (hsum S a).trans (pinned_fiber ht hd hs ha s)),
        Finset.sum_const,options_card ht hd hs,smul_eq_mul]

theorem hist_eq (U : Names n) (H : Family n) (s : Nat) :
    Nat.card {N : Family n // (∀ g ∈ N, g.card = 2 ∧ g ⊆ U) ∧
        (∀ g ∈ N, ∀ h ∈ N, g ≠ h → Disjoint g h) ∧
        (∀ R ∈ H, ∃ g ∈ N, g ⊆ R) ∧ N.card = s} = residualCount U H s := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold residualCount
  congr 1
  ext M
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bm,Dj]
  tauto

theorem truncation {ι : Type} [DecidableEq ι] (T : Finset ι) (k y : ι → Nat) (p : ι → Prop)
    [DecidablePred p] (t : Nat) :
    (∑ i ∈ T, 2^(k i) * (if p i then y i else 0)) % (2^t) =
    (∑ i ∈ T.filter (fun i => k i < t ∧ p i), 2^(k i)*y i) % (2^t) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    by_cases hk : k i < t
    · by_cases hp : p i
      · simp only [Finset.sum_insert hi,Finset.filter_insert,if_pos hp,if_pos (And.intro hk hp),
          Finset.sum_insert (Finset.notMem_mono (Finset.filter_subset _ _) hi)]
        rw [Nat.add_mod,ih,← Nat.add_mod]
      · have hm : ¬ (k i < t ∧ p i) := fun hh => hp hh.2
        simpa only [Finset.sum_insert hi,Finset.filter_insert,if_neg hp,if_neg hm,mul_zero,zero_add] using ih
    · have divisible : 2^t ∣ (2:Nat)^(k i)*y i :=
        dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _
      by_cases hp : p i
      · have hm : ¬ (k i < t ∧ p i) := fun hh => hk hh.1
        simp only [Finset.sum_insert hi,Finset.filter_insert,if_neg hm,
          if_pos hp]
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd divisible,zero_add,Nat.mod_mod,ih]
      · have hm : ¬ (k i < t ∧ p i) := fun hh => hp hh.2
        simpa only [Finset.sum_insert hi,Finset.filter_insert,if_neg hp,if_neg hm,mul_zero,zero_add] using ih

theorem modulo_sum {H : Family n}
    (ht : ∀ R ∈ H, R.card = 3) (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (s t : Nat) : (allMatch s H).card % (2^t) =
    ((cores H).powerset.filter (fun S => S.card < t ∧ (S.biUnion (outer H)).card = 2*S.card ∧
        (cores H).card+S.card ≤ s)).sum (fun S =>
          2^S.card * residualCount (leftU H S) (reduced H S) (s-(cores H).card-S.card)) % (2^t) := by
  rw [branch_sum ht hd]
  exact truncation _ _ _ _ _

end PEqualNP.Outside.L_lib_931


open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903

variable {α : Type*} [DecidableEq α]
abbrev Rows (α : Type*) := Finset (Finset α)

def Linear (H : Rows α) : Prop :=
  ∀ R ∈ H, ∀ S ∈ H, R ≠ S → (R ∩ S).card ≤ 1

def Covers (U : Finset α) (H M : Rows α) (s : Nat) : Prop :=
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ M, e.card = 2 ∧ e ⊆ U) ∧
  (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧ M.card = s

theorem requireTwo (U : Finset α) {H M : Rows α} {s : Nat}
    (h : Covers U H M s) {R : Finset α} (hR : R ∈ H) : 2 ≤ R.card := by
  obtain ⟨e, he, heR⟩ := h.2.2.1 R hR
  simpa [ (h.2.1 e he).1 ] using card_le_card heR

theorem filteredBounds (U C : Finset α) {H M : Rows α} {s : Nat}
    (lin : Linear H) (h : Covers U H M s) :
    (H.filter (fun R => R ⊆ C)).card ≤ (M.filter (fun e => e ⊆ C)).card ∧
      2 * (H.filter (fun R => R ⊆ C)).card ≤ C.card := by
  classical
  let f (R : Finset α) : Finset α := if hr : R ∈ H then
    Classical.choose (h.2.2.1 R hr) else ∅
  have hf {R : Finset α} (hr : R ∈ H) : f R ∈ M ∧ f R ⊆ R := by
    simpa only [f, dite_eq_left hr] using Classical.choose_spec (h.2.2.1 R hr)
  let HC := H.filter (fun R => R ⊆ C)
  let MC := M.filter (fun e => e ⊆ C)
  have hi : HC.card ≤ MC.card := by
    apply Finset.card_le_card_of_injOn f
    · intro R hR
      change R ∈ HC at hR
      obtain ⟨hRH, hRC⟩ := mem_filter.mp hR
      exact mem_filter.mpr ⟨(hf hRH).1, (hf hRH).2.trans hRC⟩
    · intro R hR S hS he
      change R ∈ HC at hR
      change S ∈ HC at hS
      have hr := (mem_filter.mp hR).1
      have hs := (mem_filter.mp hS).1
      by_contra hn
      have hsub : f R ⊆ R ∩ S := by
        intro a ha
        exact mem_inter.mpr ⟨(hf hr).2 ha, (hf hs).2 (he ▸ ha)⟩
      have htwo := card_le_card hsub
      rw [(h.2.1 _ (hf hr).1).1] at htwo
      exact (by have := lin R hr S hs hn; omega : False)
  have hd : (MC : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hne
    exact h.1 _ (mem_filter.mp he).1 _ (mem_filter.mp hf).1 hne
  have hsum : (MC.biUnion id).card = 2 * MC.card := by
    rw [Finset.card_biUnion hd]
    calc
      _ = ∑ _x ∈ MC, 2 := Finset.sum_congr rfl (fun e he => (h.2.1 e (mem_filter.mp he).1).1)
      _ = 2 * MC.card := by simp [Nat.mul_comm]
  have hsub : MC.biUnion id ⊆ C := by
    intro a ha
    obtain ⟨e, he, ha'⟩ := mem_biUnion.mp ha
    exact (mem_filter.mp he).2 ha'
  have hb := card_le_card hsub
  rw [hsum] at hb
  change HC.card ≤ MC.card ∧ 2 * HC.card ≤ C.card
  exact ⟨hi, by omega⟩

theorem noBadCount [Fintype α] (U : Finset α) (H : Rows α) (s : Nat)
    (lin : Linear H)
    (bad : (∃ R ∈ H, R.card < 2) ∨
      (∃ C : Finset α, C.card < 2 * (H.filter (fun R => R ⊆ C)).card)) :
    Nat.card {M : Rows α // Covers U H M s} = 0 := by
  have hEmpty : IsEmpty {M : Rows α // Covers U H M s} := ⟨by
    intro ⟨M, hM⟩
    rcases bad with ⟨R, hrH, hR⟩ | ⟨C, hC⟩
    · exact (Nat.not_lt_of_ge (requireTwo U hM hrH)) hR
    · exact (Nat.not_lt_of_ge (filteredBounds U C lin hM).2) hC⟩
  letI := hEmpty
  simp [Nat.card_eq_fintype_card]

theorem requireSize (U : Finset α) {H M : Rows α} {s : Nat}
    (hU : ∀ R ∈ H, R ⊆ U) (lin : Linear H) (h : Covers U H M s) :
    H.card ≤ s := by
  classical
  have hi := (filteredBounds U U lin h).1
  have hHU : H.filter (fun R => R ⊆ U) = H := filter_true_of_mem hU
  have hMU : M.filter (fun e => e ⊆ U) = M := filter_true_of_mem (fun e he => (h.2.1 e he).2)
  rwa [hHU, hMU, h.2.2.2] at hi

theorem noSmallCount [Fintype α] (U : Finset α) (H : Rows α) (s : Nat)
    (hU : ∀ R ∈ H, R ⊆ U) (lin : Linear H) (hsmall : s < H.card) :
    Nat.card {M : Rows α // Covers U H M s} = 0 := by
  let hEmpty : IsEmpty {M : Rows α // Covers U H M s} :=
    ⟨fun M => (Nat.not_lt_of_ge (requireSize U hU lin M.2)) hsmall⟩
  exact Nat.card_of_isEmpty

theorem uniqueHitter {U : Finset α} {H M : Rows α} {s : Nat}
    (h : Covers U H M s) {R : Finset α} (hR : R ∈ H) (hc : R.card ≤ 3) :
    ∃! e, e ∈ M ∧ e ⊆ R := by
  obtain ⟨e,he,heR⟩ := h.2.2.1 R hR
  refine ⟨e, ⟨he,heR⟩, ?_⟩
  rintro f ⟨hf,hfR⟩
  by_contra hn
  have hd := h.1 f hf e he hn
  have hu : f ∪ e ⊆ R := union_subset hfR heR
  have hh := card_le_card hu
  rw [Finset.card_union_of_disjoint hd, (h.2.1 f hf).1, (h.2.1 e he).1] at hh
  omega
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence
variable {α : Type*} [DecidableEq α]
abbrev Rows (α : Type*) := Finset (Finset α)
abbrev Nodes (U : Finset α) (H : Rows α) := U ⊕ H

def graph (U : Finset α) (H : Rows α) : SimpleGraph (Nodes U H) where
  Adj
  | .inl a, .inr R => a.1 ∈ R.1
  | .inr R, .inl a => a.1 ∈ R.1
  | _, _ => False
  symm := by constructor; intro a b; cases a <;> cases b <;> exact fun h => h
  loopless := by constructor; intro a; cases a <;> exact not_false

def incEdge (U : Finset α) (H : Rows α) (h : ∀ R ∈ H, R ⊆ U)
    (i : Σ R : H, R.val) : (graph U H).edgeSet :=
  ⟨s(Sum.inl ⟨i.2.1, h i.1.1 i.1.2 i.2.2⟩, Sum.inr i.1), by
     exact (SimpleGraph.mem_edgeSet (G := graph U H)).mpr i.2.2⟩

theorem incBij (U : Finset α) (H : Rows α) (h : ∀ R ∈ H, R ⊆ U) :
    Function.Bijective (incEdge U H h) := by
  constructor
  · rintro ⟨R,a⟩ ⟨S,b⟩ he
    have hv := congrArg Subtype.val he
    rw [incEdge, incEdge, Sym2.eq_iff] at hv
    rcases hv with ⟨ha, hr⟩ | ⟨hh, _⟩
    · have hr' : R = S := Sum.inr.inj hr
      subst S
      have ha' : (⟨a.val, h R.1 R.2 a.2⟩ : U) = ⟨b.val, h R.1 R.2 b.2⟩ := Sum.inl.inj ha
      have hab : a = b := Subtype.ext (congrArg (fun u : U => u.val) ha')
      subst b
      rfl
    · exact (Sum.inl_ne_inr hh).elim
  · rintro ⟨z,hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      have hab := (SimpleGraph.mem_edgeSet (G := graph U H)).mp hz
      cases a with
      | inl a =>
        cases b with
        | inl b => exact False.elim hab
        | inr b => exact ⟨⟨b,⟨a.1,hab⟩⟩, rfl⟩
      | inr a =>
        cases b with
        | inl b =>
          refine ⟨⟨a,⟨b.1,hab⟩⟩,Subtype.ext ?_⟩
          exact Sym2.eq_swap
        | inr b => exact False.elim hab

theorem cardEdges (U : Finset α) (H : Rows α) (h : ∀ R ∈ H, R ⊆ U) :
    Nat.card (graph U H).edgeSet = ∑ R ∈ H, R.card := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective (incEdge U H h) (incBij U H h))]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma, Finset.sum_attach]

theorem incidenceTree (U : Finset α) (H : Rows α) (h : ∀ R ∈ H, R ⊆ U)
    (hc : (graph U H).Connected)
    (hsize : (∑ R ∈ H, R.card) + 1 = U.card + H.card) :
    (graph U H).IsTree := by
  refine SimpleGraph.isTree_iff_connected_and_card.mpr ⟨hc, ?_⟩
  simpa [cardEdges U H h, Nat.card_eq_fintype_card, Fintype.card_sum] using hsize

theorem cardSum (H : Rows α) (hr : ∀ R ∈ H, 2 ≤ R.card ∧ R.card ≤ 3) :
    (∑ R ∈ H, R.card) + (H.filter (fun R => R.card = 2)).card = 3 * H.card := by
  classical
  have hadd := Finset.sum_filter (s := H) (p := fun R => R.card = 2) (f := fun _ => (1 : Nat))
  calc
    _ = (∑ R ∈ H, R.card) + ∑ R ∈ H, (if R.card = 2 then (1:Nat) else 0) := by
      rw [← hadd]
      simp
    _ = ∑ R ∈ H, (R.card + if R.card = 2 then (1:Nat) else 0) := by
      rw [Finset.sum_add_distrib]
    _ = 3 * H.card := by
      calc
        _ = ∑ _R ∈ H, (3 : Nat) := by
          apply Finset.sum_congr rfl
          intro R hR
          have := hr R hR
          split <;> omega
        _ = 3 * H.card := by simp [Nat.mul_comm]

theorem connectedClassification (U : Finset α) (H : Rows α)
    (h : ∀ R ∈ H, R ⊆ U) (hr : ∀ R ∈ H, 2 ≤ R.card ∧ R.card ≤ 3)
    (hc : (graph U H).Connected) (hn : 2 * H.card ≤ U.card) :
    (U.card = 2 * H.card + 1 ∧ (H.filter (fun R => R.card = 2)).card = 0 ∧ (graph U H).IsTree) ∨
    (U.card = 2 * H.card ∧ (H.filter (fun R => R.card = 2)).card = 1 ∧ (graph U H).IsTree) ∨
    (U.card = 2 * H.card ∧ (H.filter (fun R => R.card = 2)).card = 0 ∧
      Nat.card (graph U H).edgeSet = Nat.card (Nodes U H)) := by
  classical
  have hs := cardSum H hr
  have hg : U.card + H.card ≤ (∑ R ∈ H, R.card) + 1 := by
    have hg := hc.card_vert_le_card_edgeSet_add_one
    rw [cardEdges U H h] at hg
    simpa [Nat.card_eq_fintype_card, Fintype.card_sum] using hg
  have hv : U.card = 2 * H.card + 1 ∨ U.card = 2 * H.card := by omega
  rcases hv with hv | hv
  · left
    exact ⟨hv, by omega, incidenceTree U H h hc (by omega)⟩
  · right
    by_cases ht : (H.filter (fun R => R.card = 2)).card = 1
    · exact Or.inl ⟨hv, ht, incidenceTree U H h hc (by omega)⟩
    · refine Or.inr ⟨hv, by omega, ?_⟩
      rw [cardEdges U H h, Nat.card_eq_fintype_card, Fintype.card_sum]
      simp only [Fintype.card_coe]
      omega
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence

namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Orientation
variable {V : Type*} {G : SimpleGraph V}

def Outward (G : SimpleGraph V) (r : V) (O : V → V → Prop) : Prop :=
  (∀ u v, O u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → (O u v ↔ ¬O v u)) ∧
  (∀ u, ¬ O u r) ∧ ∀ v, v ≠ r → ∃! u, O u v

def Closer (G : SimpleGraph V) (r u v : V) : Prop :=
  G.Adj u v ∧ G.dist u r < G.dist v r

theorem closerStep (h : G.IsTree) {r u v : V} (huv : Closer G r u v) :
    G.dist v r = G.dist u r + 1 := by
  have hd := h.dist_eq_dist_add_one_of_adj r huv.1
  rw [G.dist_comm (u := r) (v := u), G.dist_comm (u := r) (v := v)] at hd
  have ht := huv.2
  omega

theorem closerInv (h : G.IsTree) (r : V) {u v : V} (ha : G.Adj u v) :
    Closer G r u v ↔ ¬ Closer G r v u := by
  have hd := h.dist_eq_dist_add_one_of_adj r ha
  rw [G.dist_comm (u := r) (v := u), G.dist_comm (u := r) (v := v)] at hd
  simp only [Closer, ha, ha.symm, true_and]
  omega

theorem closerExists (h : G.IsTree) (r v : V) (hv : v ≠ r) :
    ∃! u, Closer G r u v := by
  obtain ⟨q,hq⟩ := h.connected.exists_walk_length_eq_dist v r
  cases q with
  | nil => exact (hv rfl).elim
  | @cons _ u _ adj tail =>
    have hh : Closer G r u v := by
      refine ⟨adj.symm, ?_⟩
      have ht := G.dist_le tail
      simp only [SimpleGraph.Walk.length_cons] at hq
      omega
    refine ⟨u, hh, fun w hw => ?_⟩
    have ht := closerStep h hw
    obtain ⟨p,hp⟩ := h.connected.exists_walk_length_eq_dist w r
    have hwp : (SimpleGraph.Walk.cons hw.1.symm p).length = G.dist v r := by
      simp [ht,hp]
    have hq' : (SimpleGraph.Walk.cons adj tail).IsPath :=
      (SimpleGraph.Walk.cons adj tail).isPath_of_length_eq_dist hq
    have he := (h.existsUnique_path v r).unique
      ((SimpleGraph.Walk.cons hw.1.symm p).isPath_of_length_eq_dist hwp) hq'
    simpa using congrArg (fun p : G.Walk v r => p.snd) he

theorem closerOutward (h : G.IsTree) (r : V) : Outward G r (Closer G r) := by
  exact ⟨fun _ _ h => h.1, fun _ _ h' => closerInv h r h',
    fun u hx => (Nat.not_lt_zero (G.dist u r) (by simpa using hx.2)), closerExists h r⟩

theorem orientationUnique (h : G.IsTree) (r : V) {O : V → V → Prop}
    (ho : Outward G r O) : O = Closer G r := by
  have hc (n : Nat) : ∀ u v, G.dist v r = n → Closer G r u v → O u v := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro u v hn huv
      have hlt := huv.2
      apply (ho.2.1 u v huv.1).mpr
      intro hvu
      by_cases hu : u = r
      · subst u
        exact ho.2.2.1 _ hvu
      · obtain ⟨w, hw, _⟩ := closerExists h r u hu
        have hw' := ih (G.dist u r) (by omega) w u rfl hw
        obtain ⟨j, _, hju⟩ := ho.2.2.2 u hu
        have he := (hju v hvu).trans (hju w hw').symm
        subst w
        exact (Nat.lt_asymm hw.2 hlt)
  funext u v
  apply propext
  constructor
  · intro huv
    have ha := ho.1 u v huv
    by_contra hn
    have hcv : Closer G r v u := by
      by_contra hn'
      exact hn ((closerInv h r ha).mpr hn')
    exact ((ho.2.1 u v ha).mp huv) (hc _ v u rfl hcv)
  · exact hc _ u v rfl

theorem existsUniqueOutward (h : G.IsTree) (r : V) : ∃! O, Outward G r O :=
  ⟨Closer G r, closerOutward h r, fun _ ho => orientationUnique h r ho⟩
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Orientation

namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903PlusEdge
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Orientation
variable {V : Type*} {G T : SimpleGraph V}

def AllIncoming (G : SimpleGraph V) (O : V → V → Prop) : Prop :=
  (∀ u v, O u v → G.Adj u v) ∧
  (∀ u v, G.Adj u v → (O u v ↔ ¬O v u)) ∧
  ∀ v, ∃! u, O u v

def Extra (x y u v : V) : Prop :=
  (u = x ∧ v = y) ∨ (u = y ∧ v = x)

theorem extraSymm {x y u v : V} : Extra x y u v ↔ Extra x y v u := by
  unfold Extra
  tauto

theorem orientedExtension (hT : T.IsTree) (x y : V) (hxy : x ≠ y)
    (hd : ¬ T.Adj x y)
    (ha : ∀ u v, G.Adj u v ↔ T.Adj u v ∨ Extra x y u v) :
    ∃! O, AllIncoming G O ∧ O x y := by
  classical
  let F := Closer T y
  let E (u v : V) := F u v ∨ (u = x ∧ v = y)
  have hf : Outward T y F := closerOutward hT y
  have hsep : ∀ u v, T.Adj u v → ¬Extra x y u v := by
    intro u v ht he
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hd ht
    · exact hd ht.symm
  have hFsep : ∀ u v, Extra x y u v → ¬F u v := by
    intro u v he ho
    exact hsep u v (hf.1 u v ho) he
  refine ⟨E, ⟨⟨?_, ?_, ?_⟩, Or.inr ⟨rfl,rfl⟩⟩, ?_⟩
  · intro u v h
    exact (ha u v).mpr (h.elim (fun h => Or.inl (hf.1 u v h))
      (fun h => Or.inr (Or.inl h)))
  · intro u v h
    rcases (ha u v).mp h with ht | he
    · have h1 := hsep u v ht
      have h2 := hsep v u ht.symm
      have hre := hf.2.1 u v ht
      unfold E Extra at *
      tauto
    · have h1 := hFsep u v he
      have h2 := hFsep v u (extraSymm.mp he)
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [E,hxy,h2]
      · simp [E,hxy,h1]
  · intro v
    by_cases hv : v = y
    · subst v
      exact ⟨x, Or.inr ⟨rfl,rfl⟩, fun u hu => hu.elim
        (fun h => (hf.2.2.1 u h).elim) And.left⟩
    · obtain ⟨u,hu,hu'⟩ := hf.2.2.2 v hv
      exact ⟨u, Or.inl hu, fun w hw => hw.elim (hu' w) (fun he => (hv he.2).elim)⟩
  · intro O hO
    have hxyA : G.Adj x y := (ha x y).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩))
    have hnyx : ¬ O y x := (hO.1.2.1 x y hxyA).mp hO.2
    have hres : Outward T y (fun u v => O u v ∧ T.Adj u v) := by
      refine ⟨fun _ _ h => h.2, ?_, ?_, ?_⟩
      · intro u v ht
        have h := hO.1.2.1 u v ((ha u v).mpr (Or.inl ht))
        simp only [ht, ht.symm, and_true, h]
      · intro u hu
        obtain ⟨w, _, hw⟩ := hO.1.2.2 y
        have he := (hw u hu.1).trans (hw x hO.2).symm
        subst u
        exact hd hu.2
      · intro v hv
        obtain ⟨u,hu,hu'⟩ := hO.1.2.2 v
        refine ⟨u, ⟨hu, ?_⟩, fun w hw => hu' w hw.1⟩
        rcases (ha u v).mp (hO.1.1 u v hu) with ht | ⟨_, he⟩ | ⟨rfl,rfl⟩
        · exact ht
        · exact (hv he).elim
        · exact (hnyx hu).elim
    have he := orientationUnique hT y hres
    funext u v
    apply propext
    have hr : (O u v ∧ T.Adj u v) ↔ F u v :=
      Iff.of_eq (congrFun (congrFun he u) v)
    constructor
    · intro ho
      rcases (ha u v).mp (hO.1.1 u v ho) with ht | ht | ⟨rfl,rfl⟩
      · exact Or.inl (hr.mp ⟨ho,ht⟩)
      · exact Or.inr ht
      · exact (hnyx ho).elim
    · intro hex
      rcases hex with hf | ⟨rfl,rfl⟩
      · exact (hr.mpr hf).1
      · exact hO.2

theorem exactlyTwoExtensions (hT : T.IsTree) (x y : V) (hxy : x ≠ y) (hd : ¬ T.Adj x y)
    (ha : ∀ u v, G.Adj u v ↔ T.Adj u v ∨ Extra x y u v) :
    ∃ O P, O ≠ P ∧ AllIncoming G O ∧ AllIncoming G P ∧
      ∀ X, AllIncoming G X → X = O ∨ X = P := by
  have hd' : ¬ T.Adj y x := fun h => hd h.symm
  have ha' : ∀ u v, G.Adj u v ↔ T.Adj u v ∨ Extra y x u v := by
    intro u v
    rw [ha]
    unfold Extra
    tauto
  obtain ⟨O,ho,ho'⟩ := orientedExtension hT x y hxy hd ha
  obtain ⟨P,hp,hp'⟩ := orientedExtension hT y x hxy.symm hd' ha'
  have hA : G.Adj x y := (ha x y).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩))
  refine ⟨O,P,fun h => (ho.1.2.1 x y hA).mp ho.2 (h ▸ hp.2), ho.1,hp.1,?_⟩
  intro X hx
  by_cases hx' : X x y
  · exact Or.inl (ho' X ⟨hx,hx'⟩)
  · exact Or.inr (hp' X ⟨hx,(hx.2.1 y x hA.symm).mpr hx'⟩)

theorem connectedExactlyTwo [Finite V] (hG : G.Connected)
    (hcard : Nat.card G.edgeSet = Nat.card V) :
    ∃ O P, O ≠ P ∧ AllIncoming G O ∧ AllIncoming G P ∧
      ∀ X, AllIncoming G X → X = O ∨ X = P := by
  classical
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite G.edgeSet
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  letI := Fintype.ofFinite T.edgeSet
  have hsub : T.edgeFinset ⊆ G.edgeFinset := by
    simpa using (SimpleGraph.edgeSet_mono hTG)
  have hTc := hT.card_edgeFinset
  have hGc : G.edgeFinset.card = Fintype.card V := by
    rw [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card]
  have hs : (G.edgeFinset \ T.edgeFinset).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hGc]
    omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hs
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hx : G.Adj x y ∧ ¬ T.Adj x y := by
      have hm : s(x,y) ∈ G.edgeFinset \ T.edgeFinset := by
        rw [hz]; exact Finset.mem_singleton_self _
      simpa [SimpleGraph.mem_edgeSet] using hm
    refine exactlyTwoExtensions hT x y hx.1.ne hx.2 ?_
    intro u v
    constructor
    · intro ha
      by_cases ht : T.Adj u v
      · exact Or.inl ht
      · have hm : s(u,v) ∈ G.edgeFinset \ T.edgeFinset := by
          simp [SimpleGraph.mem_edgeSet, ha, ht]
        rw [hz, Finset.mem_singleton, Sym2.eq_iff] at hm
        exact Or.inr hm
    · rintro (ht | he)
      · exact hTG ht
      · rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hx.1
        · exact hx.1.symm
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903PlusEdge

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components
variable {α : Type*} [DecidableEq α]
abbrev Rows (α : Type*) := Finset (Finset α)

def Closed (H : Rows α) (A : Finset α) : Prop :=
  ∀ R ∈ H, ¬ Disjoint R A → R ⊆ A

open Classical in
noncomputable def step (H : Rows α) (A : Finset α) : Finset α :=
  A ∪ (H.filter (fun R => ¬ Disjoint R A)).biUnion id

theorem leStep (H : Rows α) (A : Finset α) : A ⊆ step H A := by
  classical
  unfold step
  exact subset_union_left

theorem stepEq (H : Rows α) (A : Finset α) : step H A = A ↔ Closed H A := by
  classical
  unfold step Closed
  constructor
  · intro h R hR hA a ha
    rw [← h]
    exact mem_union_right _ (mem_biUnion.mpr ⟨R,mem_filter.mpr ⟨hR,hA⟩,ha⟩)
  · intro h
    refine union_eq_left.mpr ?_
    intro a ha
    obtain ⟨R,hR,ha⟩ := mem_biUnion.mp ha
    exact h R (mem_filter.mp hR).1 (mem_filter.mp hR).2 ha

theorem stepLeOfLeClosed {H : Rows α} {A B : Finset α} (hab : A ⊆ B)
    (hc : Closed H B) : step H A ⊆ B := by
  classical
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · exact hab ha
  · obtain ⟨R,hr,ha⟩ := mem_biUnion.mp ha
    obtain ⟨hr, hn⟩ := mem_filter.mp hr
    exact hc R hr (fun h => hn (h.mono_right hab)) ha

noncomputable def seq (H : Rows α) (A : Finset α) : Nat → Finset α
  | 0 => A
  | n + 1 => step H (seq H A n)

theorem seqSub (H : Rows α) {A B : Finset α} (hab : A ⊆ B) (h : Closed H B) :
    ∀ n, seq H A n ⊆ B := by
  intro n
  induction n with
  | zero => exact hab
  | succ n ih => exact stepLeOfLeClosed ih h

theorem inputSubSeq (H : Rows α) (A : Finset α) (n : Nat) : A ⊆ seq H A n := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih => exact ih.trans (leStep _ _)

theorem seqClosedAt [Fintype α] (H : Rows α) (A : Finset α) (hA : A.Nonempty) :
    Closed H (seq H A (Fintype.card α)) := by
  classical
  have growth (n : Nat) (hn : ¬ Closed H (seq H A n)) : n + 1 ≤ (seq H A n).card := by
    induction n with
    | zero => simpa [seq] using Finset.card_pos.mpr hA
    | succ n ih =>
      have hna : ¬ Closed H (seq H A n) := by
        intro h
        exact hn (by simpa only [seq, (stepEq _ _).mpr h] using h)
      have hlt : seq H A n ⊂ seq H A (n+1) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨leStep _ _, ?_⟩
        exact fun h => hna ((stepEq _ _).mp h.symm)
      have hc := Finset.card_lt_card hlt
      have hi := ih hna
      omega
  by_contra hn
  have h := growth _ hn
  have hu := Finset.card_le_univ (seq H A (Fintype.card α))
  omega

theorem foldSeq (H : Rows α) (A : Finset α) (l : List Nat) :
    l.foldl (fun A _ => step H A) A = seq H A l.length := by
  have hs (A : Finset α) (n : Nat) : seq H (step H A) n = seq H A (n+1) := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (step H) ih
  induction l generalizing A with
  | nil => rfl
  | cons z l ih => rw [List.foldl_cons, ih, hs, List.length_cons]

noncomputable def component [Fintype α] (H : Rows α) (v : α) : Finset α :=
  seq H {v} (Fintype.card α)

theorem selfMem [Fintype α] (H : Rows α) (v : α) : v ∈ component H v :=
  inputSubSeq H {v} _ (mem_singleton_self v)

theorem componentClosed [Fintype α] (H : Rows α) (v : α) : Closed H (component H v) :=
  seqClosedAt H {v} (singleton_nonempty v)

theorem componentLe [Fintype α] {H : Rows α} {v : α} {B : Finset α} (hv : v ∈ B)
    (hb : Closed H B) : component H v ⊆ B :=
  seqSub H (singleton_subset_iff.mpr hv) hb _

theorem componentSymm [Fintype α] {H : Rows α} {v w : α} (hw : w ∈ component H v) :
    v ∈ component H w := by
  classical
  have aux (n : Nat) (w : α) (hw : w ∈ seq H {v} n) : v ∈ component H w := by
    induction n generalizing w with
    | zero =>
      have hwv : w = v := mem_singleton.mp hw
      subst w
      exact selfMem H v
    | succ n ih =>
      change w ∈ step H (seq H {v} n) at hw
      rcases mem_union.mp hw with hw | hw
      · exact ih w hw
      · obtain ⟨R,hr,hwr⟩ := mem_biUnion.mp hw
        obtain ⟨hr, hn⟩ := mem_filter.mp hr
        obtain ⟨b,hbr,hb⟩ := not_disjoint_iff.mp hn
        have hbc :=
          componentClosed H w R hr (not_disjoint_iff.mpr ⟨w,hwr,selfMem H w⟩) hbr
        exact componentLe hbc (componentClosed H w) (ih b hb)
  exact aux _ w hw

theorem componentEq [Fintype α] {H : Rows α} {v w : α} (hw : w ∈ component H v) :
    component H v = component H w :=
  Subset.antisymm (componentLe (componentSymm hw) (componentClosed H w))
    (componentLe hw (componentClosed H v))

theorem partsDisjoint [Fintype α] (H : Rows α) (U : Finset α) :
    ∀ C ∈ U.image (component H), ∀ D ∈ U.image (component H), C ≠ D → Disjoint C D := by
  intro C hc D hd hne
  obtain ⟨v,_,rfl⟩ := mem_image.mp hc
  obtain ⟨w,_,rfl⟩ := mem_image.mp hd
  refine Finset.disjoint_left.mpr ?_
  intro a ha hb
  exact hne ((componentEq ha).trans (componentEq hb).symm)

theorem componentIn [Fintype α] {H : Rows α} {U : Finset α} (hu : ∀ R ∈ H, R ⊆ U)
    {v : α} (hv : v ∈ U) : component H v ⊆ U :=
  componentLe hv (fun R hr _ => hu R hr)

theorem partsUnion [Fintype α] {H : Rows α} {U : Finset α} (hu : ∀ R ∈ H, R ⊆ U) :
    (U.image (component H)).biUnion id = U := by
  ext a
  constructor
  · intro ha
    obtain ⟨C,hc,hac⟩ := mem_biUnion.mp ha
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hc
    exact componentIn hu hv hac
  · intro ha
    exact mem_biUnion.mpr ⟨component H a,mem_image.mpr ⟨a,ha,rfl⟩,selfMem H a⟩
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Connectivity
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence (Nodes graph)
variable {α : Type*} [DecidableEq α] [Fintype α]

open Classical in
noncomputable def edges (C : Finset α) (H : Rows α) := H.filter (fun R => R ⊆ C)

theorem connected (H : Rows α) (v : α) (hne : ∀ R ∈ H, R.Nonempty) :
    (graph (component H v) (edges (component H v) H)).Connected := by
  classical
  let C := component H v
  let E := edges C H
  let G := graph C E
  let root : Nodes C E := .inl ⟨v,selfMem H v⟩
  have hsub (n : Nat) : seq H {v} n ⊆ C :=
    seqSub H (singleton_subset_iff.mpr (selfMem H v)) (componentClosed H v) n
  have reach (n : Nat) (a : α) (ha : a ∈ seq H {v} n) :
      G.Reachable root (.inl ⟨a,hsub n ha⟩) := by
    induction n generalizing a with
    | zero =>
      have hav : a = v := mem_singleton.mp ha
      subst a
      exact SimpleGraph.Reachable.refl _
    | succ n ih =>
      change a ∈ step H (seq H {v} n) at ha
      rcases mem_union.mp ha with h | h
      · exact ih a h
      · obtain ⟨R,hR,haR⟩ := mem_biUnion.mp h
        obtain ⟨hr, hn⟩ := mem_filter.mp hR
        obtain ⟨b,hbR,hb⟩ := not_disjoint_iff.mp hn
        have hRC : R ⊆ C := componentClosed H v R hr
          (not_disjoint_iff.mpr ⟨b,hbR,hsub n hb⟩)
        let r : E := ⟨R, mem_filter.mpr ⟨hr,hRC⟩⟩
        have hBR : G.Adj (.inl ⟨b,hsub n hb⟩) (.inr r) := hbR
        have hRA : G.Adj (.inr r) (.inl ⟨a,hsub (n+1) ha⟩) := haR
        exact (ih b hb).trans (hBR.reachable.trans hRA.reachable)
  refine (SimpleGraph.connected_iff_exists_forall_reachable (G := G)).mpr ⟨root, ?_⟩
  intro node
  cases node with
  | inl a => exact reach _ a.1 a.2
  | inr r =>
    obtain ⟨hr,hRC⟩ := mem_filter.mp r.2
    obtain ⟨a,ha⟩ := hne r.1 hr
    have hAR : G.Adj (.inl ⟨a,hRC ha⟩) (.inr r) := ha
    exact (reach _ a (hRC ha)).trans hAR.reachable
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Connectivity

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Involution
variable {α : Type*} [DecidableEq α] [Fintype α]

theorem transpositionType (j : Nat) (hj : Fintype.card α = 2 * j) :
    (univ.filter (fun p : Equiv.Perm α => p.cycleType = Multiset.replicate j 2)).card =
      (2*j).factorial / (2^j*j.factorial) := by
  have hfac : (∏ n ∈ (Multiset.replicate j (2 : Nat)).toFinset,
      ((Multiset.replicate j (2 : Nat)).count n).factorial) = j.factorial := by
    cases j with
    | zero => simp
    | succ j =>
      have hh : (Multiset.replicate (j+1) (2 : Nat)).toFinset = {2} := by
        ext x
        constructor
        · intro hm
          exact Finset.mem_singleton.mpr
            (Multiset.eq_of_mem_replicate (Multiset.mem_toFinset.mp hm))
        · intro hm
          obtain rfl := Finset.mem_singleton.mp hm
          exact Multiset.mem_toFinset.mpr (by simp)
      rw [hh, Finset.prod_singleton, Multiset.count_replicate_self]
  have htwo : ∀ x ∈ Multiset.replicate j (2 : Nat), 2 ≤ x := by
    intro x hx
    rw [Multiset.eq_of_mem_replicate hx]
  have hsum : (Multiset.replicate j (2 : Nat)).sum = 2*j := by simp [Nat.mul_comm]
  rw [Equiv.Perm.card_of_cycleType α, if_pos ⟨by rw [hsum, hj], htwo⟩, hfac, hsum,
    Multiset.prod_replicate, hj]
  simp

theorem involutionIff (j : Nat) (hj : Fintype.card α = 2*j) (p : Equiv.Perm α) :
    p.cycleType = Multiset.replicate j 2 ↔ p ^ 2 = 1 ∧ ∀ x, p x ≠ x := by
  have hall : (∀ x, p x ≠ x) ↔ p.support = univ := by
    constructor
    · intro h
      ext x
      simp [Equiv.Perm.mem_support, h]
    · intro h x
      have hm : x ∈ p.support := by rw [h]; exact mem_univ x
      simpa [Equiv.Perm.mem_support] using hm
  have hnum (hs : p.support = univ) (hc : p.cycleType = Multiset.replicate p.cycleType.card 2) :
      p.cycleType.card = j := by
    have ht := p.sum_cycleType
    have he : p.cycleType.sum = p.cycleType.card * 2 := by
      conv_lhs => rw [hc]
      simp
    rw [he, hs, card_univ, hj] at ht
    omega
  constructor
  · intro h
    refine ⟨Equiv.Perm.pow_prime_eq_one_iff.mpr ?_, hall.mpr ?_⟩
    · rw [h]
      exact fun c hc => Multiset.eq_of_mem_replicate hc
    · have ht := p.sum_cycleType
      rw [h, Multiset.sum_replicate] at ht
      apply eq_univ_of_card
      simp at ht
      omega
  · rintro ⟨hp, hfix⟩
    have hc := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
    rw [← hnum (hall.mp hfix) hc]
    exact hc

theorem countFixedFreeInvolutions (j : Nat) (hj : Fintype.card α = 2*j) :
    (univ.filter (fun p : Equiv.Perm α => p ^ 2 = 1 ∧ ∀ x, p x ≠ x)).card =
      (2*j).factorial / (2^j*j.factorial) := by
  convert transpositionType j hj using 2
  ext p
  simp only [mem_filter, mem_univ, true_and]
  exact (involutionIff j hj p).symm
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Involution

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Equiv
variable {α : Type*} [DecidableEq α] [Fintype α]
abbrev Rows (α : Type*) := Finset (Finset α)

def Perfect (M : Rows α) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧
  (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
  ∀ a, ∃ e ∈ M, a ∈ e

def PairRel (M : Rows α) (a b : α) : Prop := a ≠ b ∧ {a,b} ∈ M

theorem pairRelUnique {M : Rows α} (h : Perfect M) (a : α) :
    ∃! b, PairRel M a b := by
  obtain ⟨e, he, ha⟩ := h.2.2 a
  obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp (h.1 e he)
  simp only [mem_insert, mem_singleton] at ha
  have uni {b c : α} (hb : PairRel M a b) (hc : PairRel M a c) : b = c := by
    have heq : ({a,b} : Finset α) = {a,c} := by
      by_contra hn
      exact (disjoint_left.mp (h.2.1 _ hb.2 _ hc.2 hn)) (mem_insert_self a _) (mem_insert_self a _)
    have hm : b ∈ ({a,c} : Finset α) := heq ▸ mem_insert_of_mem (mem_singleton_self b)
    exact ((mem_insert.mp hm).resolve_left hb.1.symm) |> mem_singleton.mp
  rcases ha with hau | hav
  · subst a
    exact ⟨v, ⟨huv, he⟩, fun _ hy => uni hy ⟨huv, he⟩⟩
  · subst a
    have he' : ({v,u} : Finset α) ∈ M := by rwa [pair_comm]
    exact ⟨u, ⟨huv.symm, he'⟩, fun _ hy => uni hy ⟨huv.symm, he'⟩⟩

theorem pairRelSymm {M : Rows α} {a b : α} (h : PairRel M a b) :
    PairRel M b a := ⟨h.1.symm, by rw [pair_comm]; exact h.2⟩

noncomputable def partner {M : Rows α} (h : Perfect M) (a : α) : α :=
  Classical.choose (pairRelUnique h a)

theorem partnerPair {M : Rows α} (h : Perfect M) (a : α) :
    PairRel M a (partner h a) := (Classical.choose_spec (pairRelUnique h a)).1

theorem partnerOfPair {M : Rows α} (h : Perfect M) {a b : α} (hb : PairRel M a b) :
    b = partner h a := (Classical.choose_spec (pairRelUnique h a)).2 b hb

theorem partnerInvolutive {M : Rows α} (h : Perfect M) :
    Function.Involutive (partner h) :=
  fun a => (partnerOfPair h (pairRelSymm (partnerPair h a))).symm

noncomputable def partnerPerm {M : Rows α} (h : Perfect M) : Equiv.Perm α :=
  ⟨partner h, partner h, partnerInvolutive h, partnerInvolutive h⟩

theorem permOfPerfect {M : Rows α} (h : Perfect M) :
    partnerPerm h ^ 2 = 1 ∧ ∀ x, partnerPerm h x ≠ x := by
  constructor
  · ext x
    exact partnerInvolutive h x
  · exact fun x => (partnerPair h x).1.symm

def orbitPairs (p : Equiv.Perm α) : Rows α := univ.image (fun a => {a, p a})

theorem perfectOfPerm {p : Equiv.Perm α} (hp : p ^ 2 = 1 ∧ ∀ x, p x ≠ x) :
    Perfect (orbitPairs p) := by
  have hinv (a : α) : p (p a) = a := by
    simpa [pow_two] using DFunLike.congr_fun hp.1 a
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    exact card_pair (hp.2 a).symm
  · intro e he f hf hne
    obtain ⟨a, _, rfl⟩ := mem_image.mp he
    obtain ⟨b, _, rfl⟩ := mem_image.mp hf
    refine disjoint_left.mpr ?_
    intro x hx hy
    have hex (y : α) (hy : x ∈ ({y,p y} : Finset α)) : ({x,p x} : Finset α) = {y,p y} := by
      rcases mem_insert.mp hy with rfl | hy
      · rfl
      · obtain rfl := mem_singleton.mp hy
        rw [hinv, pair_comm]
    exact hne ((hex a hx).symm.trans (hex b hy))
  · intro a
    exact ⟨{a,p a}, mem_image.mpr ⟨a, mem_univ _, rfl⟩, mem_insert_self _ _⟩

noncomputable def pairingEquiv :
    {M : Rows α // Perfect M} ≃ {p : Equiv.Perm α // p ^ 2 = 1 ∧ ∀ x, p x ≠ x} where
  toFun m := ⟨partnerPerm m.2, permOfPerfect m.2⟩
  invFun p := ⟨orbitPairs p.1, perfectOfPerm p.2⟩
  left_inv m := by
    apply Subtype.ext
    change orbitPairs (partnerPerm m.2) = m.1
    ext e
    constructor
    · intro he
      obtain ⟨a, _, rfl⟩ := mem_image.mp he
      exact (partnerPair m.2 a).2
    · intro he
      obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (m.2.1 e he)
      refine mem_image.mpr ⟨a, mem_univ _, ?_⟩
      change ({a, partner m.2 a} : Finset α) = {a,b}
      rw [← partnerOfPair m.2 (show PairRel m.1 a b from ⟨hab, he⟩)]
  right_inv p := by
    apply Subtype.ext
    ext a
    exact (partnerOfPair (perfectOfPerm p.2)
      (show PairRel (orbitPairs p.1) a (p.1 a)
       from ⟨(p.2.2 a).symm, mem_image.mpr ⟨a, mem_univ _, rfl⟩⟩)).symm

theorem countPerfect (j : Nat) (h : Fintype.card α = 2*j) :
    Nat.card {M : Rows α // Perfect M} = (2*j).factorial / (2^j*j.factorial) := by
  classical
  rw [Nat.card_congr pairingEquiv, ← PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Involution.countFixedFreeInvolutions j h]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype _ (fun p => by simp)
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Equiv

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence (Rows Nodes graph)
variable {α : Type*} [DecidableEq α]
variable {U : Finset α} {H : Rows α}

def Selection (U : Finset α) (H : Rows α) :=
  {q : H → Finset α //
    (∀ R, (q R).card = 2 ∧ q R ⊆ R.val ∧ q R ⊆ U) ∧
    ∀ R S, R ≠ S → Disjoint (q R) (q S)}

def directed (q : Selection U H) : Nodes U H → Nodes U H → Prop
  | .inr R, .inl a => a.val ∈ q.val R
  | .inl a, .inr R => a.val ∈ R.val ∧ a.val ∉ q.val R
  | _, _ => False

theorem directedAdj (q : Selection U H) (u v : Nodes U H)
    (hd : directed q u v) : (graph U H).Adj u v := by
  cases u with
  | inl u =>
    cases v with
    | inl v => exact hd
    | inr v => exact hd.1
  | inr u =>
    cases v with
    | inl v => exact (q.2.1 u).2.1 hd
    | inr v => exact hd

theorem directedEdge (q : Selection U H) (u v : Nodes U H)
    (ha : (graph U H).Adj u v) : directed q u v ↔ ¬ directed q v u := by
  cases u <;> cases v <;> first | exact ha.elim | simp_all [directed, graph]

theorem directedIncomingVertex (q : Selection U H) (a : U) :
    (∀ R S : H, a.val ∈ q.val R → a.val ∈ q.val S → R = S) := by
  intro R S hr hs
  by_contra hne
  exact (Finset.disjoint_left.mp (q.2.2 R S hne)) hr hs

theorem uncoveredCard (q : Selection U H) :
    (U \ (H.attach.biUnion q.val)).card = U.card - 2*H.card := by
  classical
  have hsub : H.attach.biUnion q.val ⊆ U := by
    intro a ha
    obtain ⟨R,_,ha⟩ := mem_biUnion.mp ha
    exact (q.2.1 R).2.2 ha
  have hdis : (H.attach : Set H).PairwiseDisjoint q.val := by
    intro R _ S _ hne
    exact q.2.2 R S hne
  have hcov : (H.attach.biUnion q.val).card = 2*H.card := by
    rw [Finset.card_biUnion hdis]
    calc
      _ = ∑ _R ∈ H.attach, (2:Nat) := sum_congr rfl (fun R _ => (q.2.1 R).1)
      _ = 2*H.card := by simp [Nat.mul_comm]
  rw [card_sdiff_of_subset hsub,hcov]

open Classical in
noncomputable def selectedRow (O : Nodes U H → Nodes U H → Prop) (R : H) : Finset α :=
  R.val.filter (fun a => ∃ ha : a ∈ U, O (.inr R) (.inl ⟨a,ha⟩))

theorem selectedMem (O : Nodes U H → Nodes U H → Prop)
    (hadj : ∀ u v, O u v → (graph U H).Adj u v) (R : H) (a : U) :
    a.val ∈ selectedRow O R ↔ O (.inr R) (.inl a) := by
  classical
  change (_ ∈ Finset.filter _ _) ↔ _
  refine ⟨fun hm => ?_, fun ho => mem_filter.mpr ⟨hadj _ _ ho, a.2, ho⟩⟩
  obtain ⟨_,_,h⟩ := mem_filter.mp hm
  exact h

theorem selectedSub (O : Nodes U H → Nodes U H → Prop) (R : H) :
    selectedRow O R ⊆ R.val ∧ selectedRow O R ⊆ U := by
  classical
  constructor
  · exact filter_subset _ _
  · intro a ha
    exact (mem_filter.mp ha).2.choose

theorem selectedDisjoint (O : Nodes U H → Nodes U H → Prop)
    (hadj : ∀ u v, O u v → (graph U H).Adj u v)
    (hatmost : ∀ a : U, ∀ R S : H, O (.inr R) (.inl a) → O (.inr S) (.inl a) → R = S)
    (R S : H) (hn : R ≠ S) : Disjoint (selectedRow O R) (selectedRow O S) := by
  refine disjoint_left.mpr ?_
  intro a ha hb
  let v : U := ⟨a, (selectedSub O R).2 ha⟩
  exact hn (hatmost v R S ((selectedMem O hadj R v).mp ha) ((selectedMem O hadj S v).mp hb))

theorem selectedOfDirected (q : Selection U H) (R : H) :
    selectedRow (directed q) R = q.val R := by
  classical
  ext a
  constructor
  · intro h
    obtain ⟨_,ha,ho⟩ := mem_filter.mp h
    exact ho
  · intro ha
    exact mem_filter.mpr ⟨(q.2.1 R).2.1 ha, (q.2.1 R).2.2 ha, ha⟩

def Oriented (O : Nodes U H → Nodes U H → Prop) : Prop :=
  (∀ u v, O u v → (graph U H).Adj u v) ∧
  (∀ u v, (graph U H).Adj u v → (O u v ↔ ¬ O v u))

def Incoming (O : Nodes U H → Nodes U H → Prop) (r : Option (Nodes U H)) : Prop :=
  ∀ v, if some v = r then (∀ u, ¬ O u v) else ∃! u, O u v

theorem directedOriented (q : Selection U H) : Oriented (directed q) :=
  ⟨directedAdj q, directedEdge q⟩

theorem selectedCompl (hU : ∀ R : H, R.val ⊆ U)
    (O : Nodes U H → Nodes U H → Prop) (ho : Oriented O) (R : H) (a : α) :
    a ∈ R.val \ selectedRow O R ↔ ∃ ha : a ∈ U, O (.inl ⟨a,ha⟩) (.inr R) := by
  classical
  rw [mem_sdiff]
  constructor
  · rintro ⟨haR, hn⟩
    let v : U := ⟨a,hU R haR⟩
    exact ⟨v.2, (ho.2 (.inl v) (.inr R) haR).mpr (fun h => hn ((selectedMem O ho.1 R v).mpr h))⟩
  · rintro ⟨haU, h⟩
    let v : U := ⟨a,haU⟩
    have haR : a ∈ R.val := ho.1 _ _ h
    exact ⟨haR, fun hs => (ho.2 (.inl v) (.inr R) haR).mp h ((selectedMem O ho.1 R v).mp hs)⟩

theorem selectedCard (hU : ∀ R : H, R.val ⊆ U)
    (O : Nodes U H → Nodes U H → Prop) (ho : Oriented O) (r : Option (Nodes U H))
    (hi : Incoming O r) (R : H)
    (hc : R.val.card = if some (.inr R) = r then 2 else 3) :
    (selectedRow O R).card = 2 := by
  classical
  have h := hi (.inr R)
  have hs := card_sdiff_add_card_eq_card (selectedSub O R).1
  split_ifs at h hc with hr
  · have h0 : R.val \ selectedRow O R = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨_, hh⟩ := (selectedCompl hU O ho R a).mp ha
      exact h _ hh
    rw [h0, card_empty, hc] at hs
    omega
  · obtain ⟨node, hin, hun⟩ := h
    cases node with
    | inr S => exact False.elim (ho.1 _ _ hin)
    | inl a =>
      have h1 : R.val \ selectedRow O R = {a.val} := by
        ext b
        rw [selectedCompl hU O ho, mem_singleton]
        constructor
        · rintro ⟨hb,hbO⟩
          have he := hun _ hbO
          exact congrArg Subtype.val (Sum.inl.inj he)
        · rintro rfl
          exact ⟨a.2,hin⟩
      rw [h1, card_singleton, hc] at hs
      omega

noncomputable def fromOriented (hU : ∀ R : H, R.val ⊆ U)
    (O : Nodes U H → Nodes U H → Prop) (ho : Oriented O) (r : Option (Nodes U H))
    (hi : Incoming O r) (hc : ∀ R : H, R.val.card = if some (.inr R) = r then 2 else 3) :
    Selection U H := by
  classical
  refine ⟨selectedRow O, ⟨fun R => ⟨selectedCard hU O ho r hi R (hc R), selectedSub O R⟩, ?_⟩⟩
  apply selectedDisjoint O ho.1
  intro a R S hR hS
  have h := hi (.inl a)
  split_ifs at h with he
  · exact (h _ hR).elim
  · obtain ⟨p,_,hp⟩ := h
    exact Sum.inr.inj ((hp _ hR).trans (hp _ hS).symm)

theorem directedFrom (hU : ∀ R : H, R.val ⊆ U)
    (O : Nodes U H → Nodes U H → Prop) (ho : Oriented O) (r : Option (Nodes U H))
    (hi : Incoming O r) (hc : ∀ R : H, R.val.card = if some (.inr R) = r then 2 else 3) :
    directed (fromOriented hU O ho r hi hc) = O := by
  classical
  funext u v
  apply propext
  cases u with
  | inl a =>
    cases v with
    | inl b =>
      exact ⟨False.elim, fun h => ho.1 _ _ h⟩
    | inr S =>
      change (a.val ∈ S.val ∧ a.val ∉ selectedRow O S) ↔ _
      rw [selectedMem O ho.1]
      exact ⟨fun ⟨ha,hn⟩ => (ho.2 (.inl a) (.inr S) ha).mpr hn, fun h => ⟨ho.1 _ _ h,
        (ho.2 (.inl a) (.inr S) (ho.1 _ _ h)).mp h⟩⟩
  | inr R =>
    cases v with
    | inl a => exact selectedMem O ho.1 R a
    | inr S => exact ⟨False.elim, fun h => ho.1 _ _ h⟩

theorem directedInjective : Function.Injective (directed (U := U) (H := H)) := by
  intro a b hab
  apply Subtype.ext
  funext R
  rw [← selectedOfDirected a R, ← selectedOfDirected b R, hab]

def vacant (q : Selection U H) : Finset α := U \ H.attach.biUnion q.val

theorem vacantMem (q : Selection U H) (a : U) :
    a.val ∈ vacant q ↔ ∀ u, ¬ directed q u (.inl a) := by
  classical
  simp only [vacant, mem_sdiff, a.2, true_and, mem_biUnion, mem_attach, true_and]
  constructor
  · intro h u hO
    cases u with
    | inl b => exact hO
    | inr R => exact h ⟨R,hO⟩
  · rintro h ⟨R,hR⟩
    exact h (.inr R) hR

theorem directedIncoming (hu : ∀ R : H, R.val ⊆ U) (q : Selection U H) (r : Option (Nodes U H))
    (hc : ∀ R : H, R.val.card = if some (.inr R) = r then 2 else 3)
    (hv : ∀ a : U, a.val ∈ vacant q ↔ some (.inl a) = r) :
    Incoming (directed q) r := by
  classical
  intro node
  cases node with
  | inl a =>
    split_ifs with he
    · exact (vacantMem q a).mp ((hv a).mpr he)
    · have hn := fun ha => he ((hv a).mp ha)
      have hu : a.val ∈ H.attach.biUnion q.val := by
        by_contra h
        exact hn (mem_sdiff.mpr ⟨a.2,h⟩)
      obtain ⟨R,_,hR⟩ := mem_biUnion.mp hu
      refine ⟨.inr R, hR, ?_⟩
      intro w hw
      cases w with
      | inl w => exact False.elim hw
      | inr w => exact congrArg Sum.inr (directedIncomingVertex q a w R hw hR)
  | inr R =>
    have hcard := card_sdiff_add_card_eq_card (q.2.1 R).2.1
    rw [(q.2.1 R).1, hc R] at hcard
    split_ifs at hcard ⊢ with hr
    · intro w ho
      cases w with
      | inr S => exact ho
      | inl a =>
        have hm : a.val ∈ R.val \ q.val R := mem_sdiff.mpr ho
        have h0 : (R.val \ q.val R).card = 0 := by omega
        rw [Finset.card_eq_zero.mp h0] at hm
        exact notMem_empty _ hm
    · have h1 : (R.val \ q.val R).card = 1 := by omega
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp h1
      have hs : a ∈ R.val \ q.val R := by rw [ha]; exact mem_singleton_self a
      have haU : a ∈ U := hu R (mem_sdiff.mp hs).1
      refine ⟨.inl ⟨a,haU⟩, mem_sdiff.mp hs, ?_⟩
      intro w hw
      cases w with
      | inr S => exact False.elim hw
      | inl b =>
        have hb : b.val ∈ R.val \ q.val R := mem_sdiff.mpr hw
        rw [ha] at hb
        exact congrArg Sum.inl (Subtype.ext (mem_singleton.mp hb))
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Counts
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence (Rows Nodes graph)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Orientation
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903PlusEdge

variable {α : Type*} [DecidableEq α]
variable {U : Finset α} {H : Rows α}

theorem toIncomingTree {r : Nodes U H} {O : Nodes U H → Nodes U H → Prop}
    (h : Outward (graph U H) r O) : Oriented O ∧ Incoming O (some r) := by
  classical
  refine ⟨⟨h.1,h.2.1⟩,fun v => ?_⟩
  by_cases he : v = r
  · subst v
    simpa using h.2.2.1
  · simpa [he] using h.2.2.2 _ he

theorem ofIncomingTree {r : Nodes U H} {O : Nodes U H → Nodes U H → Prop}
    (ho : Oriented O) (hi : Incoming O (some r)) : Outward (graph U H) r O := by
  classical
  exact ⟨ho.1,ho.2,by simpa using hi r,fun v hv => by simpa [hv] using hi v⟩

theorem toIncomingCycle {O : Nodes U H → Nodes U H → Prop}
    (h : AllIncoming (graph U H) O) : Oriented O ∧ Incoming O none := by
  exact ⟨⟨h.1,h.2.1⟩,fun v => by simpa using h.2.2 v⟩

theorem ofIncomingCycle {O : Nodes U H → Nodes U H → Prop}
    (ho : Oriented O) (hi : Incoming O none) : AllIncoming (graph U H) O :=
  ⟨ho.1, ho.2, fun v => by simpa using hi v⟩

theorem freeRootUnique (hs : U.card = 2 * H.card + 1) (q : Selection U H) :
    ∃! a : U, vacant q = {a.val} := by
  classical
  have hu := uncoveredCard q
  change (vacant q).card = U.card - 2*H.card at hu
  have hc : (vacant q).card = 1 := by omega
  obtain ⟨a,ha⟩ := card_eq_one.mp hc
  have hm : a ∈ vacant q := by rw [ha]; exact mem_singleton_self a
  exact ⟨⟨a,(mem_sdiff.mp hm).1⟩,ha,fun b hb => Subtype.ext
    (Finset.singleton_inj.mp (hb.symm.trans ha))⟩

theorem emptyVacant (hs : U.card = 2 * H.card) (q : Selection U H) : vacant q = ∅ := by
  apply card_eq_zero.mp
  have hu := uncoveredCard q
  change (vacant q).card = U.card - 2*H.card at hu
  omega

noncomputable def freeEquiv (hU : ∀ R : H, R.val ⊆ U) (ht : (graph U H).IsTree)
    (hs : U.card = 2 * H.card + 1) (hr : ∀ R : H, R.val.card = 3) :
    Selection U H ≃ U := by
  classical
  let hc (a : U) (R : H) : R.val.card = if some (.inr R : Nodes U H) = some (.inl a) then 2 else 3 := by
    simpa using hr R
  let choice (a : U) := Closer (graph U H) (.inl a)
  let h (a : U) := toIncomingTree (closerOutward ht (.inl a))
  let build (a : U) := fromOriented hU (choice a) (h a).1 (some (.inl a)) (h a).2 (hc a)
  have hbuild (a : U) : directed (build a) = choice a :=
    directedFrom hU _ (h a).1 _ (h a).2 (hc a)
  refine ⟨fun q => Classical.choose (freeRootUnique hs q),build,?_,?_⟩
  · intro q
    let a := Classical.choose (freeRootUnique hs q)
    have hv : vacant q = {a.val} := (Classical.choose_spec (freeRootUnique hs q)).1
    have hq := directedIncoming hU q (some (.inl a)) (hc a) (fun b => by
      rw [hv,mem_singleton]
      simp only [Option.some.injEq, Sum.inl.injEq]
      exact Subtype.ext_iff.symm)
    apply directedInjective
    exact (hbuild a).trans (orientationUnique ht _ (ofIncomingTree (directedOriented q) hq)).symm
  · intro a
    symm
    apply (Classical.choose_spec (freeRootUnique hs (build a))).2
    ext b
    constructor
    · intro hb
      have hbU := (mem_sdiff.mp hb).1
      let v : U := ⟨b,hbU⟩
      have hn := (vacantMem (build a) v).mp hb
      rw [hbuild a] at hn
      by_contra hb'
      have hv : v ≠ a := fun he => hb' (mem_singleton.mpr (congrArg Subtype.val he))
      obtain ⟨w,hw,_⟩ := (closerOutward ht (.inl a)).2.2.2 (.inl v) (fun he => hv (Sum.inl.inj he))
      exact hn w hw
    · intro hb
      have hb' : b = a.val := mem_singleton.mp hb
      subst b
      apply (vacantMem (build a) a).mpr
      rw [hbuild a]
      exact (closerOutward ht (.inl a)).2.2.1

theorem countSingle (hU : ∀ R : H, R.val ⊆ U) (ht : (graph U H).IsTree)
    (hs : U.card = 2 * H.card) (r : H)
    (hr : ∀ R : H, R.val.card = if R = r then 2 else 3) :
    Nat.card (Selection U H) = 1 := by
  classical
  let rr : Nodes U H := .inr r
  have hc (R : H) : R.val.card = if some (.inr R) = some rr then 2 else 3 := by
    simpa [rr] using hr R
  let ch := Closer (graph U H) rr
  have ho := toIncomingTree (closerOutward ht rr)
  let build := fromOriented hU ch ho.1 (some rr) ho.2 hc
  have hdir : directed build = ch := directedFrom hU ch ho.1 (some rr) ho.2 hc
  have uniq (q : Selection U H) : q = build := by
    apply directedInjective
    rw [hdir]
    apply orientationUnique ht rr
    refine ofIncomingTree (directedOriented q) (directedIncoming hU q _ hc ?_)
    intro a
    simp [emptyVacant hs q,rr]
  letI : Unique (Selection U H) := ⟨⟨build⟩,uniq⟩
  first | exact Nat.card_unique | simp [Nat.card_eq_fintype_card]

theorem countCycle (hU : ∀ R : H, R.val ⊆ U) (ht : (graph U H).Connected)
    (he : Nat.card (graph U H).edgeSet = Nat.card (Nodes U H))
    (hs : U.card = 2 * H.card) (hr : ∀ R : H, R.val.card = 3) :
    Nat.card (Selection U H) = 2 := by
  classical
  have hc (R : H) : R.val.card = if some (.inr R : Nodes U H) = none then 2 else 3 := by
    simpa using hr R
  obtain ⟨O,P,hn,ho,hp,hall⟩ := connectedExactlyTwo ht he
  let a := fromOriented hU O (toIncomingCycle ho).1 none (toIncomingCycle ho).2 hc
  let b := fromOriented hU P (toIncomingCycle hp).1 none (toIncomingCycle hp).2 hc
  have ha : directed a = O := directedFrom hU _ _ _ _ _
  have hb : directed b = P := directedFrom hU _ _ _ _ _
  have hab : a ≠ b := fun h => hn (ha.symm.trans ((congrArg directed h).trans hb))
  have hq (q : Selection U H) : q = a ∨ q = b := by
    have hd := directedIncoming hU q none hc (fun v => by simp [emptyVacant hs q])
    rcases hall _ (ofIncomingCycle (directedOriented q) hd) with h | h
    · exact Or.inl (directedInjective (h.trans ha.symm))
    · exact Or.inr (directedInjective (h.trans hb.symm))
  let f : Bool → Selection U H := fun x => if x then a else b
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      cases x <;> cases y <;> simp_all [f,hab,Ne.symm hab]
    · intro q
      rcases hq q with rfl | rfl
      · exact ⟨true,rfl⟩
      · exact ⟨false,rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  first | exact Nat.card_unique | simp [Nat.card_eq_fintype_card]
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Counts

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Split
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903 (Rows Covers Linear uniqueHitter)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection
variable {α : Type*} [DecidableEq α]
variable {U : Finset α} {H : Rows α}

def Matching (A : Finset α) (N : Rows α) (j : Nat) :=
  (∀ e ∈ N, ∀ f ∈ N, e ≠ f → Disjoint e f) ∧
  (∀ e ∈ N, e.card = 2 ∧ e ⊆ A) ∧ N.card = j

noncomputable def pick {M : Rows α} {s : Nat} (h : Covers U H M s) (R : H) : Finset α :=
  Classical.choose (h.2.2.1 R.val R.2)

theorem pickSpec {M : Rows α} {s : Nat} (h : Covers U H M s) (R : H) :
    pick h R ∈ M ∧ pick h R ⊆ R.val := Classical.choose_spec (h.2.2.1 R.val R.2)

theorem distinctPicks {M : Rows α} {s : Nat} (lin : Linear H) (h : Covers U H M s) :
    Function.Injective (pick h) := by
  intro R S he
  by_contra hn
  have hne : R.val ≠ S.val := fun he' => hn (Subtype.ext he')
  have hu : pick h R ⊆ R.val ∩ S.val := by
    intro a ha
    exact mem_inter.mpr ⟨(pickSpec h R).2 ha, (pickSpec h S).2 (he ▸ ha)⟩
  have h2 := card_le_card hu
  have hle := lin R.val R.2 S.val S.2 hne
  rw [(h.2.1 _ (pickSpec h R).1).1] at h2
  omega

noncomputable def extract {M : Rows α} {s : Nat} (lin : Linear H) (h : Covers U H M s) :
    Selection U H :=
  ⟨pick h, ⟨fun R => ⟨(h.2.1 _ (pickSpec h R).1).1, (pickSpec h R).2,
    (h.2.1 _ (pickSpec h R).1).2⟩,
    fun R S hne => h.1 _ (pickSpec h R).1 _ (pickSpec h S).1
      (fun he => hne (distinctPicks lin h he))⟩⟩

def reserved (q : Selection U H) : Rows α := H.attach.image q.val

theorem reservedCard (q : Selection U H) : (reserved q).card = H.card := by
  have hi : Function.Injective q.val := by
    intro R S he
    by_contra hn
    have h := q.2.2 R S hn
    rw [he,disjoint_self] at h
    have hc := (q.2.1 S).1
    simpa [h] using hc
  simp [reserved,card_image_of_injective _ hi]

theorem reservedExtract {M : Rows α} {s : Nat} (lin : Linear H) (h : Covers U H M s) :
    reserved (extract lin h) ⊆ M := by
  intro e he
  obtain ⟨R,_,rfl⟩ := mem_image.mp he
  exact (pickSpec h R).1

theorem residualMatching {M : Rows α} {s : Nat} (lin : Linear H) (h : Covers U H M s) :
    Matching (vacant (extract lin h)) (M \ reserved (extract lin h)) (s-H.card) := by
  classical
  let q := extract lin h
  refine ⟨fun e he f hf hn => h.1 e (mem_sdiff.mp he).1 f (mem_sdiff.mp hf).1 hn, ?_, ?_⟩
  · intro e he
    obtain ⟨he,hne⟩ := mem_sdiff.mp he
    refine ⟨(h.2.1 _ he).1, ?_⟩
    intro a ha
    refine mem_sdiff.mpr ⟨(h.2.1 e he).2 ha, ?_⟩
    intro hae
    obtain ⟨R,_,hR⟩ := mem_biUnion.mp hae
    have hRmem : q.val R ∈ reserved q := mem_image.mpr ⟨R, mem_attach _ _,rfl⟩
    have hdiff : e ≠ q.val R := fun heq => hne (heq.symm ▸ hRmem)
    exact (disjoint_left.mp (h.1 e he _ (pickSpec h R).1 hdiff)) ha hR
  · rw [card_sdiff_of_subset (reservedExtract lin h),reservedCard,h.2.2.2]

theorem crossDisjoint (q : Selection U H) {N : Rows α} {j : Nat}
    (h : Matching (vacant q) N j) {e f : Finset α}
    (he : e ∈ reserved q) (hf : f ∈ N) : Disjoint e f := by
  obtain ⟨R,_,rfl⟩ := mem_image.mp he
  refine disjoint_left.mpr ?_
  intro a ha hb
  have hv := (h.2.1 f hf).2 hb
  exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨R,mem_attach _ _,ha⟩)

theorem reservedResidualDisj (q : Selection U H) {N : Rows α} {j : Nat}
    (h : Matching (vacant q) N j) : Disjoint (reserved q) N := by
  refine disjoint_left.mpr ?_
  intro e he hf
  have hc := crossDisjoint q h he hf
  rw [disjoint_self] at hc
  have htwo := (h.2.1 e hf).1
  simpa [hc] using htwo

theorem joinCover (q : Selection U H) {N : Rows α} {j s : Nat}
    (h : Matching (vacant q) N j) (hs : H.card + j = s) :
    Covers U H (reserved q ∪ N) s := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he f hf hn
    rcases mem_union.mp he with he | he <;> rcases mem_union.mp hf with hf | hf
    · obtain ⟨R,_,rfl⟩ := mem_image.mp he
      obtain ⟨S,_,rfl⟩ := mem_image.mp hf
      exact q.2.2 R S (fun he => hn (congrArg q.val he))
    · exact crossDisjoint q h he hf
    · exact (crossDisjoint q h hf he).symm
    · exact h.1 e he f hf hn
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨R,_,rfl⟩ := mem_image.mp he
      exact ⟨(q.2.1 R).1, (q.2.1 R).2.2⟩
    · exact ⟨(h.2.1 e he).1, (h.2.1 e he).2.trans sdiff_subset⟩
  · intro R hR
    exact ⟨q.val ⟨R,hR⟩, mem_union_left _ (mem_image.mpr ⟨⟨R,hR⟩,mem_attach _ _,rfl⟩),
      (q.2.1 ⟨R,hR⟩).2.1⟩
  · rw [card_union_of_disjoint (reservedResidualDisj q h), reservedCard,h.2.2,hs]

theorem extractJoin (lin : Linear H) (hr : ∀ R ∈ H, R.card ≤ 3)
    (q : Selection U H) {N : Rows α} {j s : Nat}
    (h : Matching (vacant q) N j) (hs : H.card + j = s) :
    extract lin (joinCover q h hs) = q := by
  apply Subtype.ext
  funext R
  let hM := joinCover q h hs
  obtain ⟨a,_,ha⟩ := uniqueHitter hM R.2 (hr R.val R.2)
  have hp : q.val R ∈ reserved q := mem_image.mpr ⟨R,mem_attach _ _,rfl⟩
  exact (ha _ (pickSpec hM R)).trans
    (ha _ ⟨mem_union_left _ hp,(q.2.1 R).2.1⟩).symm

theorem sigmaExtVal {j : Nat} {q q' : Selection U H}
    {a : {N : Rows α // Matching (vacant q) N j}}
    {b : {N : Rows α // Matching (vacant q') N j}}
    (h : q = q') (hv : a.val = b.val) :
    (⟨q,a⟩ : Σ q : Selection U H, {N : Rows α // Matching (vacant q) N j}) = ⟨q',b⟩ := by
  subst q'
  rw [show a = b from Subtype.ext hv]

noncomputable def splitEquiv (lin : Linear H) (hr : ∀ R ∈ H, R.card ≤ 3)
    (s : Nat) (hs : H.card ≤ s) :
    {M : Rows α // Covers U H M s} ≃
      (Σ q : Selection U H, {N : Rows α // Matching (vacant q) N (s-H.card)}) where
  toFun m := ⟨extract lin m.2,⟨m.val \ reserved (extract lin m.2),residualMatching lin m.2⟩⟩
  invFun p := ⟨reserved p.1 ∪ p.2.val,joinCover p.1 p.2.2 (by omega)⟩
  left_inv m := by
    apply Subtype.ext
    change reserved (extract lin m.2) ∪ (m.val \ reserved (extract lin m.2)) = m.val
    exact union_sdiff_of_subset (reservedExtract lin m.2)
  right_inv p := by
    let he := extractJoin lin hr p.1 p.2.2 (show H.card + (s-H.card) = s by omega)
    refine sigmaExtVal he ?_
    change (reserved p.1 ∪ p.2.val) \ reserved (extract lin (joinCover p.1 p.2.2 (show H.card + (s-H.card) = s by omega))) = p.2.val
    have hv : (reserved p.1 ∪ p.2.val) \ reserved p.1 = p.2.val := by
      exact union_sdiff_cancel_left (reservedResidualDisj p.1 p.2.2)
    rw [show extract lin (joinCover p.1 p.2.2 (show H.card + (s-H.card) = s by omega)) = p.1 from he]
    exact hv
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Split

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Global
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Connectivity (edges connected)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Counts
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence (graph)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {U : Finset α} {H : Rows α}

noncomputable def parts (U : Finset α) (H : Rows α) : Rows α := U.image (component H)

theorem partSub (hU : ∀ R ∈ H, R ⊆ U) (c : parts U H) : c.val ⊆ U := by
  obtain ⟨v,hv,he⟩ := mem_image.mp c.2
  rw [← he]
  exact componentIn hU hv

theorem partDisjoint (c d : parts U H) (hne : c ≠ d) : Disjoint c.val d.val :=
  partsDisjoint H U c.val c.2 d.val d.2 (fun h => hne (Subtype.ext h))

theorem rowPart (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) (R : H) :
    ∃! c : parts U H, R.val ⊆ c.val := by
  obtain ⟨a,ha⟩ := hne R.val R.2
  have haU := hU R.val R.2 ha
  let c : parts U H := ⟨component H a,mem_image.mpr ⟨a,haU,rfl⟩⟩
  have hRc : R.val ⊆ c.val :=
    componentClosed H a R.val R.2 (not_disjoint_iff.mpr ⟨a,ha,selfMem H a⟩)
  refine ⟨c,hRc,fun d hd => ?_⟩
  by_contra hn
  exact (disjoint_left.mp (partDisjoint d c hn)) (hd ha) (hRc ha)

noncomputable def atPart (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) (R : H) :
    parts U H := Classical.choose (rowPart hU hne R)

theorem atPartSub (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) (R : H) :
    R.val ⊆ (atPart hU hne R).val :=
  (Classical.choose_spec (rowPart hU hne R)).1

theorem atPartEq (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) (R : H)
    (c : parts U H) (hc : R.val ⊆ c.val) : c = atPart hU hne R :=
  (Classical.choose_spec (rowPart hU hne R)).2 c hc

theorem edgeMem {c : Finset α} {R : Finset α} : R ∈ edges c H ↔ R ∈ H ∧ R ⊆ c := by
  classical
  exact mem_filter

def toGlobal (c : parts U H) (R : edges c.val H) : H := ⟨R.val,(edgeMem.mp R.2).1⟩

noncomputable def atLocal (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) (R : H) :
    edges (atPart hU hne R).val H :=
  ⟨R.val,edgeMem.mpr ⟨R.2,atPartSub hU hne R⟩⟩

theorem sigmaRowsExt {c d : parts U H} {R : edges c.val H} {S : edges d.val H}
    (h : c = d) (hv : R.val = S.val) :
    (⟨c,R⟩ : Σ c : parts U H, edges c.val H) = ⟨d,S⟩ := by
  subst d
  rw [show R = S from Subtype.ext hv]

theorem dependentSelectionEq
    (q : ∀ c : parts U H, Selection c.val (edges c.val H))
    {c d : parts U H} {R : edges c.val H} {S : edges d.val H}
    (h : c = d) (hv : R.val = S.val) : (q c).val R = (q d).val S := by
  subst d
  rw [show R = S from Subtype.ext hv]

noncomputable def rowsEquiv (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) :
    H ≃ (Σ c : parts U H, edges c.val H) where
  toFun R := ⟨atPart hU hne R, atLocal hU hne R⟩
  invFun p := toGlobal p.1 p.2
  left_inv _ := rfl
  right_inv p := by
    have he : atPart hU hne (toGlobal p.1 p.2) = p.1 :=
      (atPartEq hU hne (toGlobal p.1 p.2) _ (edgeMem.mp p.2.2).2).symm
    exact sigmaRowsExt he rfl

def restrict (q : Selection U H) (c : parts U H) : Selection c.val (edges c.val H) :=
  ⟨fun R => q.val (toGlobal c R),⟨fun R => ⟨(q.2.1 _).1,(q.2.1 _).2.1,
    (q.2.1 _).2.1.trans (edgeMem.mp R.2).2⟩,
    fun R S hn => q.2.2 _ _ (fun h => hn (Subtype.ext (congrArg (fun x : H => x.val) h)))⟩⟩

noncomputable def combine (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty)
    (q : ∀ c : parts U H, Selection c.val (edges c.val H)) : Selection U H := by
  let f (R : H) := (q (atPart hU hne R)).val (atLocal hU hne R)
  refine ⟨f,⟨fun R => ⟨((q _).2.1 _).1, ((q _).2.1 _).2.1,
    (((q _).2.1 _).2.2).trans (partSub hU _)⟩,?_⟩⟩
  intro R S hn
  let c := atPart hU hne R
  let d := atPart hU hne S
  by_cases he : c = d
  · have hc : R.val ⊆ c.val := atPartSub hU hne R
    have hd : S.val ⊆ c.val := he ▸ atPartSub hU hne S
    have hcR : R.val ∈ edges c.val H := edgeMem.mpr ⟨R.2,hc⟩
    have hcS : S.val ∈ edges c.val H := edgeMem.mpr ⟨S.2,hd⟩
    change Disjoint ((q c).val ⟨R.val,hcR⟩) ((q d).val ⟨S.val,edgeMem.mpr ⟨S.2,atPartSub hU hne S⟩⟩)
    rw [show (q d).val ⟨S.val,edgeMem.mpr ⟨S.2,atPartSub hU hne S⟩⟩ =
        (q c).val ⟨S.val,hcS⟩ from dependentSelectionEq q he.symm rfl]
    exact (q c).2.2 _ _ (fun h => hn (Subtype.ext (congrArg (fun x : edges c.val H => x.val) h)))
  · exact (partDisjoint c d he).mono ((q c).2.1 _).2.2 ((q d).2.1 _).2.2

noncomputable def globalEquiv (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) :
    Selection U H ≃ (∀ c : parts U H, Selection c.val (edges c.val H)) where
  toFun := restrict
  invFun := combine hU hne
  left_inv q := by apply Subtype.ext; funext R; rfl
  right_inv q := by
    funext c
    apply Subtype.ext
    funext R
    change (q (atPart hU hne (toGlobal c R))).val (atLocal hU hne (toGlobal c R)) = (q c).val R
    have he := (atPartEq hU hne (toGlobal c R) c (edgeMem.mp R.2).2).symm
    exact dependentSelectionEq q he rfl

theorem sumRows (hU : ∀ R ∈ H, R ⊆ U) (hne : ∀ R ∈ H, R.Nonempty) :
    (∑ c : parts U H, (edges c.val H).card) = H.card := by
  classical
  have hc := Nat.card_congr (rowsEquiv hU hne)
  rw [Nat.card_sigma] at hc
  simpa using hc.symm

theorem sumPoints (hU : ∀ R ∈ H, R ⊆ U) :
    (∑ c : parts U H, c.val.card) = U.card := by
  classical
  have hdis : ((parts U H : Rows α) : Set (Finset α)).PairwiseDisjoint id := partsDisjoint H U
  have he := card_biUnion hdis
  rw [show (parts U H).biUnion id = U from partsUnion hU] at he
  simpa [sum_attach] using he.symm
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Global

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Residual
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Split (Matching)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Equiv (Perfect countPerfect)
variable {α : Type*} [DecidableEq α]
abbrev Rows (α : Type*) := Finset (Finset α)

def support (M : Rows α) : Finset α := M.biUnion id

theorem cardSupport {M : Rows α}
    (hd : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (he : ∀ e ∈ M, e.card = 2) :
    (support M).card = 2 * M.card := by
  have hh : (M : Set (Finset α)).PairwiseDisjoint id := hd
  unfold support
  rw [card_biUnion hh]
  calc
    _ = ∑ _e ∈ M, (2:Nat) := sum_congr rfl he
    _ = 2 * M.card := by simp [Nat.mul_comm]

theorem supportSub {M : Rows α} {A : Finset α} (h : ∀ e ∈ M, e ⊆ A) :
    support M ⊆ A := by
  intro a ha
  obtain ⟨e,he,ha⟩ := mem_biUnion.mp ha
  exact h e he ha

def liftRow (S : Finset α) : Finset S ↪ Finset α :=
  (Finset.mapEmbedding (Function.Embedding.subtype (· ∈ S))).toEmbedding

def flatten (S : Finset α) (M : Rows S) : Rows α := M.map (liftRow S)

def lower (S : Finset α) (M : Rows α) : Rows S := M.image (fun e => e.subtype (· ∈ S))

theorem liftLower (S : Finset α) {e : Finset α} (he : e ⊆ S) :
    liftRow S (e.subtype (· ∈ S)) = e := subtype_map_of_mem he

theorem flatLower (S : Finset α) (M : Rows α) (h : ∀ e ∈ M, e ⊆ S) :
    flatten S (lower S M) = M := by
  ext e
  constructor
  · intro he
    obtain ⟨er,her,hr⟩ := mem_map.mp he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp her
    rw [liftLower S (h f hf)] at hr
    exact hr ▸ hf
  · intro he
    exact mem_map.mpr ⟨e.subtype (· ∈ S),mem_image.mpr ⟨e,he,rfl⟩,liftLower S (h _ he)⟩

theorem lowerFlat (S : Finset α) (M : Rows S) : lower S (flatten S M) = M := by
  have h (r : Finset S) : (liftRow S r).subtype (· ∈ S) = r := by
    apply (liftRow S).injective
    exact liftLower S (fun _ ha => property_of_mem_map_subtype r ha)
  ext r
  constructor
  · intro hr
    obtain ⟨e,he,heq⟩ := mem_image.mp hr
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    rw [h f] at heq
    exact heq ▸ hf
  · intro hr
    exact mem_image.mpr ⟨liftRow S r,mem_map.mpr ⟨r,hr,rfl⟩,h r⟩

theorem lowerPerfect {M : Rows α} {A : Finset α} {j : Nat}
    (hm : Matching A M j) : Perfect (lower (support M) M) := by
  let S := support M
  have hsub (e : Finset α) (he : e ∈ M) : e ⊆ S :=
    fun x hx => mem_biUnion.mpr ⟨e,he,hx⟩
  refine ⟨?_,?_,?_⟩
  · intro e he
    obtain ⟨f,hf,rfl⟩ := mem_image.mp he
    rw [← card_map (Function.Embedding.subtype (· ∈ S))]
    exact (congrArg Finset.card (liftLower S (hsub _ hf))).trans (hm.2.1 _ hf).1
  · intro e he f hf hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hf
    exact disjoint_left.mpr (fun _ h₁ h₂ => (disjoint_left.mp
      (hm.1 _ ha _ hb (fun h => hn (congrArg (Finset.subtype (· ∈ S)) h))))
        (mem_subtype.mp h₁) (mem_subtype.mp h₂))
  · intro a
    obtain ⟨e,he,ha⟩ := mem_biUnion.mp a.2
    exact ⟨e.subtype (· ∈ S),mem_image.mpr ⟨e,he,rfl⟩,mem_subtype.mpr ha⟩

theorem supportFlat {S : Finset α} {M : Rows S} (hp : Perfect M) :
    support (flatten S M) = S := by
  ext a
  constructor
  · intro ha
    obtain ⟨e,he,ha⟩ := mem_biUnion.mp ha
    obtain ⟨f,_,rfl⟩ := mem_map.mp he
    exact property_of_mem_map_subtype f ha
  · intro ha
    obtain ⟨e,he,ha'⟩ := hp.2.2 ⟨a,ha⟩
    exact mem_biUnion.mpr ⟨liftRow S e,mem_map.mpr ⟨e,he,rfl⟩,mem_map.mpr ⟨⟨a,ha⟩,ha',rfl⟩⟩

theorem flatMatching {A S : Finset α} {M : Rows S} {j : Nat}
    (hS : S ∈ A.powersetCard (2*j)) (hm : Perfect M) : Matching A (flatten S M) j := by
  obtain ⟨hsub,hcard⟩ := mem_powersetCard.mp hS
  have hd : ∀ e ∈ flatten S M, ∀ f ∈ flatten S M, e ≠ f → Disjoint e f := by
    intro e he f hf hn
    obtain ⟨a,ha,rfl⟩ := mem_map.mp he
    obtain ⟨b,hb,rfl⟩ := mem_map.mp hf
    exact (disjoint_map _).mpr (hm.2.1 _ ha _ hb (fun h => hn (congrArg (liftRow S) h)))
  have he : ∀ e ∈ flatten S M, e.card = 2 ∧ e ⊆ A := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := mem_map.mp he
    exact ⟨by simpa [liftRow] using hm.1 f hf, fun _ ha => hsub (property_of_mem_map_subtype f ha)⟩
  have hc := cardSupport hd (fun e h => (he e h).1)
  rw [supportFlat hm,hcard] at hc
  exact ⟨hd,he,by omega⟩

theorem supportsExt {A : Finset α} {j : Nat} {S T : A.powersetCard (2*j)}
    {M : {N : Rows (S.val : Finset α) // Perfect N}}
    {N : {N : Rows (T.val : Finset α) // Perfect N}}
    (h : S = T) (hval : flatten S.val M.val = flatten T.val N.val) :
    (⟨S,M⟩ : Σ S : A.powersetCard (2*j), {N : Rows (S.val : Finset α) // Perfect N}) = ⟨T,N⟩ := by
  subst T
  have hv : M.val = N.val := map_injective _ hval
  rw [show M = N from Subtype.ext hv]

def supportEquiv (A : Finset α) (j : Nat) :
    {M : Rows α // Matching A M j} ≃
      (Σ S : A.powersetCard (2*j), {N : Rows (S.val : Finset α) // Perfect N}) where
  toFun m := ⟨⟨support m.val,mem_powersetCard.mpr ⟨supportSub (fun e he => (m.2.2.1 e he).2),
    (cardSupport m.2.1 (fun e he => (m.2.2.1 e he).1)).trans (congrArg (2*·) m.2.2.2)⟩⟩,
    ⟨lower (support m.val) m.val, lowerPerfect m.2⟩⟩
  invFun p := ⟨flatten p.1.val p.2.val,flatMatching p.1.2 p.2.2⟩
  left_inv m := Subtype.ext (flatLower _ _ (fun e he _ ha => mem_biUnion.mpr ⟨e,he,ha⟩))
  right_inv p := by
    refine supportsExt (Subtype.ext (supportFlat p.2.2)) ?_
    apply flatLower
    intro e he a ha
    exact mem_biUnion.mpr ⟨e,he,ha⟩

theorem countResidual (A : Finset α) (j : Nat) :
    Nat.card {M : Rows α // Matching A M j} =
      A.card.choose (2*j) * ((2*j).factorial / (2^j*j.factorial)) := by
  classical
  rw [Nat.card_congr (supportEquiv A j), Nat.card_sigma]
  calc
    _ = ∑ _s : A.powersetCard (2*j), ((2*j).factorial / (2^j*j.factorial)) := by
      apply Finset.sum_congr rfl
      intro S _
      exact countPerfect j (by simpa using (mem_powersetCard.mp S.2).2)
    _ = _ := by simp [card_powersetCard]
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Residual

open Finset
namespace PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903 (Linear Covers)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components (Rows component step foldSeq)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Connectivity (edges connected)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence (graph Nodes connectedClassification)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903LocalSelection (Selection vacant uncoveredCard)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Counts (freeEquiv countSingle countCycle)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Global
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Split (Matching splitEquiv)
open PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Residual (countResidual)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {U : Finset α} {H : Rows α}

open Classical in
noncomputable def free (U : Finset α) (H : Rows α) :=
  (parts U H).filter (fun C => C.card = 2*(edges C H).card + 1)

open Classical in
noncomputable def cycles (U : Finset α) (H : Rows α) :=
  (parts U H).filter (fun C => C.card = 2*(edges C H).card ∧ ∀ R ∈ edges C H, R.card = 3)

def Bad (U : Finset α) (H : Rows α) :=
  (∃ R ∈ H, R.card < 2) ∨ ∃ C ∈ parts U H, C.card < 2*(edges C H).card

theorem rowSizes (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) :
    ∀ R ∈ H, 2 ≤ R.card ∧ R.card ≤ 3 :=
  fun R hR => ⟨Nat.le_of_not_lt (fun h => hb (Or.inl ⟨R,hR,h⟩)), hr R hR⟩

theorem nonemptyRows (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) :
    ∀ R ∈ H, R.Nonempty :=
  fun R hR => card_pos.mp (by have := (rowSizes hr hb R hR).1; omega)

theorem allTriple {X : Rows α} (hr : ∀ R ∈ X, 2 ≤ R.card ∧ R.card ≤ 3)
    (h : (X.filter (fun R => R.card = 2)).card = 0) : ∀ R ∈ X, R.card = 3 := by
  classical
  intro R hR
  have hsz := hr R hR
  have hn : R.card ≠ 2 := by
    intro he
    have hm : R ∈ X.filter (fun R => R.card = 2) := mem_filter.mpr ⟨hR,he⟩
    rw [Finset.card_eq_zero.mp h] at hm
    exact notMem_empty _ hm
  omega

theorem partCases (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) (c : parts U H) :
    let E := edges c.val H
    (c.val.card = 2*E.card+1 ∧ ∀ R ∈ E, R.card = 3) ∨
    (c.val.card = 2*E.card ∧ ∃! R : E, R.val.card = 2) ∨
    (c.val.card = 2*E.card ∧ (∀ R ∈ E, R.card = 3) ∧
      Nat.card (graph c.val E).edgeSet = Nat.card (Nodes c.val E)) := by
  classical
  let E := edges c.val H
  have hz : 2*E.card ≤ c.val.card := Nat.le_of_not_lt (fun h => hb (Or.inr ⟨c.val,c.2,h⟩))
  have hr' : ∀ R ∈ E, 2 ≤ R.card ∧ R.card ≤ 3 := fun R hR => rowSizes hr hb R (edgeMem.mp hR).1
  have hc : (graph c.val E).Connected := by
    obtain ⟨v,_,hv⟩ := mem_image.mp c.2
    change (graph c.val (edges c.val H)).Connected
    rw [← hv]
    exact connected H v (nonemptyRows hr hb)
  rcases connectedClassification c.val E (fun _ h => (edgeMem.mp h).2) hr' hc hz with ha | hb | hc'
  · exact Or.inl ⟨ha.1,allTriple hr' ha.2.1⟩
  · refine Or.inr (Or.inl ⟨hb.1,?_⟩)
    obtain ⟨R,hR⟩ := Finset.card_eq_one.mp hb.2.1
    have hRmem : R ∈ E.filter (fun R => R.card = 2) := by rw [hR]; exact mem_singleton_self _
    refine ⟨⟨R,(mem_filter.mp hRmem).1⟩,(mem_filter.mp hRmem).2,?_⟩
    intro S hS
    have hm : S.val ∈ E.filter (fun R => R.card = 2) := mem_filter.mpr ⟨S.2,hS⟩
    rw [hR] at hm
    exact Subtype.ext (mem_singleton.mp hm)
  · exact Or.inr (Or.inr ⟨hc'.1,allTriple hr' hc'.2.1,hc'.2.2⟩)

theorem partPointCount (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) (c : parts U H) :
    c.val.card = 2*(edges c.val H).card + if c.val ∈ free U H then 1 else 0 := by
  classical
  have hh : c.val ∈ free U H ↔ c.val.card = 2*(edges c.val H).card+1 := by
    simp [free,c.2]
  rcases partCases hr hb c with ha | hb | hc
  · rw [if_pos (hh.mpr ha.1)]
    exact ha.1
  · rw [if_neg (fun h => by have := hh.mp h; omega),Nat.add_zero]
    exact hb.1
  · rw [if_neg (fun h => by have := hh.mp h; omega),Nat.add_zero]
    exact hc.1

theorem surplus (hU : ∀ R ∈ H, R ⊆ U) (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) :
    U.card = 2*H.card + (free U H).card := by
  classical
  rw [← sumPoints hU, ← sumRows hU (nonemptyRows hr hb)]
  calc
    _ = ∑ c : parts U H, (2*(edges c.val H).card + if c.val ∈ free U H then 1 else 0) :=
      Finset.sum_congr rfl (fun c _ => partPointCount hr hb c)
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum]
      congr 1
      rw [← sum_filter]
      simp only [sum_const, smul_eq_mul, mul_one]
      exact card_bij (fun c _ => c.val)
        (fun c hc => (mem_filter.mp hc).2)
        (fun _ _ _ _ h => Subtype.ext h)
        (fun c hc => ⟨⟨c,(mem_filter.mp hc).1⟩,mem_filter.mpr ⟨mem_univ _,hc⟩,rfl⟩)

theorem localCount (hr : ∀ R ∈ H, R.card ≤ 3) (hb : ¬ Bad U H) (c : parts U H) :
    Nat.card (Selection c.val (edges c.val H)) =
      (if c.val ∈ free U H then c.val.card else 1) * (if c.val ∈ cycles U H then 2 else 1) := by
  classical
  let E := edges c.val H
  have hU (R : E) : R.val ⊆ c.val := (edgeMem.mp R.2).2
  have hc : (graph c.val E).Connected := by
    obtain ⟨v,_,hv⟩ := mem_image.mp c.2
    change (graph c.val (edges c.val H)).Connected
    rw [← hv]
    exact connected H v (nonemptyRows hr hb)
  have hF : c.val ∈ free U H ↔ c.val.card = 2*E.card+1 := by simp [free,c.2,E]
  have hC : c.val ∈ cycles U H ↔ c.val.card = 2*E.card ∧ ∀ R ∈ E, R.card = 3 := by
    simp [cycles,c.2,E]
  rcases partCases hr hb c with ⟨hs,hall⟩ | ⟨hs,hpair⟩ | ⟨hs,hall,hedge⟩
  · change c.val.card = 2*E.card+1 at hs
    change ∀ R ∈ E, R.card = 3 at hall
    rw [if_pos (hF.mpr hs),if_neg (fun h => by have := (hC.mp h).1; omega),Nat.mul_one]
    have ht := PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence.incidenceTree c.val E (fun _ hm => (edgeMem.mp hm).2) hc (by
      have hsum : (∑ R ∈ E, R.card) = 3*E.card := by
        calc
          _ = ∑ _R ∈ E, (3:Nat) := Finset.sum_congr rfl hall
          _ = _ := by simp [Nat.mul_comm]
      rw [hsum]
      omega)
    simpa using Nat.card_congr (freeEquiv hU ht hs (fun R => hall R.val R.2))
  · change c.val.card = 2*E.card at hs
    obtain ⟨R,hR,hR'⟩ := hpair
    have h2 : ¬ (∀ R ∈ E, R.card = 3) := by intro h; have := h R.val R.2; omega
    rw [if_neg (fun h => by have := hF.mp h; omega),
      if_neg (fun h => h2 (hC.mp h).2), Nat.mul_one]
    have hshape (S : E) : S.val.card = if S = R then 2 else 3 := by
      by_cases he : S = R
      · simpa [he] using hR
      · rw [if_neg he]
        have hsz := rowSizes hr hb S.val (edgeMem.mp S.2).1
        have hn : S.val.card ≠ 2 := fun h => he (hR' S h)
        omega
    have hcount : (E.filter (fun S => S.card = 2)).card = 1 := by
      apply card_eq_one.mpr
      refine ⟨R.val,?_⟩
      ext S
      simp only [mem_filter,mem_singleton]
      exact ⟨fun ⟨hS, h⟩ => congrArg (fun z : E => z.val) (hR' ⟨S,hS⟩ h),
        fun h => h ▸ ⟨R.2,hR⟩⟩
    have hz := PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence.cardSum E
      (fun S hS => rowSizes hr hb S (edgeMem.mp hS).1)
    have ht := PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Incidence.incidenceTree c.val E (fun _ hm => (edgeMem.mp hm).2) hc (by omega)
    exact countSingle hU ht hs R hshape
  · rw [if_neg (fun h => by have := hF.mp h; omega),if_pos (hC.mpr ⟨hs,hall⟩),Nat.one_mul]
    exact countCycle hU hc hedge hs (fun R => hall R.val R.2)

theorem cardSelection (hU : ∀ R ∈ H, R ⊆ U) (hr : ∀ R ∈ H, R.card ≤ 3)
    (hb : ¬ Bad U H) :
    Nat.card (Selection U H) = (free U H).prod Finset.card * 2^(cycles U H).card := by
  classical
  rw [Nat.card_congr (globalEquiv hU (nonemptyRows hr hb)), Nat.card_pi]
  simp_rw [localCount hr hb]
  rw [prod_mul_distrib]
  congr 1
  · rw [← prod_filter]
    change (∏ c ∈ (parts U H).attach.filter (fun c => c.val ∈ free U H), c.val.card) = _
    exact prod_bij (fun c _ => c.val)
      (fun c hc => (mem_filter.mp hc).2)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun c hc => ⟨⟨c,(mem_filter.mp hc).1⟩,mem_filter.mpr ⟨mem_attach _ _,hc⟩,rfl⟩)
      (fun _ _ => rfl)
  · rw [← prod_filter,prod_const]
    congr 1
    change ((parts U H).attach.filter (fun c => c.val ∈ cycles U H)).card = _
    exact card_bij (fun c _ => c.val)
      (fun c hc => (mem_filter.mp hc).2)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun c hc => ⟨⟨c,(mem_filter.mp hc).1⟩,mem_filter.mpr ⟨mem_attach _ _,hc⟩,rfl⟩)

open Classical in
theorem main (hU : ∀ R ∈ H, R ⊆ U) (hr : ∀ R ∈ H, R.card ≤ 3) (lin : Linear H) (s : Nat) :
    let j := s-H.card
    Nat.card {M : Rows α // Covers U H M s} =
      if Bad U H ∨ s < H.card ∨ (free U H).card < 2*j then 0 else
        ((free U H).prod Finset.card) * 2^(cycles U H).card *
         (free U H).card.choose (2*j) * ((2*j).factorial / (2^j*j.factorial)) := by
  classical
  dsimp only
  by_cases hb : Bad U H
  · rw [if_pos (Or.inl hb)]
    apply PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903.noBadCount U H s lin
    rcases hb with h | ⟨C,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨C,h⟩
  by_cases hs : s < H.card
  · rw [if_pos (Or.inr (Or.inl hs))]
    exact PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903.noSmallCount U H s hU lin hs
  have hsn : H.card ≤ s := by omega
  letI : Fintype (Selection U H) := by unfold Selection; infer_instance
  rw [Nat.card_congr (splitEquiv lin hr s hsn), Nat.card_sigma]
  have hc (q : Selection U H) : (vacant q).card = (free U H).card := by
    have huv := uncoveredCard q
    change (vacant q).card = _ at huv
    rw [huv,surplus hU hr hb]
    omega
  simp_rw [countResidual, hc]
  rw [Finset.sum_const,smul_eq_mul,Finset.card_univ,← Nat.card_eq_fintype_card,
    cardSelection hU hr hb]
  by_cases he : (free U H).card < 2*(s-H.card)
  · rw [if_pos (Or.inr (Or.inr he)),Nat.choose_eq_zero_of_lt he]
    simp
  · rw [if_neg (by tauto)]
    ring
end PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main

open Classical in
theorem PEqualNP.Outside.L_lib_931.linear_formula : ∀ n : Nat,
  let Rows := Finset (Finset (Fin n))
  let disj := fun M : Rows => ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f
  let linear := fun H : Rows => ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1
  let count := fun (U : Finset (Fin n)) (H : Rows) (s : Nat) =>
    Nat.card {M : Rows // disj M ∧ (∀ e ∈ M, e.card = 2 ∧ e ⊆ U) ∧
      (∀ R ∈ H, ∃ e ∈ M, e ⊆ R) ∧ M.card = s}
  ∀ (U : Finset (Fin n)) (H : Rows), (∀ R ∈ H, R ⊆ U ∧ R.card ≤ 3) → linear H →
    let component := fun v : Fin n => (List.range n).foldl (fun A _ =>
      A ∪ (H.filter (fun R => ¬ Disjoint R A)).biUnion id) {v}
    let parts := U.image component
    let edges := fun C : Finset (Fin n) => H.filter (fun R => R ⊆ C)
    let free := parts.filter (fun C => C.card = 2*(edges C).card+1)
    let cycles := parts.filter (fun C => C.card = 2*(edges C).card ∧
      ∀ R ∈ edges C, R.card = 3)
    let bad := (∃ R ∈ H, R.card < 2) ∨ ∃ C ∈ parts, C.card < 2*(edges C).card
    ∀ s : Nat, let j := s-H.card
      count U H s = if bad ∨ s < H.card ∨ free.card < 2*j then 0 else
        (free.prod Finset.card) * 2^cycles.card * free.card.choose (2*j) *
          ((2*j).factorial / (2^j*j.factorial)) := by
  intro n
  dsimp only
  intro U H hU lin s
  have hh := PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main.main (U := U) (H := H)
    (fun R hR => (hU R hR).1) (fun R hR => (hU R hR).2) lin s
  unfold PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main.Bad PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main.free PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Main.cycles
    PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Global.parts PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Connectivity.edges at hh
  have hc (v : Fin n) : (List.range n).foldl (fun A _ =>
      A ∪ (H.filter (fun R => ¬ Disjoint R A)).biUnion id) {v} =
      PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components.component H v := by
    change (List.range n).foldl (fun A _ => PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components.step H A) {v} = _
    rw [PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components.foldSeq, List.length_range]
    simp [PEqualNP.Outside.L_lib_931.ReducedEngine.LocalPairing903Components.component]
  simp_rw [hc]
  convert hh using 1 <;> congr!


namespace PEqualNP.Outside.L_lib_931
variable {n : Nat}

def fastCount (U : Names n) (F : Family n) (s : Nat) : Nat :=
  let component := fun v : Fin n => (List.range n).foldl (fun A _ =>
      A ∪ (F.filter (fun R => ¬ Disjoint R A)).biUnion id) {v}
  let parts := U.image component
  let edges := fun C : Names n => F.filter (fun R => R ⊆ C)
  let free := parts.filter (fun C => C.card = 2*(edges C).card+1)
  let cycles := parts.filter (fun C => C.card = 2*(edges C).card ∧ ∀ R ∈ edges C, R.card = 3)
  let bad := (∃ R ∈ F, R.card < 2) ∨ ∃ C ∈ parts, C.card < 2*(edges C).card
  let j := s-F.card
  if bad ∨ s<F.card ∨ free.card<2*j then 0 else
    (free.prod Finset.card) * 2^cycles.card * free.card.choose (2*j) *
    ((2*j).factorial / (2^j*j.factorial))

theorem fast_on_branch {H : Family n} (ht : ∀ R ∈ H, R.card = 3) (S : Family n) (s : Nat) :
    residualCount (leftU H S) (reduced H S) s = fastCount (leftU H S) (reduced H S) s := by
  let U := leftU H S
  let F := reduced H S
  have hR : ∀ R ∈ F, R ⊆ U ∧ R.card ≤ 3 := by
    intro R hR
    obtain ⟨R₀,hB,rfl⟩ := Finset.mem_image.mp hR
    refine ⟨Finset.inter_subset_right,?_⟩
    exact (Finset.card_le_card Finset.inter_subset_left).trans (ht R₀ (Finset.mem_filter.mp hB).1).le
  have h := linear_formula n U F hR (reduced_linear ht S) s
  change (Nat.card {M : Family n // Bm U F s M}) = fastCount U F s at h
  simpa [residualCount,Nat.card_eq_fintype_card,Fintype.card_subtype] using h

theorem layer_sum {G : Family n} (t : Nat) (p : Family n → Prop) [DecidablePred p] (v : Family n → Nat) :
    (∑ S ∈ G.powerset.filter (fun S => S.card<t ∧ p S), v S) =
    ∑ j ∈ Finset.range t, ∑ S ∈ (G.powersetCard j).filter p, v S := by
  let A := G.powerset.filter (fun S => S.card<t ∧ p S)
  have hb (S : Family n) (hS : S ∈ A) :
      (∑ j ∈ Finset.range t, if S.card=j then v S else 0) = v S := by
    have ht := (Finset.mem_filter.mp hS).2.1
    rw [Finset.sum_eq_single S.card]
    · simp
    · intro j _ hn; exact if_neg (Ne.symm hn)
    · exact fun h => (h (Finset.mem_range.mpr ht)).elim
  calc
    _ = ∑ S ∈ A, ∑ j ∈ Finset.range t, if S.card=j then v S else 0 :=
      Finset.sum_congr rfl (fun _ h => (hb _ h).symm)
    _ = ∑ j ∈ Finset.range t, ∑ S ∈ A, if S.card=j then v S else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      congr 1
      ext S
      simp only [A,Finset.mem_filter,Finset.mem_powerset,Finset.mem_powersetCard]
      have := Finset.mem_range.mp hj
      aesop

def runHist (n t : Nat) (H : Family n) (s : Nat) : Nat :=
  (∑ j ∈ Finset.range t, ∑ S ∈ (cores H).powersetCard j,
    if (S.biUnion (outer H)).card=2*S.card ∧ (cores H).card+S.card≤s then
      2^S.card * fastCount (leftU H S) (reduced H S) (s-(cores H).card-S.card) else 0) % (2^t)

theorem run_hist {H : Family n} (ht : ∀ R ∈ H, R.card = 3)
    (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2) (s t : Nat) :
    (allMatch s H).card % (2^t) = runHist n t H s := by
  rw [modulo_sum ht hd,layer_sum]
  unfold runHist
  apply congrArg (fun z : Nat => z % (2^t))
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S hS
  rw [fast_on_branch ht]

theorem branch_count_le (G : Family n) (t : Nat) :
    (G.powerset.filter (fun S => S.card<t)).card ≤ (G.card+1)^t := by
  classical
  let A := G.powerset.filter (fun S => S.card<t)
  let sew (S : A) (i : Fin t) : Option G :=
    let L := S.val.toList
    if h : i.val<L.length then
      some ⟨L[i.val], (Finset.mem_powerset.mp (Finset.mem_filter.mp S.property).1)
        (by exact Finset.mem_toList.mp (List.getElem_mem h))⟩
    else none
  have hm (S : A) (x : G) : x.val ∈ S.val ↔ ∃ i, sew S i=some x := by
    constructor
    · intro hx
      have he := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hx)
      rcases he with ⟨i,hi,he⟩
      have hl : S.val.toList.length<t := by simpa using (Finset.mem_filter.mp S.property).2
      refine ⟨⟨i,hi.trans hl⟩,?_⟩
      simp only [sew,dif_pos hi,Option.some.injEq]
      exact Subtype.ext he
    · rintro ⟨i,hi⟩
      unfold sew at hi
      split at hi
      · cases hi
        exact Finset.mem_toList.mp (List.getElem_mem ‹_›)
      · contradiction
  have inj : Function.Injective sew := by
    intro S T h
    apply Subtype.ext
    ext x
    by_cases hx : x ∈ G
    · rw [hm S ⟨x,hx⟩, hm T ⟨x,hx⟩,h]
    · have hS := Finset.mem_powerset.mp (Finset.mem_filter.mp S.property).1
      have hT := Finset.mem_powerset.mp (Finset.mem_filter.mp T.property).1
      exact ⟨fun m => (hx (hS m)).elim,fun m => (hx (hT m)).elim⟩
  simpa [A,Fintype.card_fun] using Fintype.card_le_of_injective sew inj

theorem core_count_le {H : Family n} (ht : ∀ R ∈ H, R.card=3)
    (hd : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2) (t : Nat) :
    ((cores H).powerset.filter (fun S => S.card<t)).card ≤ (n+1)^t := by
  have hdj := card_biUnion_pairs (M:=cores H) (fun _ h => ((mem_cores_iff ht).mp h).1)
    (fun _ h1 _ h2 hn => cores_pairwise_disjoint ht hd h1 h2 hn)
  have hn := Finset.card_le_card (Finset.subset_univ ((cores H).biUnion id))
  simp only [Finset.card_univ,Fintype.card_fin] at hn
  exact (branch_count_le (cores H) t).trans (Nat.pow_le_pow_left (by omega) _)

end PEqualNP.Outside.L_lib_931

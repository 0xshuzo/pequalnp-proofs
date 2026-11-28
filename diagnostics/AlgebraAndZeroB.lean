import PEqualNP.Defs

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


namespace PEqualNP.Outside.L_lib_931.Code

def header (n : Nat) := List.replicate n true ++ [false]
def bits (width value : Nat) := (List.range width).map (fun h => value.testBit h)
def val : List Bool → Nat
  | [] => 0
  | b::l => b.toNat+2*val l
lemma bit_cons (w v:Nat) : bits (w+1) v = v.testBit 0 :: bits w (v/2) := by
  simp only [bits,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro h _
  simp [Nat.testBit_succ]
lemma read_bits (w v:Nat) (h:v<2^w) : val (bits w v)=v := by
  induction w generalizing v with
  | zero => simp at h; subst h; rfl
  | succ w ih =>
    rw [bit_cons,val,ih (v/2) (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at h; exact h)]
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> simp [h2] <;> omega

def popHeader : List Bool → Nat × List Bool
  | [] => (0,[])
  | false::xs => (0,xs)
  | true::xs => let h := popHeader xs; (h.1+1,h.2)
theorem pop_header (n : Nat) (xs : List Bool) : popHeader (header n ++ xs) = (n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((popHeader (header n ++ xs)).1+1,(popHeader (header n ++ xs)).2) = (n+1,xs)
    rw [ih]

def blocks {α : Type} (w : Nat) (f : List Bool → α) : Nat → List Bool → List α
  | 0, _ => []
  | k+1, xs => if xs=[] then [] else f (xs.take w) :: blocks w f k (xs.drop w)

theorem empty_blocks {α : Type} (w : Nat) (f : List Bool → α) (k : Nat) :
    blocks w f k [] = [] := by cases k <;> simp [blocks]

theorem blocks_roundtrip {α β : Type} (w : Nat) (hw : 0<w)
    (enc : α → List Bool) (f : List Bool → β) (g : α → β) (L : List α)
    (hlen : ∀ x ∈ L, (enc x).length=w) (hval : ∀ x ∈ L, f (enc x)=g x)
    (k : Nat) (hk : L.length ≤ k) : blocks w f k (L.flatMap enc) = L.map g := by
  induction L generalizing k with
  | nil => simp [empty_blocks]
  | cons x xs ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have he := hlen x (List.mem_cons_self)
      have hn : enc x ++ xs.flatMap enc ≠ [] := by
        intro h
        have := congrArg List.length h
        simp [he] at this
        omega
      have hxt := ih (fun a ha => hlen a (List.mem_cons_of_mem _ ha))
          (fun a ha => hval a (List.mem_cons_of_mem _ ha)) k (by simpa using hk)
      simp [blocks,List.flatMap_cons,hn,List.take_left' he,List.drop_left' he,
        hval x List.mem_cons_self,hxt]

noncomputable def codeRow {n : Nat} (R : Finset (Fin n)) := R.toList.flatMap (fun i => bits (n.log2+1) i.val)

def decodeRow (n : Nat) (xs : List Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun u => u.val ∈ blocks (n.log2+1) val 3 xs)

theorem flat_width {α : Type} (w : Nat) (e : α → List Bool) (L : List α)
    (h : ∀ x ∈ L, (e x).length=w) : (L.flatMap e).length=L.length*w := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    rw [h x List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]
    omega

theorem row_roundtrip {n : Nat} {R : Finset (Fin n)} (h : R.card=3) :
    decodeRow n (codeRow R)=R := by
  have hl : R.toList.length=3 := by simpa using h
  have hcode := blocks_roundtrip (n.log2+1) (by omega)
    (fun u : Fin n => bits (n.log2+1) u.val) val Fin.val R.toList
    (fun u _ => by simp [bits])
    (fun u _ => read_bits _ _ (lt_trans u.isLt Nat.lt_log2_self)) 3 hl.le
  ext u
  simp only [decodeRow,codeRow,hcode,Finset.mem_filter,Finset.mem_univ,true_and,List.mem_map]
  constructor
  · rintro ⟨v,hv,hEq⟩
    have e : v=u := Fin.ext hEq
    simpa [e] using hv
  · intro hu
    exact ⟨u,by simpa using hu,rfl⟩

def parseFamily (n : Nat) (xs : List Bool) : Finset (Finset (Fin n)) :=
  (blocks (3*(n.log2+1)) (decodeRow n) xs.length xs).toFinset

theorem family_roundtrip {n : Nat} (H : Finset (Finset (Fin n))) (hh : ∀ R ∈ H, R.card=3) :
    parseFamily n (H.toList.flatMap codeRow)=H := by
  let w := n.log2+1
  have hr (R : Finset (Fin n)) (hR : R ∈ H.toList) : (codeRow R).length=3*w := by
    rw [codeRow,flat_width w _ _ (fun _ _ => by simp [bits,w])]
    simp [hh R (by simpa using hR)]
  have hl := flat_width (3*w) codeRow H.toList hr
  have hk : H.toList.length ≤ (H.toList.flatMap codeRow).length := by
    rw [hl]
    exact Nat.le_mul_of_pos_right _ (by dsimp [w]; omega)
  have hrtrip := blocks_roundtrip (3*w) (by dsimp [w]; omega)
    codeRow (decodeRow n) id H.toList hr (fun R hR => row_roundtrip (hh R (by simpa using hR)))
    _ hk
  simpa [parseFamily,w] using congrArg List.toFinset hrtrip

def outputFor (n t : Nat) (H : Finset (Finset (Fin n))) : List Bool :=
  (List.range (n/2+1)).flatMap fun s => bits t
    ((Finset.univ.filter (fun N : Finset (Finset (Fin n)) =>
      (∀ g ∈ N, g.card=2 ∧ g ⊆ Finset.univ) ∧
      (∀ g ∈ N, ∀ h ∈ N, g≠h → Disjoint g h) ∧
      (∀ R ∈ H, ∃ g ∈ N, g⊆R) ∧ N.card=s)).card)

def withT (n : Nat) (b : Nat × List Bool) := outputFor n b.1 (parseFamily n b.2)
def withN (a : Nat × List Bool) := withT a.1 (popHeader a.2)
def decode (x : List Bool) := withN (popHeader x)

theorem decode_spec {n : Nat} (t : Nat) (H : Finset (Finset (Fin n))) (hh : ∀ R ∈ H, R.card=3) :
    decode (header n ++ header t ++ H.toList.flatMap codeRow) =
    (List.range (n/2+1)).flatMap fun s => bits t
      (Nat.card {N : Finset (Finset (Fin n)) // (∀ g ∈ N, g.card=2 ∧ g ⊆ Finset.univ) ∧
      (∀ g ∈ N, ∀ h ∈ N, g≠h → Disjoint g h) ∧
      (∀ R ∈ H, ∃ g ∈ N, g⊆R) ∧ N.card=s}) := by
  rw [List.append_assoc,decode,pop_header,withN,pop_header,withT,family_roundtrip H hh]
  simp only [outputFor,
    Nat.card_eq_fintype_card,Fintype.card_subtype]

end PEqualNP.Outside.L_lib_931.Code

namespace PEqualNP.Outside.L_lib_931.Erase
open Turing
lemma i7 (tm:FinTM2) (s:List (tm.Γ tm.k₀)) :
    initList tm s =
      (⟨some tm.main,tm.initialState,Function.update (fun _=>[]) tm.k₀ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold initList
  congr 1
  funext k
  by_cases h:k=tm.k₀
  · subst h;simp
  · simp [h]
lemma i9 (tm:FinTM2) (s:List (tm.Γ tm.k₁)) :
    haltList tm s =
      (⟨none,tm.initialState,Function.update (fun _=>[]) tm.k₁ s⟩ :
        TM2.Cfg tm.Γ tm.Λ tm.σ):=by
  unfold haltList
  congr 1
  funext k
  by_cases h:k=tm.k₁
  · subst h;simp
  · simp [h]
def d60:List Bool→ TM2.Stmt (fun _:Unit=>Bool) Unit Bool
  | []=>.halt
  | a::l=>.push () (fun _=>a) (d60 l)
def d3 (l:List Bool):Unit→ TM2.Stmt (fun _:Unit=>Bool) Unit Bool :=
  fun _=>.pop () (fun _ o=>o.isSome)
    (.branch (fun s=>s)
      (.load (fun _=>false) (.goto fun _=>()))
      (d60 l.reverse))
def d20 (l:List Bool):FinTM2 where
  K:=Unit
  k₀:=()
  k₁:=()
  Γ _:=Bool
  Λ:=Unit
  main:=()
  σ:=Bool
  initialState:=false
  m:=d3 l
abbrev a3z:Type:=TM2.Cfg (fun _:Unit=>Bool) Unit Bool
lemma d17 (S T:List Bool) :
    Function.update (fun _:Unit=>S) () T=fun _=>T:=by
  funext k
  simp
lemma d42 (l:List Bool) (v:Bool) (S:List Bool) :
    TM2.stepAux (d60 l) v (fun _:Unit=>S) =
      (⟨none,v,fun _=>l.reverse++S⟩:a3z):=by
  induction l generalizing S with
  | nil=>rfl
  | cons a l ih =>
    simp only [d60,TM2.stepAux]
    rw [d17,ih]
    simp
lemma d64 (l:List Bool) (x:Bool) (a:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>x::a⟩:a3z) =
      some ⟨some (),false,fun _=>a⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp
lemma d76 (l:List Bool) :
    TM2.step (d3 l) (⟨some (),false,fun _=>[]⟩:a3z) =
      some ⟨none,false,fun _=>l⟩:=by
  simp only [TM2.step,d3,TM2.stepAux]
  rw [d17]
  simp only [List.head?_nil,Option.isSome_none,Bool.cond_false,List.tail_nil]
  rw [d42]
  simp
lemma d63 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (⟨some (),false,fun _=>a⟩:a3z)) =
      some ⟨none,false,fun _=>l⟩:=by
  induction a with
  | nil=>exact d76 l
  | cons x a ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    have e:flip bind (TM2.step (d3 l))
        (some (⟨some (),false,fun _=>x::a⟩:a3z)) =
        some ⟨some (),false,fun _=>a⟩:=d64 l x a
    rw [e,ih]
lemma d75 (l:List Bool) (a:List Bool) :
    (flip bind (TM2.step (d3 l)))^[a.length+1]
        (some (initList (d20 l) a))=some (haltList (d20 l) l):=by
  refine (congrArg (fun c=>(flip bind (TM2.step (d3 l)))^[a.length+1]
    (some c)) (i7 (d20 l) a)).trans
    (Eq.trans ?_ (congrArg some (i9 (d20 l) l)).symm)
  show (flip bind (TM2.step (d3 l)))^[a.length+1]
    (some (⟨some (),false,Function.update (fun _=>[]) () a⟩:a3z)) =
    some (⟨none,false,Function.update (fun _=>[]) () l⟩:a3z)
  rw [d17,d17]
  exact d63 l a

def erase : TM2ComputableAux Bool Bool := ⟨d20 [],Equiv.refl _,Equiv.refl _⟩
theorem fin (i : erase.tm.K) : Finite (erase.tm.Γ i) := inferInstanceAs (Finite Bool)
theorem erases (x : List Bool) :
    Nonempty (TM2OutputsInTime erase.tm (x.map erase.inputAlphabet.invFun)
      (some (([] : List Bool).map erase.outputAlphabet.invFun)) ((x.length+2)^1)) := by
  refine ⟨{steps := x.length+1,steps_le_m := by simp,evals_in_steps := ?_}⟩
  have hx : x.map (Equiv.refl Bool).invFun = x := by simp
  change (flip bind (TM2.step (d3 [])))^[_] (some (initList (d20 []) (x.map (Equiv.refl Bool).invFun))) =
    some (haltList (d20 []) [])
  rw [hx]
  exact d75 [] x
end PEqualNP.Outside.L_lib_931.Erase

namespace PEqualNP.Outside.L_lib_931
theorem compiled_zero : let header := fun n : Nat => List.replicate n true ++ [false]
let bits := fun (w x : Nat) => (List.range w).map (fun i => x.testBit i)
∃ (f : List Bool → List Bool) (M : Turing.TM2ComputableAux Bool Bool) (C : Nat),
  (∀ i, Finite (M.tm.Γ i)) ∧
  ∀ (n t : Nat) (H : Finset (Finset (Fin n))), (∀ R ∈ H, R.card = 3) →
    (∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2) →
    let Rows := Finset (Finset (Fin n))
    let count := fun (U : Finset (Fin n)) (F : Rows) (s : Nat) =>
      Nat.card {N : Rows // (∀ g ∈ N, g.card = 2 ∧ g ⊆ U) ∧
        (∀ g ∈ N, ∀ h ∈ N, g ≠ h → Disjoint g h) ∧
        (∀ R ∈ F, ∃ g ∈ N, g ⊆ R) ∧ N.card = s}
    let shared := (H.product H).image (fun z => z.1 ∩ z.2)
    let cores := shared.filter (fun c => c.card = 2)
    let ordinary := Finset.univ \ cores.biUnion id
    let base := H.filter (fun R => R ⊆ ordinary)
    let outer := fun c : Finset (Fin n) => (H.filter (fun R => c ⊆ R)).biUnion id \ c
    let left := fun S : Rows => ordinary \ S.biUnion outer
    let reduced := fun S : Rows => base.image (fun R => R ∩ left S)
    let hist := fun s : Nat => count Finset.univ H s
    let encode := header n ++ header t ++ H.toList.flatMap
      (fun R => R.toList.flatMap (fun u => bits (n.log2+1) u.val))
    (∀ S ⊆ cores, ∀ R ∈ reduced S, ∀ T ∈ reduced S, R ≠ T → (R ∩ T).card ≤ 1) ∧
    (∀ s : Nat, hist s % (2^t) =
      ((cores.powerset.filter (fun S => S.card < t ∧ (S.biUnion outer).card = 2*S.card ∧
        cores.card+S.card ≤ s)).sum (fun S =>
          2^S.card * count (left S) (reduced S) (s-cores.card-S.card))) % (2^t)) ∧
    f encode = (List.range (n/2+1)).flatMap (fun s => bits t (hist s)) ∧
    (t = 0 → Nonempty (Turing.TM2OutputsInTime M.tm (encode.map M.inputAlphabet.invFun)
      (some ((f encode).map M.outputAlphabet.invFun)) ((encode.length+2)^(t+C)))) := by
  intro header bits
  refine ⟨Code.decode,Erase.erase,1,Erase.fin,?_⟩
  intro n t H ht hd Rows count shared cores₀ ordinary₀ base₀ outer₀ left₀ reduced₀ hist encode
  have hc (s : Nat) : hist s = (allMatch s H).card := hist_eq _ _ _
  have hr (S : Family n) (s : Nat) :
      count (left₀ S) (reduced₀ S) s = residualCount (leftU H S) (reduced H S) s :=
    hist_eq _ _ _
  have hdec : Code.decode encode = (List.range (n/2+1)).flatMap (fun s => bits t (hist s)) :=
    Code.decode_spec t H ht
  refine ⟨fun S _ => reduced_linear ht S,?_,hdec,?_⟩
  · intro s
    change hist s % (2^t) = ((cores H).powerset.filter (fun S =>
      S.card<t ∧ (S.biUnion (outer H)).card=2*S.card ∧ (cores H).card+S.card≤s)).sum
      (fun S => 2^S.card * count (left₀ S) (reduced₀ S) (s-(cores H).card-S.card)) % (2^t)
    simp_rw [hc,hr]
    exact modulo_sum ht hd s t
  · intro hz
    have he : Code.decode encode = [] := by
      rw [hdec,hz]
      simp [bits]
    rw [he,hz]
    exact Erase.erases encode

end PEqualNP.Outside.L_lib_931

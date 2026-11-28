import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.DictionaryBudget
theorem countUnion {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (paid : Finset ℕ) (m : ℕ)
    (step : ∀ w < m, 1 < (support w).card → ∃ cs : Finset ℕ,
      cs ⊆ Finset.range w ∧ support w ⊆ cs.biUnion support ∧
      cs.card ≤ 1 + (if w ∈ paid then 1 else 0))
    (roots : Finset ℕ) (hr : roots ⊆ Finset.range m) :
    (roots.biUnion support).card ≤ roots.card + ((Finset.range m) ∩ paid).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have : roots = ∅ := by simpa using hr
    simp [this]
  | succ m ih =>
    have old := ih (fun w hw => step w (by omega))
    have hpre : roots.erase m ⊆ Finset.range m := by
      intro w hw
      have ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
      have hlt := Finset.mem_range.mp (hr hmem)
      exact Finset.mem_range.mpr (by omega)
    have hcost : ((Finset.range (m + 1)) ∩ paid).card =
        ((Finset.range m) ∩ paid).card + (if m ∈ paid then 1 else 0) := by
      by_cases h : m ∈ paid
      · have he : Finset.range (m + 1) ∩ paid = insert m (Finset.range m ∩ paid) := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
      · have he : Finset.range (m + 1) ∩ paid = Finset.range m ∩ paid := by
          ext w
          by_cases hw : w = m <;> simp [Finset.range_add_one, hw, h]
        simp [he, h]
    rw [hcost]
    by_cases hm : m ∈ roots
    · have hrins := Finset.insert_erase hm
      have hroots : (roots.erase m).card + 1 = roots.card :=
        Finset.card_erase_add_one hm
      by_cases hb : 1 < (support m).card
      · obtain ⟨cs, hcpre, hcov, hcard⟩ := step m (by omega) hb
        have hsub : roots.biUnion support ⊆ ((roots.erase m) ∪ cs).biUnion support := by
          intro a ha
          obtain ⟨w, hw, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases heq : w = m
          · subst w
            obtain ⟨v, hv, hav⟩ := Finset.mem_biUnion.mp (hcov haw)
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_union_right _ hv, hav⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq, hw⟩), haw⟩
        have hh := old ((roots.erase m) ∪ cs) (Finset.union_subset hpre hcpre)
        have hh' := Finset.card_le_card hsub
        have hu := Finset.card_union_le (roots.erase m) cs
        omega
      · have hh := old (roots.erase m) hpre
        have he : roots.biUnion support = support m ∪ (roots.erase m).biUnion support := by
          conv_lhs => rw [← hrins]
          rw [Finset.biUnion_insert]
        rw [he]
        have hu := Finset.card_union_le (support m) ((roots.erase m).biUnion support)
        omega
    · rw [Finset.erase_eq_of_notMem hm] at hpre
      have hh := old roots hpre
      omega

theorem dag_union_bound {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (R B : Finset ℕ)
    (step : ∀ i, 1 < (f i).card → (∃ a < i, f i ⊆ f a) ∨
      (i ∈ B ∧ ∃ a < i, ∃ b < i, f i ⊆ f a ∪ f b)) :
    (R.biUnion f).card ≤ R.card + B.card := by
  classical
  let m := R.sup id + 1
  have hr : R ⊆ Finset.range m := by
    intro w hw
    have h : w ≤ R.sup id := Finset.le_sup (f := id) hw
    exact Finset.mem_range.mpr (by dsimp [m]; omega)
  have haux : (R.biUnion f).card ≤ R.card + (Finset.range m ∩ B).card := by
    apply countUnion f B m _ R hr
    intro i _ hi
    rcases step i hi with ⟨a, ha, hsub⟩ | ⟨hiB, a, ha, b, hb, hsub⟩
    · refine ⟨{a}, ?_, ?_, ?_⟩
      · simpa using ha
      · simpa using hsub
      · simp
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Finset.mem_range.mpr ha
        · rw [Finset.mem_singleton.mp hw]
          exact Finset.mem_range.mpr hb
      · simpa using hsub
      · simp only [hiB, ite_true]
        exact Finset.card_le_two
  have hl := Finset.card_le_card (Finset.inter_subset_right (s₁ := Finset.range m) (s₂ := B))
  omega


def bucket (sites : Finset Nat) (charge : Nat → Nat) (p : Nat) :=
  sites.filter (fun n => charge n = p)

def Merge (s : Nat → Finset α) (paid : Finset Nat) [DecidableEq α] :=
  ∀ i, 1 < (s i).card →
    (∃ a < i, s i ⊆ s a) ∨ (i ∈ paid ∧ ∃ a < i, ∃ b < i, s i ⊆ s a ∪ s b)

theorem priceRoot {α : Type*} [DecidableEq α] (s : Nat → Finset α) (paid : Finset Nat)
    (step : Merge s paid) (r : Nat) : (s r).card ≤ 1 + paid.card := by
  have h := dag_union_bound s ({r} : Finset Nat) paid step
  simpa using h

theorem birthTrace (sites : Finset Nat) (charge : Nat → Nat) (which : Nat → Fin 6)
    (colors : Nat → Finset (Fin 6)) (coeff : Fin 6 → Nat → Prop)
    (step : ∀ i p, p ∈ colors i →
       (∃ a < i, p ∈ colors a) ∨
       (i ∈ bucket sites charge 7 ∧ which i = p ∧ ∃ a < i, coeff p a)) :
    ∀ i p, p ∈ colors i → ∃ j ∈ bucket sites charge 7, which j = p ∧ ∃ a, coeff p a := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro p hp
    rcases step i p hp with ⟨a,lt,old⟩|⟨here,eq,a,_,hw⟩
    · exact ih a lt p old
    · exact ⟨i,here,eq,a,hw⟩

theorem addBucket (sites : Finset Nat) (charge : Nat → Nat) :
    ∀ k : Nat, (∑ j ∈ Finset.range k, (bucket sites charge j).card) ≤
      (sites.filter (fun i => charge i < k)).card := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : Disjoint (sites.filter (fun i => charge i < k)) (bucket sites charge k) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have lt := (Finset.mem_filter.mp hi).2
      have eq := (Finset.mem_filter.mp hj).2
      omega
    have eq : sites.filter (fun i => charge i < k+1) =
        (sites.filter (fun i => charge i < k)) ∪ bucket sites charge k := by
      ext i
      simp only [bucket, Finset.mem_filter,Finset.mem_union]
      constructor
      · rintro ⟨hi,lt⟩
        by_cases h : charge i = k
        · exact Or.inr ⟨hi,h⟩
        · exact Or.inl ⟨hi,by omega⟩
      · rintro (⟨hi,lt⟩|⟨hi,lt⟩) <;> exact ⟨hi,by omega⟩
    rw [Finset.sum_range_succ,eq,Finset.card_union_of_disjoint hp]
    omega

theorem budget (sites : Finset Nat) (charge : Nat → Nat) (which : Nat → Fin 6)
    (colors : Nat → Finset (Fin 6)) (lines : Fin 6 → Nat → Finset (Fin 15))
    (coefficient : Fin 6 → Nat → Prop) (root : Nat)
    (finalColors : colors root = Finset.univ)
    (safe : Merge colors (bucket sites charge 6))
    (line : ∀ p : Fin 6, Merge (lines p) (bucket sites charge p.val))
    (origin : ∀ i p, p ∈ colors i →
       (∃ a < i, p ∈ colors a) ∨
       (i ∈ bucket sites charge 7 ∧ which i = p ∧ ∃ a < i, coefficient p a))
    (full : ∀ p i, coefficient p i → (if p.val = 0 then 4 else 5) ≤ (lines p i).card) :
    34 ≤ sites.card := by
  have get (p : Fin 6) : ∃ j ∈ bucket sites charge 7, which j = p ∧ ∃ a, coefficient p a :=
    birthTrace sites charge which colors coefficient origin root p (by simp [finalColors])
  have lb (p : Fin 6) : (if p.val = 0 then 3 else 4) ≤ (bucket sites charge p.val).card := by
    obtain ⟨_,_,_,a,ha⟩ := get p
    have sz := full p a ha
    have cost := priceRoot (lines p) _ (line p) a
    by_cases h : p.val = 0 <;> simp [h] at sz ⊢ <;> omega
  have color := priceRoot colors _ safe root
  rw [finalColors] at color
  have six : (Finset.univ : Finset (Fin 6)).card = 6 := by decide
  rw [six] at color
  have onto : (Finset.univ : Finset (Fin 6)) ⊆ (bucket sites charge 7).image which := by
    intro p _
    obtain ⟨j,hj,eq,_⟩ := get p
    exact Finset.mem_image.mpr ⟨j,hj,eq⟩
  have draws := Finset.card_le_card onto
  have cap := Finset.card_image_le (s := bucket sites charge 7) (f := which)
  have total := addBucket sites charge 8
  have lim := Finset.card_le_card (Finset.filter_subset (fun i => charge i < 8) sites)
  have a := lb 0
  have b := lb 1
  have c := lb 2
  have d := lb 3
  have e := lb 4
  have f := lb 5
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.zero_add] at total
  norm_num at a b c d e f draws
  omega

end PEqualNP.Outside.L_meta_9743.DictionaryBudget

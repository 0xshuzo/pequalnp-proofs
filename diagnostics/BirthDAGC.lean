import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9743.MultiBirth
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

/-- Six nonempty families of partial star births can pay for their incidence
    requirements jointly through multiple coefficient wires, with shared sub-DAGs. -/
theorem partialStarBudget
    (sites : Finset Nat) (charge owner coeff : Nat → Nat)
    (sources : Nat → Finset Nat) (lines : Fin 6 → Nat → Finset (Fin 15)) (root : Nat)
    (birthsPaid : sources root ⊆ bucket sites charge 7)
    (joins : Merge sources (bucket sites charge 6))
    (lineStep : ∀ p : Fin 6, Merge (lines p) (bucket sites charge p.val))
    (incidences : ∀ p : Fin 6, (if p.val = 0 then 4 else 5) ≤
      (((bucket (sources root) owner p.val).image coeff).biUnion (lines p)).card) :
    34 ≤ sites.card := by
  classical
  let B := sources root
  have active (p : Fin 6) : 1 ≤ (bucket B owner p.val).card := by
    by_contra h
    have z : (bucket B owner p.val).card = 0 := by omega
    have e := Finset.card_eq_zero.mp z
    have hh := incidences p
    change (if p.val = 0 then 4 else 5) ≤
      (((bucket B owner p.val).image coeff).biUnion (lines p)).card at hh
    simp only [e, Finset.image_empty, Finset.biUnion_empty, Finset.card_empty] at hh
    split at hh <;> omega
  have cost (p : Fin 6) : (if p.val = 0 then 4 else 5) ≤
      (bucket B owner p.val).card + (bucket sites charge p.val).card := by
    have a := incidences p
    have b := dag_union_bound (lines p) ((bucket B owner p.val).image coeff)
      (bucket sites charge p.val) (lineStep p)
    have c := Finset.card_image_le (s := bucket B owner p.val) (f := coeff)
    exact a.trans (b.trans (Nat.add_le_add_right c _))
  have spent := addBucket sites charge 8
  have cap := Finset.card_le_card (Finset.filter_subset (fun i => charge i < 8) sites)
  have parts := addBucket B owner 6
  have partsCap := Finset.card_le_card (Finset.filter_subset (fun i => owner i < 6) B)
  have connects : B.card ≤ 1 + (bucket sites charge 6).card := priceRoot sources _ joins root
  have births : B.card ≤ (bucket sites charge 7).card := Finset.card_le_card birthsPaid
  have a := cost 0
  have b := cost 1
  have c := cost 2
  have d := cost 3
  have e := cost 4
  have f := cost 5
  have a' := active 0
  have b' := active 1
  have c' := active 2
  have d' := active 3
  have e' := active 4
  have f' := active 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at spent parts
  norm_num at a b c d e f
  change 1 ≤ (bucket B owner 0).card at a'
  change 1 ≤ (bucket B owner 1).card at b'
  change 1 ≤ (bucket B owner 2).card at c'
  change 1 ≤ (bucket B owner 3).card at d'
  change 1 ≤ (bucket B owner 4).card at e'
  change 1 ≤ (bucket B owner 5).card at f'
  omega
inductive Feeds (parent : Nat → Finset Nat) : Nat → Nat → Prop
  | start (i) : Feeds parent i i
  | next {i j k} : Feeds parent i j → j ∈ parent k → Feeds parent i k

noncomputable def provenance (parent : Nat → Finset Nat) (birth : Finset Nat) (w : Nat) :
    Finset Nat := by
  classical
  exact birth.filter (fun i => Feeds parent i w)

theorem provenance_mem (parent : Nat → Finset Nat) (birth : Finset Nat) (i w : Nat) :
    i ∈ provenance parent birth w ↔ i ∈ birth ∧ Feeds parent i w := by
  classical
  simp [provenance]

theorem coverDAG
    (sites : Finset Nat) (charge owner coeff : Nat → Nat)
    (born : Finset Nat) (bornPaid : born ⊆ bucket sites charge 7)
    (parent : Nat → Finset Nat) (edges : Nat → Finset (Fin 6 × Fin 15))
    (lines : Fin 6 → Nat → Finset (Fin 15)) (want : Fin 6 → Finset (Fin 15)) (root : Nat)
    (topo : ∀ i j, j ∈ parent i → j < i)
    (leaf : ∀ i ∈ born, parent i = ∅)
    (choices : ∀ i, parent i = ∅ ∨ (∃ j, parent i = {j}) ∨
      (i ∈ bucket sites charge 6 ∧ ∃ j k, parent i = {j,k}))
    (lineStep : ∀ p : Fin 6, Merge (lines p) (bucket sites charge p.val))
    (branch : ∀ i, i ∉ born → edges i ⊆ (parent i).biUnion edges)
    (birth : ∀ i ∈ born, ∀ e ∈ edges i, owner i = e.1.val ∧ e.2 ∈ lines e.1 (coeff i))
    (finalEdges : ∀ p, ∀ l ∈ want p, (p,l) ∈ edges root)
    (degrees : ∀ p, (if p.val = 0 then 4 else 5) ≤ (want p).card) :
    34 ≤ sites.card := by
  classical
  let src := provenance parent born
  have hmem (i w : Nat) : i ∈ src w ↔ i ∈ born ∧ Feeds parent i w :=
    provenance_mem parent born i w
  have above (w i : Nat) (hi : i ∈ src w) :
      i = w ∨ ∃ j ∈ parent w, i ∈ src j := by
    obtain ⟨hb, path⟩ := (hmem i w).mp hi
    cases path with
    | start => exact Or.inl rfl
    | next prev last => exact Or.inr ⟨_,last,(hmem _ _).mpr ⟨hb,prev⟩⟩
  have small (w : Nat) (h : parent w = ∅) : (src w).card ≤ 1 := by
    have sub : src w ⊆ {w} := by
      intro i hi
      rcases above w i hi with eq | ⟨j,hj,_⟩
      · simpa only [Finset.mem_singleton] using eq
      · simp [h] at hj
    simpa using Finset.card_le_card sub
  have lift (w : Nat) (hw : 1 < (src w).card) : src w ⊆ (parent w).biUnion src := by
    intro i hi
    rcases above w i hi with eq | ⟨j,hj,hsub⟩
    · subst i
      have hb := ((hmem _ _).mp hi).1
      have := small w (leaf w hb)
      omega
    · exact Finset.mem_biUnion.mpr ⟨j,hj,hsub⟩
  have joins : Merge src (bucket sites charge 6) := by
    intro w hw
    rcases choices w with h | ⟨j,h⟩ | ⟨paid,j,k,h⟩
    · have := small w h
      omega
    · refine Or.inl ⟨j, topo w j (by simp [h]), ?_⟩
      simpa [h] using lift w hw
    · refine Or.inr ⟨paid,j,topo w j (by simp [h]),k,topo w k (by simp [h]),?_⟩
      simpa [h] using lift w hw
  have witnesses (w : Nat) : ∀ e ∈ edges w, ∃ i ∈ src w,
      owner i = e.1.val ∧ e.2 ∈ lines e.1 (coeff i) := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro e he
      by_cases h : w ∈ born
      · exact ⟨w,(hmem w w).mpr ⟨h,.start w⟩,birth w h e he⟩
      · obtain ⟨j,hj,hedge⟩ := Finset.mem_biUnion.mp (branch w h he)
        obtain ⟨i,hi,rest⟩ := ih j (topo w j hj) e hedge
        obtain ⟨bor,prev⟩ := (hmem i j).mp hi
        exact ⟨i,(hmem i w).mpr ⟨bor,.next prev hj⟩,rest⟩
  have paid : src root ⊆ bucket sites charge 7 := by
    intro i hi
    exact bornPaid ((hmem i root).mp hi).1
  apply partialStarBudget sites charge owner coeff src lines root paid joins lineStep
  intro p
  apply (degrees p).trans
  apply Finset.card_le_card
  intro l hl
  obtain ⟨i,hi,ho,hline⟩ := witnesses root (p,l) (finalEdges p l hl)
  apply Finset.mem_biUnion.mpr
  exact ⟨coeff i,Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,ho⟩,rfl⟩,hline⟩
end PEqualNP.Outside.L_meta_9743.MultiBirth

import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32577

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Polynomial

private def IsMatching {α : Type*} [DecidableEq α] (V : Finset α) (M : Finset (Finset α)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ e ⊆ V) ∧
  (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂)

private instance {α : Type*} [DecidableEq α] (V : Finset α) (M : Finset (Finset α)) :
    Decidable (IsMatching V M) := by
  unfold IsMatching; infer_instance

private def matchFn {n : ℕ} (M : Finset (Finset (Fin n))) (x y : Fin n → Bool) : Bool :=
  decide ((∃ i : Fin n, x i = true ∧ y i = true) ∨
    (∃ e ∈ M, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)))

private def matchFnOn {n : ℕ} (S : Finset (Fin n)) (M : Finset (Finset (Fin n)))
    (x y : Fin n → Bool) : Bool :=
  decide ((∃ i ∈ S, x i = true ∧ y i = true) ∨
    (∃ e ∈ M, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)))

private lemma wires_append (g₁ g₂ : List Gate) (inp : List Bool) (o : ℕ) :
    (Circuit.mk (g₁ ++ g₂) o).wires inp = (Circuit.mk g₂ o).wires ((Circuit.mk g₁ o).wires inp) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_length (gs : List Gate) (inp : List Bool) (o : ℕ) :
    ((Circuit.mk gs o).wires inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma wires_getD_prefix (gs : List Gate) (inp : List Bool) (o k : ℕ) (hk : k < inp.length) :
    ((Circuit.mk gs o).wires inp).getD k false = inp.getD k false := by
  induction gs generalizing inp with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih (inp ++ [g.op.eval (g.inputs.map fun i => inp.getD i false)]) (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma wires_getD_step (gs : List Gate) (g : Gate) (inp : List Bool) (o : ℕ) :
    ((Circuit.mk (gs ++ [g]) o).wires inp).getD (inp.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => ((Circuit.mk gs o).wires inp).getD i false) := by
  rw [wires_append]
  set w := (Circuit.mk gs o).wires inp
  have hw : w.length = inp.length + gs.length := wires_length gs inp o
  simp only [Circuit.wires, List.foldl_cons, List.foldl_nil]
  rw [← hw]
  simp [List.getD_eq_getElem?_getD]

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires inp).getD (inp.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        if i < inp.length + j then (C.wires inp).getD i false else false) := by
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [List.append_assoc, List.singleton_append, ← h2, h1]
  have hlen : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
  have hstep : ((Circuit.mk (C.gates.take j ++ [C.gates[j]]) 0).wires inp).getD (inp.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
        ((Circuit.mk (C.gates.take j) 0).wires inp).getD i false) := by
    have hs := wires_getD_step (C.gates.take j) C.gates[j] inp 0
    rw [hlen] at hs; exact hs
  have hpref1 : (C.wires inp).getD (inp.length + j) false =
      ((Circuit.mk (C.gates.take j ++ [C.gates[j]]) 0).wires inp).getD (inp.length + j) false := by
    have heq : C.wires inp = (Circuit.mk ((C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1)) 0).wires inp := by
      simp only [Circuit.wires, ← hsplit]
    rw [heq, wires_append]
    exact wires_getD_prefix _ _ 0 _ (by rw [wires_length]; simp; omega)
  rw [hpref1, hstep]
  congr 1
  refine List.map_congr_left (fun i _ => ?_)
  by_cases hi : i < inp.length + j
  · simp only [hi, ↓reduceIte]
    have hpref2 : (C.wires inp).getD i false =
        ((Circuit.mk (C.gates.take j) 0).wires inp).getD i false := by
      have heq : C.wires inp = (Circuit.mk (C.gates.take j ++ C.gates.drop j) 0).wires inp := by
        simp only [Circuit.wires, List.take_append_drop]
      rw [heq, wires_append]
      exact wires_getD_prefix _ _ 0 _ (by rw [wires_length, hlen]; exact hi)
    exact hpref2.symm
  · simp only [hi, ↓reduceIte]
    have hlen2 : ((Circuit.mk (C.gates.take j) 0).wires inp).length = inp.length + j := by
      rw [wires_length, hlen]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

private lemma wires_getD_oob (C : Circuit) (inp : List Bool) (w : ℕ)
    (hw : inp.length + C.gates.length ≤ w) :
    (C.wires inp).getD w false = false := by
  have hlen : (C.wires inp).length = inp.length + C.gates.length := wires_length C.gates inp C.output
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

private lemma gateOp_mono (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (h1 : i < l₁.length) (h2 : i < l₂.length), l₁[i] ≤ l₂[i]) :
    op.eval l₁ ≤ op.eval l₂ := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    cases h1 : l₁.all id
    · exact Bool.false_le _
    · have h2 : l₂.all id = true := by
        rw [List.all_eq_true] at h1 ⊢
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
        have h1i : l₁[i]'(by omega) = true := h1 _ (List.getElem_mem _)
        have hle_i := hle i (by omega) hi
        rw [h1i] at hle_i
        exact Bool.eq_true_of_true_le hle_i
      rw [h2]
  · simp only [GateOp.eval]
    cases h1 : l₁.any id
    · exact Bool.false_le _
    · have h2 : l₂.any id = true := by
        rw [List.any_eq_true] at h1 ⊢
        rcases h1 with ⟨a, ha, ha_t⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
        refine ⟨l₂[i]'(by omega), List.getElem_mem _, ?_⟩
        have hle_i := hle i hi (by omega)
        simp only [id_eq] at ha_t ⊢
        rw [ha_t] at hle_i
        exact Bool.eq_true_of_true_le hle_i
      rw [h2]

private lemma monotone2_wires_mono (C : Circuit) (hM : Monotone2 C)
    {inp₁ inp₂ : List Bool} (hlen : inp₁.length = inp₂.length)
    (hle : ∀ i, inp₁.getD i false ≤ inp₂.getD i false) :
    ∀ w, (C.wires inp₁).getD w false ≤ (C.wires inp₂).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < inp₁.length
    · have hp1 := wires_getD_prefix C.gates inp₁ C.output w h1
      have hp2 := wires_getD_prefix C.gates inp₂ C.output w (by omega)
      rw [hp1, hp2]
      exact hle w
    · by_cases h2 : w < inp₁.length + C.gates.length
      · set j := w - inp₁.length
        have hj : j < C.gates.length := by omega
        have hw1 : w = inp₁.length + j := by omega
        have hw2 : w = inp₂.length + j := by omega
        rw [hw1, wires_getD_gate C inp₁ j hj]
        rw [← hw1, hw2, wires_getD_gate C inp₂ j hj]
        refine gateOp_mono (C.gates[j]).op (hM _ (List.getElem_mem hj)).1 (by simp) ?_
        intro idx hidx1 hidx2
        have hidx : idx < (C.gates[j]).inputs.length := by simpa using hidx1
        simp only [List.getElem_map]
        by_cases hlt : (C.gates[j]).inputs[idx]'hidx < inp₁.length + j
        · have hlt2 : (C.gates[j]).inputs[idx]'hidx < inp₂.length + j := by omega
          simp only [hlt, hlt2, ↓reduceIte]
          exact ih _ (by omega)
        · have hlt2 : ¬ (C.gates[j]).inputs[idx]'hidx < inp₂.length + j := by omega
          simp only [hlt, hlt2, ↓reduceIte]
          exact le_refl false
      · rw [wires_getD_oob C inp₁ w (by omega), wires_getD_oob C inp₂ w (by omega)]

private def gateParents (C : Circuit) (m w : ℕ) : Finset ℕ :=
  if h : m ≤ w ∧ w - m < C.gates.length then
    ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).toFinset
  else ∅

private lemma mem_gateParents_lt (C : Circuit) (m w u : ℕ) (hu : u ∈ gateParents C m w) : u < w := by
  unfold gateParents at hu
  split_ifs at hu with h
  · simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hu
    exact hu.2
  · simp at hu

private lemma gateParents_card_le (C : Circuit) (hM : Monotone2 C) (m w : ℕ) :
    (gateParents C m w).card ≤ 2 := by
  unfold gateParents
  split_ifs with h
  · have hlen := (hM _ (List.getElem_mem h.2)).2
    calc
      ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).toFinset.card
        ≤ ((C.gates[w - m]'(h.2)).inputs.filter (fun u => decide (u < w))).length := List.toFinset_card_le _
      _ ≤ (C.gates[w - m]'(h.2)).inputs.length := List.length_filter_le _ _
      _ ≤ 2 := hlen
  · simp

private def reach (C : Circuit) (m : ℕ) (w : ℕ) : Finset ℕ :=
  insert w ((gateParents C m w).attach.biUnion (fun u => reach C m u.1))
termination_by w
decreasing_by exact mem_gateParents_lt C m w u.1 u.2

private lemma reach_eq (C : Circuit) (m w : ℕ) :
    reach C m w = insert w ((gateParents C m w).biUnion (reach C m)) := by
  conv_lhs => rw [reach]
  ext x
  simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]

private lemma self_mem_reach (C : Circuit) (m w : ℕ) : w ∈ reach C m w := by
  rw [reach_eq]; exact Finset.mem_insert_self _ _

private lemma reach_subset_of_mem_gateParents (C : Circuit) (m w u : ℕ)
    (hu : u ∈ gateParents C m w) : reach C m u ⊆ reach C m w := by
  intro x hx
  rw [reach_eq]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hx⟩)

private lemma mem_reach_le (C : Circuit) (m w x : ℕ) (hx : x ∈ reach C m w) : x ≤ w := by
  induction w using Nat.strong_induction_on generalizing x with
  | ind w ih =>
    rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hx
    rcases hx with rfl | ⟨u, hu, hxu⟩
    · exact le_refl _
    · exact le_trans (ih u (mem_gateParents_lt C m w u hu) x hxu) (Nat.le_of_lt (mem_gateParents_lt C m w u hu))

private lemma reach_eq_on_wires (C : Circuit) (m : ℕ) {inp₁ inp₂ : List Bool}
    (h1 : inp₁.length = m) (h2 : inp₂.length = m) (w : ℕ)
    (hagree : ∀ i < m, i ∈ reach C m w → inp₁.getD i false = inp₂.getD i false) :
    (C.wires inp₁).getD w false = (C.wires inp₂).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < m
    · rw [wires_getD_prefix C.gates inp₁ C.output w (by omega),
          wires_getD_prefix C.gates inp₂ C.output w (by omega)]
      exact hagree w hw (self_mem_reach C m w)
    · by_cases hw2 : w < m + C.gates.length
      · set j := w - m
        have hj : j < C.gates.length := by omega
        have hwm1 : w = inp₁.length + j := by omega
        have hwm2 : w = inp₂.length + j := by omega
        rw [hwm1, wires_getD_gate C inp₁ j hj]
        rw [← hwm1, hwm2, wires_getD_gate C inp₂ j hj]
        congr 1
        refine List.map_congr_left (fun u hu => ?_)
        by_cases hlt : u < w
        · have hlt1 : u < inp₁.length + j := by omega
          have hlt2 : u < inp₂.length + j := by omega
          simp only [hlt1, hlt2, ↓reduceIte]
          have hup : u ∈ gateParents C m w := by
            unfold gateParents
            have hcond : m ≤ w ∧ w - m < C.gates.length := ⟨by omega, hj⟩
            rw [dif_pos hcond]
            simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
            exact ⟨hu, hlt⟩
          exact ih u hlt (fun i him hi => hagree i him (reach_subset_of_mem_gateParents C m w u hup hi))
        · have hlt1 : ¬ u < inp₁.length + j := by omega
          have hlt2 : ¬ u < inp₂.length + j := by omega
          simp only [hlt1, hlt2, ↓reduceIte]
      · rw [wires_getD_oob C inp₁ w (by omega), wires_getD_oob C inp₂ w (by omega)]

private lemma biUnion_card_eq_sum_iff_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card = ∑ a ∈ s, (f a).card →
    ∀ a₁ ∈ s, ∀ a₂ ∈ s, a₁ ≠ a₂ → Disjoint (f a₁) (f a₂) := by
  intro heq a₁ ha₁ a₂ ha₂ hne
  by_contra hnd
  rw [Finset.not_disjoint_iff] at hnd
  rcases hnd with ⟨b, hb1, hb2⟩
  have hsub : s.biUnion f = (f a₁ ∪ f a₂) ∪ ((s.erase a₁).erase a₂).biUnion f := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro ⟨a, ha, hxa⟩
      by_cases h1 : a = a₁
      · left; left; rwa [← h1]
      · by_cases h2 : a = a₂
        · left; right; rwa [← h2]
        · right; exact ⟨a, ⟨h2, h1, ha⟩, hxa⟩
    · rintro ((hx | hx) | ⟨a, ⟨_, _, ha⟩, hxa⟩)
      · exact ⟨a₁, ha₁, hx⟩
      · exact ⟨a₂, ha₂, hx⟩
      · exact ⟨a, ha, hxa⟩
  have hlt : (f a₁ ∪ f a₂).card < (f a₁).card + (f a₂).card := by
    have hpos : 0 < (f a₁ ∩ f a₂).card := Finset.card_pos.mpr ⟨b, Finset.mem_inter.mpr ⟨hb1, hb2⟩⟩
    have hu := Finset.card_union_add_card_inter (f a₁) (f a₂)
    omega
  have hsum : ∑ a ∈ s, (f a).card =
      (f a₁).card + (f a₂).card + ∑ a ∈ (s.erase a₁).erase a₂, (f a).card := by
    have h1 := Finset.add_sum_erase s (fun a => (f a).card) ha₁
    have ha₂' : a₂ ∈ s.erase a₁ := Finset.mem_erase.mpr ⟨hne.symm, ha₂⟩
    have h2 := Finset.add_sum_erase (s.erase a₁) (fun a => (f a).card) ha₂'
    omega
  have hle : (s.biUnion f).card ≤ (f a₁ ∪ f a₂).card + ∑ a ∈ (s.erase a₁).erase a₂, (f a).card := by
    rw [hsub]
    exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left (Finset.card_biUnion_le) _)
  omega

private inductive MTree (n : ℕ) where
  | leafL (i : Fin n)
  | leafR (i : Fin n)
  | and (t₁ t₂ : MTree n)
  | or (t₁ t₂ : MTree n)

private def MTree.eval {n : ℕ} : MTree n → (Fin n → Bool) → (Fin n → Bool) → Bool
  | .leafL i, x, _ => x i
  | .leafR i, _, y => y i
  | .and t₁ t₂, x, y => t₁.eval x y && t₂.eval x y
  | .or t₁ t₂, x, y => t₁.eval x y || t₂.eval x y

private def MTree.vars {n : ℕ} : MTree n → Finset (Fin n ⊕ Fin n)
  | .leafL i => {Sum.inl i}
  | .leafR i => {Sum.inr i}
  | .and t₁ t₂ => t₁.vars ∪ t₂.vars
  | .or t₁ t₂ => t₁.vars ∪ t₂.vars

private def MTree.ReadOnce {n : ℕ} : MTree n → Prop
  | .leafL _ => True
  | .leafR _ => True
  | .and t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧ Disjoint t₁.vars t₂.vars
  | .or t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧ Disjoint t₁.vars t₂.vars

private lemma MTree.vars_nonempty {n : ℕ} (t : MTree n) : t.vars.Nonempty := by
  induction t with
  | leafL i => exact ⟨Sum.inl i, Finset.mem_singleton_self _⟩
  | leafR i => exact ⟨Sum.inr i, Finset.mem_singleton_self _⟩
  | and _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left
  | or _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left

private lemma MTree.eval_zero {n : ℕ} (t : MTree n) :
    t.eval (fun _ => false) (fun _ => false) = false := by
  induction t with
  | leafL _ => rfl
  | leafR _ => rfl
  | and _ _ ih₁ ih₂ => simp [MTree.eval, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [MTree.eval, ih₁, ih₂]

private lemma MTree.eval_eq_of_eq_on_vars {n : ℕ} (t : MTree n) {x₁ x₂ y₁ y₂ : Fin n → Bool}
    (hx : ∀ i, Sum.inl i ∈ t.vars → x₁ i = x₂ i)
    (hy : ∀ i, Sum.inr i ∈ t.vars → y₁ i = y₂ i) :
    t.eval x₁ y₁ = t.eval x₂ y₂ := by
  induction t with
  | leafL i => exact hx i (Finset.mem_singleton_self _)
  | leafR i => exact hy i (Finset.mem_singleton_self _)
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    rw [ih₁ (fun i hi => hx i (Finset.mem_union_left _ hi))
            (fun i hi => hy i (Finset.mem_union_left _ hi)),
        ih₂ (fun i hi => hx i (Finset.mem_union_right _ hi))
            (fun i hi => hy i (Finset.mem_union_right _ hi))]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    rw [ih₁ (fun i hi => hx i (Finset.mem_union_left _ hi))
            (fun i hi => hy i (Finset.mem_union_left _ hi)),
        ih₂ (fun i hi => hx i (Finset.mem_union_right _ hi))
            (fun i hi => hy i (Finset.mem_union_right _ hi))]

private lemma MTree.eval_mono {n : ℕ} (t : MTree n) {x₁ x₂ y₁ y₂ : Fin n → Bool}
    (hx : ∀ i, x₁ i ≤ x₂ i) (hy : ∀ i, y₁ i ≤ y₂ i) :
    t.eval x₁ y₁ ≤ t.eval x₂ y₂ := by
  induction t with
  | leafL i => exact hx i
  | leafR i => exact hy i
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    cases h1 : t₁.eval x₁ y₁ <;> cases h2 : t₂.eval x₁ y₁
    · simp
    · simp
    · simp
    · rw [h1] at ih₁; rw [h2] at ih₂
      rw [Bool.eq_true_of_true_le ih₁, Bool.eq_true_of_true_le ih₂]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [MTree.eval]
    cases h1 : t₁.eval x₁ y₁ <;> cases h2 : t₂.eval x₁ y₁
    · simp
    · rw [h2] at ih₂; rw [Bool.eq_true_of_true_le ih₂]; simp
    · rw [h1] at ih₁; rw [Bool.eq_true_of_true_le ih₁]; simp
    · rw [h1] at ih₁; rw [Bool.eq_true_of_true_le ih₁]; simp

private def unitVec {n : ℕ} (i : Fin n) : Fin n → Bool := fun k => decide (k = i)

private lemma MTree.all_unit_true_is_or {n : ℕ} (t : MTree n) (hro : t.ReadOnce)
    (hL : ∀ i, Sum.inl i ∈ t.vars → t.eval (unitVec i) (fun _ => false) = true)
    (hR : ∀ i, Sum.inr i ∈ t.vars → t.eval (fun _ => false) (unitVec i) = true) :
    ∀ x y, t.eval x y =
      decide ((∃ i, Sum.inl i ∈ t.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t.vars ∧ y i = true)) := by
  induction t with
  | leafL i =>
    intro x y
    simp only [MTree.eval, MTree.vars, Finset.mem_singleton, Sum.inl.injEq,
      exists_eq_left, reduceCtorEq, false_and, exists_false, or_false, decide_eq_true_iff]
    cases x i <;> decide
  | leafR i =>
    intro x y
    simp only [MTree.eval, MTree.vars, Finset.mem_singleton, reduceCtorEq, false_and,
      exists_false, Sum.inr.injEq, exists_eq_left, false_or, decide_eq_true_iff]
    cases y i <;> decide
  | and t₁ t₂ _ _ =>
    exfalso
    rcases t₁.vars_nonempty with ⟨v, hv⟩
    have hv2 : v ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hv
    cases v with
    | inl i =>
      have ht := hL i (Finset.mem_union_left _ hv)
      simp only [MTree.eval, Bool.and_eq_true] at ht
      have h0 : t₂.eval (unitVec i) (fun _ => false) = t₂.eval (fun _ => false) (fun _ => false) := by
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => hv2 (h ▸ hj)
        simp [unitVec, hji]
      rw [h0, t₂.eval_zero] at ht
      exact Bool.false_ne_true ht.2
    | inr i =>
      have ht := hR i (Finset.mem_union_left _ hv)
      simp only [MTree.eval, Bool.and_eq_true] at ht
      have h0 : t₂.eval (fun _ => false) (unitVec i) = t₂.eval (fun _ => false) (fun _ => false) := by
        refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => hv2 (h ▸ hj)
        simp [unitVec, hji]
      rw [h0, t₂.eval_zero] at ht
      exact Bool.false_ne_true ht.2
  | or t₁ t₂ ih₁ ih₂ =>
    have hL₁ : ∀ i, Sum.inl i ∈ t₁.vars → t₁.eval (unitVec i) (fun _ => false) = true := by
      intro i hi
      have ht := hL i (Finset.mem_union_left _ hi)
      have hi2 : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hi
      have h0 : t₂.eval (unitVec i) (fun _ => false) = false := by
        refine (t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)).trans t₂.eval_zero
        have hji : j ≠ i := fun h => hi2 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hR₁ : ∀ i, Sum.inr i ∈ t₁.vars → t₁.eval (fun _ => false) (unitVec i) = true := by
      intro i hi
      have ht := hR i (Finset.mem_union_left _ hi)
      have hi2 : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 hi
      have h0 : t₂.eval (fun _ => false) (unitVec i) = false := by
        refine (t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)).trans t₂.eval_zero
        have hji : j ≠ i := fun h => hi2 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hL₂ : ∀ i, Sum.inl i ∈ t₂.vars → t₂.eval (unitVec i) (fun _ => false) = true := by
      intro i hi
      have ht := hL i (Finset.mem_union_right _ hi)
      have hi1 : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
      have h0 : t₁.eval (unitVec i) (fun _ => false) = false := by
        refine (t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)).trans t₁.eval_zero
        have hji : j ≠ i := fun h => hi1 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    have hR₂ : ∀ i, Sum.inr i ∈ t₂.vars → t₂.eval (fun _ => false) (unitVec i) = true := by
      intro i hi
      have ht := hR i (Finset.mem_union_right _ hi)
      have hi1 : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
      have h0 : t₁.eval (fun _ => false) (unitVec i) = false := by
        refine (t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)).trans t₁.eval_zero
        have hji : j ≠ i := fun h => hi1 (h ▸ hj)
        simp [unitVec, hji]
      simp [MTree.eval, h0] at ht
      exact ht
    intro x y
    simp only [MTree.eval, ih₁ hro.1 hL₁ hR₁ x y, ih₂ hro.2.1 hL₂ hR₂ x y, MTree.vars,
      Finset.mem_union]
    by_cases h : (∃ i, (Sum.inl i ∈ t₁.vars ∨ Sum.inl i ∈ t₂.vars) ∧ x i = true) ∨
        (∃ i, (Sum.inr i ∈ t₁.vars ∨ Sum.inr i ∈ t₂.vars) ∧ y i = true)
    · rw [decide_eq_true h]
      rcases h with ⟨i, hi | hi, hxi⟩ | ⟨i, hi | hi, hyi⟩
      · have : decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inl ⟨i, hi, hxi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inl ⟨i, hi, hxi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inr ⟨i, hi, hyi⟩)
        simp [this]
      · have : decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) = true :=
          decide_eq_true (Or.inr ⟨i, hi, hyi⟩)
        simp [this]
    · rw [decide_eq_false h]
      have h1 : ¬ ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) := by
        rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hyi⟩)
        · exact h (Or.inl ⟨i, Or.inl hi, hxi⟩)
        · exact h (Or.inr ⟨i, Or.inl hi, hyi⟩)
      have h2 : ¬ ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) := by
        rintro (⟨i, hi, hxi⟩ | ⟨i, hi, hyi⟩)
        · exact h (Or.inl ⟨i, Or.inr hi, hxi⟩)
        · exact h (Or.inr ⟨i, Or.inr hi, hyi⟩)
      simp [decide_eq_false h1, decide_eq_false h2]

private lemma classify_mtree {n : ℕ} :
    ∀ (t : MTree n) (S : Finset (Fin n)),
      S.Nonempty →
      t.ReadOnce →
      (∀ i, Sum.inl i ∈ t.vars ↔ i ∈ S) →
      (∀ i, Sum.inr i ∈ t.vars ↔ i ∈ S) →
      (∀ i ∈ S, t.eval (unitVec i) (unitVec i) = true) →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → t.eval (unitVec i) (unitVec j) = false) →
      (∀ i ∈ S, t.eval (unitVec i) (fun _ => false) = false ∧
                t.eval (fun _ => false) (unitVec i) = false) →
      ∃ M : Finset (Finset (Fin n)), IsMatching S M ∧
        ∀ x y, t.eval x y = matchFnOn S M x y := by
  intro t
  induction t with
  | leafL i =>
    intro S hS _ hL hR _ _ hzero
    have hi : i ∈ S := (hL i).mp (Finset.mem_singleton_self _)
    have h0 := (hzero i hi).1
    simp [MTree.eval, unitVec] at h0
  | leafR i =>
    intro S hS _ hL hR _ _ hzero
    have hi : i ∈ S := (hR i).mp (Finset.mem_singleton_self _)
    have h0 := (hzero i hi).2
    simp [MTree.eval, unitVec] at h0
  | or t₁ t₂ ih₁ ih₂ =>
    intro S hS hro hL hR hdiag hoff hzero
    have hsame : ∀ i ∈ S, Sum.inl i ∈ t₁.vars ↔ Sum.inr i ∈ t₁.vars := by
      intro i hi
      have hL_in : Sum.inl i ∈ t₁.vars ∨ Sum.inl i ∈ t₂.vars := Finset.mem_union.mp ((hL i).mpr hi)
      have hR_in : Sum.inr i ∈ t₁.vars ∨ Sum.inr i ∈ t₂.vars := Finset.mem_union.mp ((hR i).mpr hi)
      have h10 : t₁.eval (unitVec i) (fun _ => false) = false := by
        have h := (hzero i hi).1; simp [MTree.eval] at h; exact h.1
      have h01 : t₁.eval (fun _ => false) (unitVec i) = false := by
        have h := (hzero i hi).2; simp [MTree.eval] at h; exact h.1
      have h20 : t₂.eval (unitVec i) (fun _ => false) = false := by
        have h := (hzero i hi).1; simp [MTree.eval] at h; exact h.2
      have h02 : t₂.eval (fun _ => false) (unitVec i) = false := by
        have h := (hzero i hi).2; simp [MTree.eval] at h; exact h.2
      constructor
      · intro h1L
        by_contra h1R
        have h2L : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 h1L
        have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← h10]
          refine t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
          have hji : j ≠ i := fun h => h1R (h ▸ hj)
          simp [unitVec, hji]
        have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← h02]
          refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
          have hji : j ≠ i := fun h => h2L (h ▸ hj)
          simp [unitVec, hji]
        have hd := hdiag i hi
        simp [MTree.eval, he1, he2] at hd
      · intro h1R
        by_contra h1L
        have h2R : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 h1R
        have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← h01]
          refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
          have hji : j ≠ i := fun h => h1L (h ▸ hj)
          simp [unitVec, hji]
        have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← h20]
          refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
          have hji : j ≠ i := fun h => h2R (h ▸ hj)
          simp [unitVec, hji]
        have hd := hdiag i hi
        simp [MTree.eval, he1, he2] at hd
    let S₁ := S.filter (fun i => decide (Sum.inl i ∈ t₁.vars))
    let S₂ := S.filter (fun i => decide (Sum.inl i ∈ t₂.vars))
    have hL₁ : ∀ i, Sum.inl i ∈ t₁.vars ↔ i ∈ S₁ := by
      intro i
      simp only [S₁, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun hi => ⟨(hL i).mp (Finset.mem_union_left _ hi), hi⟩, And.right⟩
    have hR₁ : ∀ i, Sum.inr i ∈ t₁.vars ↔ i ∈ S₁ := by
      intro i
      constructor
      · intro hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_left _ hi)
        exact (hL₁ i).mp ((hsame i hiS).mpr hi)
      · intro hi
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        exact (hsame i hiS).mp ((hL₁ i).mpr hi)
    have hL₂ : ∀ i, Sum.inl i ∈ t₂.vars ↔ i ∈ S₂ := by
      intro i
      simp only [S₂, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun hi => ⟨(hL i).mp (Finset.mem_union_right _ hi), hi⟩, And.right⟩
    have hR₂ : ∀ i, Sum.inr i ∈ t₂.vars ↔ i ∈ S₂ := by
      intro i
      constructor
      · intro hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_right _ hi)
        have h1R : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hi
        have h1L : Sum.inl i ∉ t₁.vars := fun h => h1R ((hsame i hiS).mp h)
        have h2L : Sum.inl i ∈ t₂.vars := (Finset.mem_union.mp ((hL i).mpr hiS)).resolve_left h1L
        exact (hL₂ i).mp h2L
      · intro hi
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        have h2L : Sum.inl i ∈ t₂.vars := (hL₂ i).mpr hi
        have h1L : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 h2L
        have h1R : Sum.inr i ∉ t₁.vars := fun h => h1L ((hsame i hiS).mpr h)
        exact (Finset.mem_union.mp ((hR i).mpr hiS)).resolve_left h1R
    have hS₁_ne : S₁.Nonempty := by
      rcases t₁.vars_nonempty with ⟨v, hv⟩
      cases v with
      | inl i => exact ⟨i, (hL₁ i).mp hv⟩
      | inr i => exact ⟨i, (hR₁ i).mp hv⟩
    have hS₂_ne : S₂.Nonempty := by
      rcases t₂.vars_nonempty with ⟨v, hv⟩
      cases v with
      | inl i => exact ⟨i, (hL₂ i).mp hv⟩
      | inr i => exact ⟨i, (hR₂ i).mp hv⟩
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact Finset.disjoint_left.mp hro.2.2 ((hL₁ i).mpr h1) ((hL₂ i).mpr h2)
    have hunion : S₁ ∪ S₂ = S := by
      ext i
      rw [Finset.mem_union, ← hL₁, ← hL₂, ← Finset.mem_union, ← hL]
      rfl
    have hd₁ : ∀ i ∈ S₁, t₁.eval (unitVec i) (unitVec i) = true := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have h2L : Sum.inl i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 ((hL₁ i).mpr hi)
      have h2R : Sum.inr i ∉ t₂.vars := Finset.disjoint_left.mp hro.2.2 ((hR₁ i).mpr hi)
      have he2 : t₂.eval (unitVec i) (unitVec i) = false := by
        rw [← t₂.eval_zero]
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
        · have hji : j ≠ i := fun h => h2L (h ▸ hj)
          simp [unitVec, hji]
        · have hji : j ≠ i := fun h => h2R (h ▸ hj)
          simp [unitVec, hji]
      have hd := hdiag i hiS
      simp [MTree.eval, he2] at hd
      exact hd
    have hd₂ : ∀ i ∈ S₂, t₂.eval (unitVec i) (unitVec i) = true := by
      intro i hi
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
      have h1L : Sum.inl i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 ((hL₂ i).mpr hi)
      have h1R : Sum.inr i ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 ((hR₂ i).mpr hi)
      have he1 : t₁.eval (unitVec i) (unitVec i) = false := by
        rw [← t₁.eval_zero]
        refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
        · have hji : j ≠ i := fun h => h1L (h ▸ hj)
          simp [unitVec, hji]
        · have hji : j ≠ i := fun h => h1R (h ▸ hj)
          simp [unitVec, hji]
      have hd := hdiag i hiS
      simp [MTree.eval, he1] at hd
      exact hd
    have ho₁ : ∀ i ∈ S₁, ∀ j ∈ S₁, i ≠ j → t₁.eval (unitVec i) (unitVec j) = false := by
      intro i hi j hj hne
      have h := hoff i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne
      simp [MTree.eval] at h; exact h.1
    have ho₂ : ∀ i ∈ S₂, ∀ j ∈ S₂, i ≠ j → t₂.eval (unitVec i) (unitVec j) = false := by
      intro i hi j hj hne
      have h := hoff i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne
      simp [MTree.eval] at h; exact h.2
    have hz₁ : ∀ i ∈ S₁, t₁.eval (unitVec i) (fun _ => false) = false ∧
        t₁.eval (fun _ => false) (unitVec i) = false := by
      intro i hi
      have h := hzero i (Finset.mem_filter.mp hi).1
      simp [MTree.eval] at h
      exact ⟨h.1.1, h.2.1⟩
    have hz₂ : ∀ i ∈ S₂, t₂.eval (unitVec i) (fun _ => false) = false ∧
        t₂.eval (fun _ => false) (unitVec i) = false := by
      intro i hi
      have h := hzero i (Finset.mem_filter.mp hi).1
      simp [MTree.eval] at h
      exact ⟨h.1.2, h.2.2⟩
    obtain ⟨M₁, hM₁, hev₁⟩ := ih₁ S₁ hS₁_ne hro.1 hL₁ hR₁ hd₁ ho₁ hz₁
    obtain ⟨M₂, hM₂, hev₂⟩ := ih₂ S₂ hS₂_ne hro.2.1 hL₂ hR₂ hd₂ ho₂ hz₂
    refine ⟨M₁ ∪ M₂, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with he1 | he2
        · exact ⟨(hM₁.1 e he1).1, (hM₁.1 e he1).2.trans (hunion ▸ Finset.subset_union_left)⟩
        · exact ⟨(hM₂.1 e he2).1, (hM₂.1 e he2).2.trans (hunion ▸ Finset.subset_union_right)⟩
      · intro e₁ he₁ e₂ he₂ hne
        rcases Finset.mem_union.mp he₁ with h1 | h1 <;> rcases Finset.mem_union.mp he₂ with h2 | h2
        · exact hM₁.2 e₁ h1 e₂ h2 hne
        · exact Disjoint.mono (hM₁.1 e₁ h1).2 (hM₂.1 e₂ h2).2 hdisj
        · exact Disjoint.mono (hM₂.1 e₁ h1).2 (hM₁.1 e₂ h2).2 hdisj.symm
        · exact hM₂.2 e₁ h1 e₂ h2 hne
    · intro x y
      simp only [MTree.eval, hev₁ x y, hev₂ x y, matchFnOn]
      rw [← hunion]
      by_cases h : (∃ i ∈ S₁ ∪ S₂, x i = true ∧ y i = true) ∨
          (∃ e ∈ M₁ ∪ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))
      · rw [decide_eq_true h]
        rcases h with ⟨i, hi, hxi, hyi⟩ | ⟨e, he, hex⟩
        · rcases Finset.mem_union.mp hi with hi1 | hi2
          · have : decide ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inl ⟨i, hi1, hxi, hyi⟩)
            simp [this]
          · have : decide ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inl ⟨i, hi2, hxi, hyi⟩)
            simp [this]
        · rcases Finset.mem_union.mp he with he1 | he2
          · have : decide ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inr ⟨e, he1, hex⟩)
            simp [this]
          · have : decide ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
                (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) = true :=
              decide_eq_true (Or.inr ⟨e, he2, hex⟩)
            simp [this]
      · rw [decide_eq_false h]
        have h1 : ¬ ((∃ i ∈ S₁, x i = true ∧ y i = true) ∨
            (∃ e ∈ M₁, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          rintro (⟨i, hi, hxy⟩ | ⟨e, he, hex⟩)
          · exact h (Or.inl ⟨i, Finset.mem_union_left _ hi, hxy⟩)
          · exact h (Or.inr ⟨e, Finset.mem_union_left _ he, hex⟩)
        have h2 : ¬ ((∃ i ∈ S₂, x i = true ∧ y i = true) ∨
            (∃ e ∈ M₂, (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          rintro (⟨i, hi, hxy⟩ | ⟨e, he, hex⟩)
          · exact h (Or.inl ⟨i, Finset.mem_union_right _ hi, hxy⟩)
          · exact h (Or.inr ⟨e, Finset.mem_union_right _ he, hex⟩)
        simp [decide_eq_false h1, decide_eq_false h2]
  | and t₁ t₂ _ _ =>
    intro S hS hro hL hR hdiag hoff _
    have hboth : ∀ i ∈ S, (Sum.inl i ∈ t₁.vars ∨ Sum.inr i ∈ t₁.vars) ∧
        (Sum.inl i ∈ t₂.vars ∨ Sum.inr i ∈ t₂.vars) := by
      intro i hi
      have hd := hdiag i hi
      simp only [MTree.eval, Bool.and_eq_true] at hd
      constructor
      · by_contra hno
        push_neg at hno
        have h0 : t₁.eval (unitVec i) (unitVec i) = false := by
          rw [← t₁.eval_zero]
          refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun h => hno.1 (h ▸ hj); simp [unitVec, hji]
          · have hji : j ≠ i := fun h => hno.2 (h ▸ hj); simp [unitVec, hji]
        exact Bool.false_ne_true (h0.symm.trans hd.1)
      · by_contra hno
        push_neg at hno
        have h0 : t₂.eval (unitVec i) (unitVec i) = false := by
          rw [← t₂.eval_zero]
          refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun j hj => ?_)
          · have hji : j ≠ i := fun h => hno.1 (h ▸ hj); simp [unitVec, hji]
          · have hji : j ≠ i := fun h => hno.2 (h ▸ hj); simp [unitVec, hji]
        exact Bool.false_ne_true (h0.symm.trans hd.2)
    have hexact : ∀ i ∈ S,
        (Sum.inl i ∈ t₁.vars ∧ Sum.inr i ∉ t₁.vars ∧ Sum.inl i ∉ t₂.vars ∧ Sum.inr i ∈ t₂.vars) ∨
        (Sum.inl i ∉ t₁.vars ∧ Sum.inr i ∈ t₁.vars ∧ Sum.inl i ∈ t₂.vars ∧ Sum.inr i ∉ t₂.vars) := by
      intro i hi
      rcases hboth i hi with ⟨h1L | h1R, h2L | h2R⟩
      · exact absurd h2L (Finset.disjoint_left.mp hro.2.2 h1L)
      · left
        exact ⟨h1L, Finset.disjoint_right.mp hro.2.2 h2R, Finset.disjoint_left.mp hro.2.2 h1L, h2R⟩
      · right
        exact ⟨Finset.disjoint_right.mp hro.2.2 h2L, h1R, h2L, Finset.disjoint_left.mp hro.2.2 h1R⟩
      · exact absurd h2R (Finset.disjoint_left.mp hro.2.2 h1R)
    have ht₁_or : ∀ x y, t₁.eval x y =
        decide ((∃ i, Sum.inl i ∈ t₁.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₁.vars ∧ y i = true)) := by
      refine t₁.all_unit_true_is_or hro.1 ?_ ?_
      · intro i hi
        have hiS : i ∈ S := (hL i).mp (Finset.mem_union_left _ hi)
        have h1R : Sum.inr i ∉ t₁.vars := by
          rcases hexact i hiS with ⟨_, h1R, _, _⟩ | ⟨h1L, _, _, _⟩
          · exact h1R
          · exact absurd hi h1L
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.1]
        refine t₁.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => h1R (h ▸ hj)
        simp [unitVec, hji]
      · intro i hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_left _ hi)
        have h1L : Sum.inl i ∉ t₁.vars := by
          rcases hexact i hiS with ⟨_, h1R, _, _⟩ | ⟨h1L, _, _, _⟩
          · exact absurd hi h1R
          · exact h1L
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.1]
        refine t₁.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => h1L (h ▸ hj)
        simp [unitVec, hji]
    have ht₂_or : ∀ x y, t₂.eval x y =
        decide ((∃ i, Sum.inl i ∈ t₂.vars ∧ x i = true) ∨ (∃ i, Sum.inr i ∈ t₂.vars ∧ y i = true)) := by
      refine t₂.all_unit_true_is_or hro.2.1 ?_ ?_
      · intro i hi
        have hiS : i ∈ S := (hL i).mp (Finset.mem_union_right _ hi)
        have h2R : Sum.inr i ∉ t₂.vars := by
          rcases hexact i hiS with ⟨_, _, h2L, _⟩ | ⟨_, _, _, h2R⟩
          · exact absurd hi h2L
          · exact h2R
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.2]
        refine t₂.eval_eq_of_eq_on_vars (fun _ _ => rfl) (fun j hj => ?_)
        have hji : j ≠ i := fun h => h2R (h ▸ hj)
        simp [unitVec, hji]
      · intro i hi
        have hiS : i ∈ S := (hR i).mp (Finset.mem_union_right _ hi)
        have h2L : Sum.inl i ∉ t₂.vars := by
          rcases hexact i hiS with ⟨_, _, h2L, _⟩ | ⟨_, _, _, h2R⟩
          · exact h2L
          · exact absurd hi h2R
        have hd := (Bool.and_eq_true _ _).mp (hdiag i hiS)
        rw [← hd.2]
        refine t₂.eval_eq_of_eq_on_vars (fun j hj => ?_) (fun _ _ => rfl)
        have hji : j ≠ i := fun h => h2L (h ▸ hj)
        simp [unitVec, hji]
    have huniqL : ∀ i ∈ S, ∀ j ∈ S, Sum.inl i ∈ t₁.vars → Sum.inl j ∈ t₁.vars → i = j := by
      intro i hi j hj hi1 hj1
      by_contra hne
      have hj2R : Sum.inr j ∈ t₂.vars := by
        rcases hexact j hj with ⟨_, _, _, h2R⟩ | ⟨h1L, _, _, _⟩
        · exact h2R
        · exact absurd hj1 h1L
      have h := hoff i hi j hj hne
      simp only [MTree.eval, ht₁_or, ht₂_or] at h
      have h1t : decide ((∃ k, Sum.inl k ∈ t₁.vars ∧ unitVec i k = true) ∨
          (∃ k, Sum.inr k ∈ t₁.vars ∧ unitVec j k = true)) = true :=
        decide_eq_true (Or.inl ⟨i, hi1, by simp [unitVec]⟩)
      have h2t : decide ((∃ k, Sum.inl k ∈ t₂.vars ∧ unitVec i k = true) ∨
          (∃ k, Sum.inr k ∈ t₂.vars ∧ unitVec j k = true)) = true :=
        decide_eq_true (Or.inr ⟨j, hj2R, by simp [unitVec]⟩)
      rw [h1t, h2t] at h
      exact Bool.false_ne_true.symm h
    have huniqR : ∀ i ∈ S, ∀ j ∈ S, Sum.inr i ∈ t₁.vars → Sum.inr j ∈ t₁.vars → i = j := by
      intro i hi j hj hi1 hj1
      by_contra hne
      have hj2L : Sum.inl j ∈ t₂.vars := by
        rcases hexact j hj with ⟨_, h1R, _, _⟩ | ⟨_, _, h2L, _⟩
        · exact absurd hj1 h1R
        · exact h2L
      have h := hoff j hj i hi (Ne.symm hne)
      simp only [MTree.eval, ht₁_or, ht₂_or] at h
      have h1t : decide ((∃ k, Sum.inl k ∈ t₁.vars ∧ unitVec j k = true) ∨
          (∃ k, Sum.inr k ∈ t₁.vars ∧ unitVec i k = true)) = true :=
        decide_eq_true (Or.inr ⟨i, hi1, by simp [unitVec]⟩)
      have h2t : decide ((∃ k, Sum.inl k ∈ t₂.vars ∧ unitVec j k = true) ∨
          (∃ k, Sum.inr k ∈ t₂.vars ∧ unitVec i k = true)) = true :=
        decide_eq_true (Or.inl ⟨j, hj2L, by simp [unitVec]⟩)
      rw [h1t, h2t] at h
      exact Bool.false_ne_true.symm h
    by_cases hcard : S.card = 1
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
      refine ⟨∅, ⟨by simp, by simp⟩, ?_⟩
      intro x y
      simp only [MTree.eval, ht₁_or, ht₂_or, matchFnOn, Finset.mem_singleton, Finset.notMem_empty,
        false_and, exists_false, or_false]
      have ha_vars : ∀ k, Sum.inl k ∈ t₁.vars ∨ Sum.inr k ∈ t₁.vars → k = a := by
        intro k hk
        rcases hk with h1 | h1
        · exact Finset.mem_singleton.mp ((hL k).mp (Finset.mem_union_left _ h1))
        · exact Finset.mem_singleton.mp ((hR k).mp (Finset.mem_union_left _ h1))
      have ha_vars2 : ∀ k, Sum.inl k ∈ t₂.vars ∨ Sum.inr k ∈ t₂.vars → k = a := by
        intro k hk
        rcases hk with h1 | h1
        · exact Finset.mem_singleton.mp ((hL k).mp (Finset.mem_union_right _ h1))
        · exact Finset.mem_singleton.mp ((hR k).mp (Finset.mem_union_right _ h1))
      rcases hexact a (Finset.mem_singleton_self a) with ⟨h1L, h1R, h2L, h2R⟩ | ⟨h1L, h1R, h2L, h2R⟩
      · have he1 : ((∃ k, Sum.inl k ∈ t₁.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₁.vars ∧ y k = true)) ↔
            x a = true := by
          constructor
          · rintro (⟨k, hk, hxk⟩ | ⟨k, hk, _⟩)
            · rwa [← ha_vars k (Or.inl hk)]
            · exact absurd (ha_vars k (Or.inr hk) ▸ hk) h1R
          · intro hx; exact Or.inl ⟨a, h1L, hx⟩
        have he2 : ((∃ k, Sum.inl k ∈ t₂.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₂.vars ∧ y k = true)) ↔
            y a = true := by
          constructor
          · rintro (⟨k, hk, _⟩ | ⟨k, hk, hyk⟩)
            · exact absurd (ha_vars2 k (Or.inl hk) ▸ hk) h2L
            · rwa [← ha_vars2 k (Or.inr hk)]
          · intro hy; exact Or.inr ⟨a, h2R, hy⟩
        simp only [he1, he2, exists_eq_left]
        cases x a <;> cases y a <;> decide
      · have he1 : ((∃ k, Sum.inl k ∈ t₁.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₁.vars ∧ y k = true)) ↔
            y a = true := by
          constructor
          · rintro (⟨k, hk, _⟩ | ⟨k, hk, hyk⟩)
            · exact absurd (ha_vars k (Or.inl hk) ▸ hk) h1L
            · rwa [← ha_vars k (Or.inr hk)]
          · intro hy; exact Or.inr ⟨a, h1R, hy⟩
        have he2 : ((∃ k, Sum.inl k ∈ t₂.vars ∧ x k = true) ∨ (∃ k, Sum.inr k ∈ t₂.vars ∧ y k = true)) ↔
            x a = true := by
          constructor
          · rintro (⟨k, hk, hxk⟩ | ⟨k, hk, _⟩)
            · rwa [← ha_vars2 k (Or.inl hk)]
            · exact absurd (ha_vars2 k (Or.inr hk) ▸ hk) h2R
          · intro hx; exact Or.inl ⟨a, h2L, hx⟩
        simp only [he1, he2, exists_eq_left]
        cases x a <;> cases y a <;> decide
    · have hge2 : 2 ≤ S.card := by
        have hpos : 0 < S.card := hS.card_pos
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
      have hpair : ∃ u v, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧
          Sum.inl u ∈ t₁.vars ∧ Sum.inr v ∈ t₁.vars ∧
          Sum.inr u ∈ t₂.vars ∧ Sum.inl v ∈ t₂.vars := by
        rcases hexact a ha with ⟨ha1L, _, _, ha2R⟩ | ⟨_, ha1R, ha2L, _⟩
        · rcases hexact b hb with ⟨hb1L, _, _, _⟩ | ⟨_, hb1R, hb2L, _⟩
          · exact absurd (huniqL a ha b hb ha1L hb1L) hab
          · exact ⟨a, b, ha, hb, hab, ha1L, hb1R, ha2R, hb2L⟩
        · rcases hexact b hb with ⟨hb1L, _, _, hb2R⟩ | ⟨_, hb1R, _, _⟩
          · exact ⟨b, a, hb, ha, hab.symm, hb1L, ha1R, hb2R, ha2L⟩
          · exact absurd (huniqR a ha b hb ha1R hb1R) hab
      rcases hpair with ⟨u, v, huS, hvS, huv, hu1L, hv1R, hu2R, hv2L⟩
      have hSeq : S = {u, v} := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hk
          rcases hexact k hk with ⟨hk1L, _, _, _⟩ | ⟨_, hk1R, _, _⟩
          · left; exact huniqL k hk u huS hk1L hu1L
          · right; exact huniqR k hk v hvS hk1R hv1R
        · rintro (rfl | rfl)
          · exact huS
          · exact hvS
      refine ⟨{{u, v}}, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro e he
          rw [Finset.mem_singleton.mp he]
          exact ⟨Finset.card_pair huv, by rw [hSeq]⟩
        · intro e₁ he₁ e₂ he₂ hne
          exact absurd ((Finset.mem_singleton.mp he₁).trans (Finset.mem_singleton.mp he₂).symm) hne
      · intro x y
        simp only [MTree.eval, ht₁_or, ht₂_or, matchFnOn, hSeq, Finset.mem_singleton]
        have h1L_iff : ∀ k, Sum.inl k ∈ t₁.vars ↔ k = u := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hL k).mp (Finset.mem_union_left _ hk)
            exact huniqL k hkS u huS hk hu1L
          · rintro rfl; exact hu1L
        have h1R_iff : ∀ k, Sum.inr k ∈ t₁.vars ↔ k = v := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hR k).mp (Finset.mem_union_left _ hk)
            exact huniqR k hkS v hvS hk hv1R
          · rintro rfl; exact hv1R
        have h2L_iff : ∀ k, Sum.inl k ∈ t₂.vars ↔ k = v := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hL k).mp (Finset.mem_union_right _ hk)
            have hk1L : Sum.inl k ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hk
            rcases hexact k hkS with ⟨h, _, _, _⟩ | ⟨_, hk1R, _, _⟩
            · exact absurd h hk1L
            · exact huniqR k hkS v hvS hk1R hv1R
          · rintro rfl; exact hv2L
        have h2R_iff : ∀ k, Sum.inr k ∈ t₂.vars ↔ k = u := by
          intro k
          constructor
          · intro hk
            have hkS : k ∈ S := (hR k).mp (Finset.mem_union_right _ hk)
            have hk1R : Sum.inr k ∉ t₁.vars := Finset.disjoint_right.mp hro.2.2 hk
            rcases hexact k hkS with ⟨hk1L, _, _, _⟩ | ⟨_, h, _, _⟩
            · exact huniqL k hkS u huS hk1L hu1L
            · exact absurd h hk1R
          · rintro rfl; exact hu2R
        simp only [h1L_iff, h1R_iff, h2L_iff, h2R_iff, exists_eq_left, exists_eq_or_imp,
          Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        cases x u <;> cases x v <;> cases y u <;> cases y v <;> decide

private lemma optimal_circuit_is_matchFn {n : ℕ} (hn : 2 ≤ n) (C : Circuit)
    (hM : Monotone2 C) (hsz : C.size + 1 ≤ 2 * n)
    (hrep : Represents (fun i j : Fin n => decide (i = j)) C) :
    ∃ M : Finset (Finset (Fin n)), IsMatching Finset.univ M ∧
      ∀ x y, C.eval (List.ofFn x ++ List.ofFn y) = matchFn M x y := by
  have heval_zeroL : ∀ i : Fin n, C.eval (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i)) = false := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by intro h; rw [h0] at h; exact (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have hle : C.eval (List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i)) ≤
        C.eval (oneEach j i) := by
      unfold Circuit.eval
      refine monotone2_wires_mono C hM (by simp [oneEach]) (fun k => ?_) C.output
      by_cases hk : k < n
      · simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hk]
      · by_cases hk2 : k < n + n
        · simp only [oneEach, unitVec, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show k - n < n by omega]
          exact le_refl _
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hf : C.eval (oneEach j i) = false := by rw [hrep j i]; simp [hj]
    rw [hf] at hle
    exact Bool.eq_false_of_le_false hle
  have heval_zeroR : ∀ i : Fin n, C.eval (List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false)) = false := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin n, j ≠ i := by
      by_cases h0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by intro h; rw [h0] at h; exact (by decide : (1 : ℕ) ≠ 0) (congrArg Fin.val h)⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h0⟩
    have hle : C.eval (List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false)) ≤
        C.eval (oneEach i j) := by
      unfold Circuit.eval
      refine monotone2_wires_mono C hM (by simp [oneEach]) (fun k => ?_) C.output
      by_cases hk : k < n
      · simp [oneEach, unitVec, List.getD_eq_getElem?_getD, List.getElem?_append_left, hk]
      · by_cases hk2 : k < n + n
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp [show k - n < n by omega]
        · simp only [oneEach, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hf : C.eval (oneEach i j) = false := by rw [hrep i j]; simp [hj.symm]
    rw [hf] at hle
    exact Bool.eq_false_of_le_false hle
  have hall_inp : ∀ k < 2 * n, k ∈ reach C (2 * n) C.output := by
    intro k hk
    by_contra hnot
    by_cases hkn : k < n
    · let i : Fin n := ⟨k, hkn⟩
      have heq := reach_eq_on_wires C (2 * n)
        (inp₁ := List.ofFn (unitVec i) ++ List.ofFn (unitVec i))
        (inp₂ := List.ofFn (fun _ : Fin n => false) ++ List.ofFn (unitVec i))
        (by simp; omega) (by simp; omega) C.output (fun m hm hmr => ?_)
      · have h1 : C.eval (List.ofFn (unitVec i) ++ List.ofFn (unitVec i)) = true := by
          change C.eval (oneEach i i) = true; rw [hrep i i]; simp
        have h2 := heval_zeroL i
        unfold Circuit.eval at h1 h2
        rw [heq] at h1
        exact Bool.false_ne_true.symm (h1.symm.trans h2)
      · have hmk : m ≠ k := fun h => hnot (h ▸ hmr)
        by_cases hmn : m < n
        · simp [unitVec, List.getD_eq_getElem?_getD, List.getElem?_append_left, hmn,
            Fin.ext_iff, i, hmk]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp
    · let i : Fin n := ⟨k - n, by omega⟩
      have heq := reach_eq_on_wires C (2 * n)
        (inp₁ := List.ofFn (unitVec i) ++ List.ofFn (unitVec i))
        (inp₂ := List.ofFn (unitVec i) ++ List.ofFn (fun _ : Fin n => false))
        (by simp; omega) (by simp; omega) C.output (fun m hm hmr => ?_)
      · have h1 : C.eval (List.ofFn (unitVec i) ++ List.ofFn (unitVec i)) = true := by
          change C.eval (oneEach i i) = true; rw [hrep i i]; simp
        have h2 := heval_zeroR i
        unfold Circuit.eval at h1 h2
        rw [heq] at h1
        exact Bool.false_ne_true.symm (h1.symm.trans h2)
      · have hmk : m ≠ k := fun h => hnot (h ▸ hmr)
        by_cases hmn : m < n
        · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hmn]
        · have hsub : m - n ≠ k - n := by omega
          have hmn2 : m - n < n := by omega
          have hne_fin : (⟨m - n, hmn2⟩ : Fin n) ≠ i := fun h => hsub (congrArg Fin.val h)
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
          simp only [List.length_ofFn, List.getElem?_ofFn, hmn2, ↓reduceDIte, Option.getD_some]
          simp [unitVec, hne_fin, hne_fin.symm]
  have hout_lt : C.output < 2 * n + C.gates.length := by
    by_contra hge
    push_neg at hge
    have h0 := hrep ⟨0, by omega⟩ ⟨0, by omega⟩
    unfold Circuit.eval at h0
    rw [wires_getD_oob C (oneEach ⟨0, by omega⟩ ⟨0, by omega⟩) C.output (by simp [oneEach]; omega)] at h0
    simp at h0
  let R := reach C (2 * n) C.output
  let G := R.filter (fun w => decide (2 * n ≤ w))
  have hG_sub : G ⊆ (Finset.range C.gates.length).image (fun j => 2 * n + j) := by
    intro w hw
    simp only [G, Finset.mem_filter, decide_eq_true_eq] at hw
    have hw_le := mem_reach_le C (2 * n) C.output w hw.1
    rw [Finset.mem_image]
    exact ⟨w - 2 * n, Finset.mem_range.mpr (by omega), by omega⟩
  have hG_card_le : G.card ≤ 2 * n - 1 := by
    have h1 := Finset.card_le_card hG_sub
    have h2 := Finset.card_image_le (s := Finset.range C.gates.length) (f := fun j => 2 * n + j)
    rw [Finset.card_range] at h2
    have h3 : C.gates.length ≤ 2 * n - 1 := by unfold Circuit.size at hsz; omega
    omega
  have hR_card : R.card = 2 * n + G.card := by
    have hpart : R = Finset.range (2 * n) ∪ G := by
      ext w
      simp only [Finset.mem_union, Finset.mem_range, G, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · intro hw
        by_cases hlt : w < 2 * n
        · left; exact hlt
        · right; exact ⟨hw, by omega⟩
      · rintro (hlt | ⟨hw, _⟩)
        · exact hall_inp w hlt
        · exact hw
    have hdisj : Disjoint (Finset.range (2 * n)) G := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rw [Finset.mem_range] at hw1
      simp only [G, Finset.mem_filter, decide_eq_true_eq] at hw2
      omega
    rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_range]
  have herase_sub : R.erase C.output ⊆ G.biUnion (gateParents C (2 * n)) := by
    have hrec : ∀ w ∈ R, ∀ x ∈ reach C (2 * n) w, x ≠ w →
        x ∈ (G.filter (· ≤ w)).biUnion (gateParents C (2 * n)) := by
      intro w hw
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro x hx hne
        rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hx
        rcases hx with rfl | ⟨u, hu, hxu⟩
        · exact absurd rfl hne
        · have hwG : w ∈ G := by
            simp only [G, Finset.mem_filter, decide_eq_true_eq]
            refine ⟨hw, ?_⟩
            by_contra hlt
            unfold gateParents at hu
            have hcond : ¬ (2 * n ≤ w ∧ w - 2 * n < C.gates.length) := by omega
            rw [dif_neg hcond] at hu
            simp at hu
          by_cases hxu_eq : x = u
          · rw [hxu_eq]
            exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwG, le_refl w⟩, hu⟩
          · have huR : u ∈ R := by
              have hsub : reach C (2 * n) u ⊆ reach C (2 * n) w :=
                reach_subset_of_mem_gateParents C (2 * n) w u hu
              have hwsub : ∀ y ∈ reach C (2 * n) w, y ∈ R := by
                intro y hy
                clear ih
                have htrans : ∀ a b c, b ∈ reach C (2 * n) a → c ∈ reach C (2 * n) b → c ∈ reach C (2 * n) a := by
                  intro a
                  induction a using Nat.strong_induction_on with
                  | ind a iha =>
                    intro b c hba hcb
                    rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
                    rcases hba with rfl | ⟨v, hv, hbv⟩
                    · exact hcb
                    · exact reach_subset_of_mem_gateParents C (2 * n) a v hv
                        (iha v (mem_gateParents_lt C (2 * n) a v hv) b c hbv hcb)
                exact htrans C.output w y hw hy
              exact hwsub u (reach_subset_of_mem_gateParents C (2 * n) w u hu (self_mem_reach _ _ _))
            have hih := ih u (mem_gateParents_lt C (2 * n) w u hu) huR x hxu hxu_eq
            rcases Finset.mem_biUnion.mp hih with ⟨v, hv, hxv⟩
            rw [Finset.mem_filter] at hv
            exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨hv.1, le_trans hv.2 (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hu))⟩, hxv⟩
    intro x hx
    rw [Finset.mem_erase] at hx
    have h := hrec C.output (self_mem_reach C (2 * n) C.output) x hx.2 hx.1
    rcases Finset.mem_biUnion.mp h with ⟨v, hv, hxv⟩
    exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_filter.mp hv).1, hxv⟩
  have hsum_le : ∑ w ∈ G, (gateParents C (2 * n) w).card ≤ 2 * G.card := by
    calc
      ∑ w ∈ G, (gateParents C (2 * n) w).card ≤ ∑ _w ∈ G, 2 :=
        Finset.sum_le_sum (fun w _ => gateParents_card_le C hM (2 * n) w)
      _ = 2 * G.card := by simp [mul_comm]
  have herase_card : (R.erase C.output).card = 2 * n + G.card - 1 := by
    rw [Finset.card_erase_of_mem (self_mem_reach C (2 * n) C.output), hR_card]
  have hbi_ge : 2 * n + G.card - 1 ≤ (G.biUnion (gateParents C (2 * n))).card := by
    rw [← herase_card]; exact Finset.card_le_card herase_sub
  have hbi_le : (G.biUnion (gateParents C (2 * n))).card ≤ ∑ w ∈ G, (gateParents C (2 * n) w).card :=
    Finset.card_biUnion_le
  have hG_card : G.card = 2 * n - 1 := by omega
  have hbi_eq : (G.biUnion (gateParents C (2 * n))).card = ∑ w ∈ G, (gateParents C (2 * n) w).card := by omega
  have hsum_eq : ∑ w ∈ G, (gateParents C (2 * n) w).card = 2 * G.card := by omega
  have hdeg2 : ∀ w ∈ G, (gateParents C (2 * n) w).card = 2 := by
    intro w hw
    by_contra hne
    have hlt : (gateParents C (2 * n) w).card < 2 :=
      Nat.lt_of_le_of_ne (gateParents_card_le C hM (2 * n) w) hne
    have h1 := Finset.add_sum_erase G (fun x => (gateParents C (2 * n) x).card) hw
    have h2 : ∑ x ∈ G.erase w, (gateParents C (2 * n) x).card ≤ 2 * (G.erase w).card := by
      calc
        ∑ x ∈ G.erase w, (gateParents C (2 * n) x).card ≤ ∑ _x ∈ G.erase w, 2 :=
          Finset.sum_le_sum (fun x _ => gateParents_card_le C hM (2 * n) x)
        _ = 2 * (G.erase w).card := by simp [mul_comm]
    have h3 : (G.erase w).card + 1 = G.card := Finset.card_erase_add_one hw
    omega
  have hpar_disj : ∀ w₁ ∈ G, ∀ w₂ ∈ G, w₁ ≠ w₂ →
      Disjoint (gateParents C (2 * n) w₁) (gateParents C (2 * n) w₂) :=
    biUnion_card_eq_sum_iff_disjoint G (gateParents C (2 * n)) hbi_eq
  have hreach_trans : ∀ a b c, b ∈ reach C (2 * n) a → c ∈ reach C (2 * n) b → c ∈ reach C (2 * n) a := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a iha =>
      intro b c hba hcb
      rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
      rcases hba with rfl | ⟨v, hv, hbv⟩
      · exact hcb
      · exact reach_subset_of_mem_gateParents C (2 * n) a v hv
          (iha v (mem_gateParents_lt C (2 * n) a v hv) b c hbv hcb)
  have hstep_parent : ∀ a b, b ∈ reach C (2 * n) a → b ≠ a →
      ∃ p ∈ reach C (2 * n) a, b ∈ gateParents C (2 * n) p := by
    intro a
    induction a using Nat.strong_induction_on with
    | ind a iha =>
      intro b hba hne
      rw [reach_eq, Finset.mem_insert, Finset.mem_biUnion] at hba
      rcases hba with rfl | ⟨v, hv, hbv⟩
      · exact absurd rfl hne
      · by_cases hbv_eq : b = v
        · exact ⟨a, self_mem_reach _ _ _, hbv_eq ▸ hv⟩
        · obtain ⟨p, hp, hbp⟩ := iha v (mem_gateParents_lt C (2 * n) a v hv) b hbv hbv_eq
          exact ⟨p, reach_subset_of_mem_gateParents C (2 * n) a v hv hp, hbp⟩
  have hchildren_disj : ∀ w ∈ G, ∀ u ∈ gateParents C (2 * n) w, ∀ v ∈ gateParents C (2 * n) w,
      u ≠ v → Disjoint (reach C (2 * n) u) (reach C (2 * n) v) := by
    intro w hw u hu v hv huv
    rw [Finset.disjoint_left]
    intro x hxu hxv
    let common := reach C (2 * n) u ∩ reach C (2 * n) v
    have hne_c : common.Nonempty := ⟨x, Finset.mem_inter.mpr ⟨hxu, hxv⟩⟩
    let y := common.max' hne_c
    have hy_mem : y ∈ common := Finset.max'_mem common hne_c
    have hyu : y ∈ reach C (2 * n) u := (Finset.mem_inter.mp hy_mem).1
    have hyv : y ∈ reach C (2 * n) v := (Finset.mem_inter.mp hy_mem).2
    have hpu : ∃ p ∈ G, p ≤ w ∧ y ∈ gateParents C (2 * n) p ∧ (p = w ∨ p ∈ reach C (2 * n) u) := by
      by_cases hyu_eq : y = u
      · exact ⟨w, hw, le_refl w, hyu_eq ▸ hu, Or.inl rfl⟩
      · obtain ⟨p, hpu, hyp⟩ := hstep_parent u y hyu hyu_eq
        have hpR : p ∈ R := hreach_trans C.output w p (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w u hu hpu)
        have hpG : p ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hpR, ?_⟩
          by_contra hlt
          unfold gateParents at hyp
          have hcond : ¬ (2 * n ≤ p ∧ p - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyp; simp at hyp
        exact ⟨p, hpG, le_trans (mem_reach_le _ _ _ _ hpu) (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hu)),
          hyp, Or.inr hpu⟩
    have hpv : ∃ q ∈ G, q ≤ w ∧ y ∈ gateParents C (2 * n) q ∧ (q = w ∨ q ∈ reach C (2 * n) v) := by
      by_cases hyv_eq : y = v
      · exact ⟨w, hw, le_refl w, hyv_eq ▸ hv, Or.inl rfl⟩
      · obtain ⟨q, hqv, hyq⟩ := hstep_parent v y hyv hyv_eq
        have hqR : q ∈ R := hreach_trans C.output w q (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w v hv hqv)
        have hqG : q ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hqR, ?_⟩
          by_contra hlt
          unfold gateParents at hyq
          have hcond : ¬ (2 * n ≤ q ∧ q - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyq; simp at hyq
        exact ⟨q, hqG, le_trans (mem_reach_le _ _ _ _ hqv) (Nat.le_of_lt (mem_gateParents_lt _ _ _ _ hv)),
          hyq, Or.inr hqv⟩
    rcases hpu with ⟨p, hpG, _, hyp, hpw | hpu'⟩ <;> rcases hpv with ⟨q, hqG, _, hyq, hqw | hqv'⟩
    · have hyu_eq : y = u := by
        by_contra hne
        obtain ⟨p', hp', hyp'⟩ := hstep_parent u y hyu hne
        have hp'lt : p' < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hp') (mem_gateParents_lt _ _ _ _ hu)
        have hp'R : p' ∈ R := hreach_trans C.output w p' (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w u hu hp')
        have hp'G : p' ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hp'R, ?_⟩
          by_contra hlt
          unfold gateParents at hyp'
          have hcond : ¬ (2 * n ≤ p' ∧ p' - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyp'; simp at hyp'
        exact Finset.disjoint_left.mp (hpar_disj w hw p' hp'G (Nat.ne_of_gt hp'lt)) (hpw ▸ hyp) hyp'
      have hyv_eq : y = v := by
        by_contra hne
        obtain ⟨q', hq', hyq'⟩ := hstep_parent v y hyv hne
        have hq'lt : q' < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hq') (mem_gateParents_lt _ _ _ _ hv)
        have hq'R : q' ∈ R := hreach_trans C.output w q' (Finset.mem_filter.mp hw).1
          (reach_subset_of_mem_gateParents C (2 * n) w v hv hq')
        have hq'G : q' ∈ G := by
          simp only [G, Finset.mem_filter, decide_eq_true_eq]
          refine ⟨hq'R, ?_⟩
          by_contra hlt
          unfold gateParents at hyq'
          have hcond : ¬ (2 * n ≤ q' ∧ q' - 2 * n < C.gates.length) := by omega
          rw [dif_neg hcond] at hyq'; simp at hyq'
        exact Finset.disjoint_left.mp (hpar_disj w hw q' hq'G (Nat.ne_of_gt hq'lt)) (hqw ▸ hyq) hyq'
      exact huv (hyu_eq.symm.trans hyv_eq)
    · have hqlt : q < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hqv') (mem_gateParents_lt _ _ _ _ hv)
      exact Finset.disjoint_left.mp (hpar_disj w hw q hqG (Nat.ne_of_gt hqlt)) (hpw ▸ hyp) hyq
    · have hplt : p < w := lt_of_le_of_lt (mem_reach_le _ _ _ _ hpu') (mem_gateParents_lt _ _ _ _ hu)
      exact Finset.disjoint_left.mp (hpar_disj w hw p hpG (Nat.ne_of_gt hplt)) (hqw ▸ hyq) hyp
    · have hpq : p = q := by
        by_contra hne
        exact Finset.disjoint_left.mp (hpar_disj p hpG q hqG hne) hyp hyq
      have hp_mem : p ∈ common := Finset.mem_inter.mpr ⟨hpu', hpq ▸ hqv'⟩
      have hle_y : p ≤ y := Finset.le_max' common p hp_mem
      have hlt_p : y < p := mem_gateParents_lt C (2 * n) p y hyp
      omega
  have hbuild : ∀ w ∈ R, ∃ t : MTree n, t.ReadOnce ∧
      (∀ i : Fin n, Sum.inl i ∈ t.vars ↔ i.val ∈ reach C (2 * n) w) ∧
      (∀ i : Fin n, Sum.inr i ∈ t.vars ↔ n + i.val ∈ reach C (2 * n) w) ∧
      (∀ x y, t.eval x y = (C.wires (List.ofFn x ++ List.ofFn y)).getD w false) := by
    intro w hw
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hlt : w < 2 * n
      · by_cases hwn : w < n
        · refine ⟨MTree.leafL ⟨w, hwn⟩, trivial, ?_, ?_, ?_⟩
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, Sum.inl.injEq, Fin.ext_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, reduceCtorEq, false_iff]
            intro hmem
            have hle := mem_reach_le C (2 * n) w (n + i.val) hmem
            omega
          · intro x y
            rw [wires_getD_prefix C.gates (List.ofFn x ++ List.ofFn y) C.output w (by simp; omega)]
            simp [MTree.eval, List.getD_eq_getElem?_getD, List.getElem?_append_left, hwn]
        · refine ⟨MTree.leafR ⟨w - n, by omega⟩, trivial, ?_, ?_, ?_⟩
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, reduceCtorEq, false_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]; omega
          · intro i
            simp only [MTree.vars, Finset.mem_singleton, Sum.inr.injEq, Fin.ext_iff]
            have hrg : reach C (2 * n) w = {w} := by
              rw [reach_eq]
              have hp : gateParents C (2 * n) w = ∅ := by
                unfold gateParents
                rw [dif_neg (by omega)]
              simp [hp]
            rw [hrg, Finset.mem_singleton]; omega
          · intro x y
            rw [wires_getD_prefix C.gates (List.ofFn x ++ List.ofFn y) C.output w (by simp; omega)]
            simp only [MTree.eval, List.getD_eq_getElem?_getD]
            rw [List.getElem?_append_right (by simp; omega)]
            simp [show w - n < n by omega]
      · have hwG : w ∈ G := Finset.mem_filter.mpr ⟨hw, decide_eq_true (by omega)⟩
        have hw_le : w ≤ C.output := mem_reach_le C (2 * n) C.output w hw
        have hj : w - 2 * n < C.gates.length := by omega
        have hpc : (gateParents C (2 * n) w).card = 2 := hdeg2 w hwG
        obtain ⟨u, v, huv, hp_eq⟩ := Finset.card_eq_two.mp hpc
        have hu_mem : u ∈ gateParents C (2 * n) w := hp_eq ▸ Finset.mem_insert_self u {v}
        have hv_mem : v ∈ gateParents C (2 * n) w := hp_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
        have huR : u ∈ R := hreach_trans C.output w u hw (reach_subset_of_mem_gateParents _ _ _ _ hu_mem (self_mem_reach _ _ _))
        have hvR : v ∈ R := hreach_trans C.output w v hw (reach_subset_of_mem_gateParents _ _ _ _ hv_mem (self_mem_reach _ _ _))
        obtain ⟨t₁, hro₁, hL₁, hR₁, hev₁⟩ := ih u (mem_gateParents_lt C (2 * n) w u hu_mem) huR
        obtain ⟨t₂, hro₂, hL₂, hR₂, hev₂⟩ := ih v (mem_gateParents_lt C (2 * n) w v hv_mem) hvR
        have hdisj_r : Disjoint (reach C (2 * n) u) (reach C (2 * n) v) :=
          hchildren_disj w hwG u hu_mem v hv_mem huv
        have hdisj_t : Disjoint t₁.vars t₂.vars := by
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          cases z with
          | inl i => exact Finset.disjoint_left.mp hdisj_r ((hL₁ i).mp hz1) ((hL₂ i).mp hz2)
          | inr i => exact Finset.disjoint_left.mp hdisj_r ((hR₁ i).mp hz1) ((hR₂ i).mp hz2)
        have hg_inp : ∀ z, z ∈ (C.gates[w - 2 * n]).inputs ↔ z = u ∨ z = v := by
          have hsub_len : (C.gates[w - 2 * n]).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
          have hu_in : u ∈ (C.gates[w - 2 * n]).inputs := by
            unfold gateParents at hu_mem
            rw [dif_pos ⟨by omega, hj⟩] at hu_mem
            exact (List.mem_filter.mp (List.mem_toFinset.mp hu_mem)).1
          have hv_in : v ∈ (C.gates[w - 2 * n]).inputs := by
            unfold gateParents at hv_mem
            rw [dif_pos ⟨by omega, hj⟩] at hv_mem
            exact (List.mem_filter.mp (List.mem_toFinset.mp hv_mem)).1
          cases hlist : (C.gates[w - 2 * n]).inputs with
          | nil => rw [hlist] at hu_in; simp at hu_in
          | cons a l =>
            cases l with
            | nil =>
              rw [hlist] at hu_in hv_in
              simp only [List.mem_singleton] at hu_in hv_in
              exact absurd (hu_in.trans hv_in.symm) huv
            | cons b l' =>
              cases l' with
              | nil =>
                rw [hlist] at hu_in hv_in
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_in hv_in
                intro z
                simp only [List.mem_cons, List.not_mem_nil, or_false]
                rcases hu_in with rfl | rfl <;> rcases hv_in with rfl | rfl
                · exact absurd rfl huv
                · rfl
                · exact or_comm
                · exact absurd rfl huv
              | cons c l'' =>
                rw [hlist] at hsub_len; simp at hsub_len
        have hlist_pair : (C.gates[w - 2 * n]).inputs = [u, v] ∨ (C.gates[w - 2 * n]).inputs = [v, u] := by
          have hsub_len : (C.gates[w - 2 * n]).inputs.length ≤ 2 := (hM _ (List.getElem_mem hj)).2
          cases hlist : (C.gates[w - 2 * n]).inputs with
          | nil =>
            have := (hg_inp u).mpr (Or.inl rfl); rw [hlist] at this; simp at this
          | cons a l =>
            cases l with
            | nil =>
              have hu1 := (hg_inp u).mpr (Or.inl rfl)
              have hv1 := (hg_inp v).mpr (Or.inr rfl)
              rw [hlist] at hu1 hv1; simp at hu1 hv1; exact absurd (hu1.trans hv1.symm) huv
            | cons b l' =>
              cases l' with
              | nil =>
                have ha := (hg_inp a).mp (by rw [hlist]; simp)
                have hb := (hg_inp b).mp (by rw [hlist]; simp)
                have hu1 := (hg_inp u).mpr (Or.inl rfl)
                have hv1 := (hg_inp v).mpr (Or.inr rfl)
                rw [hlist] at hu1 hv1; simp at hu1 hv1
                rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
                · rcases hv1 with h | h <;> exact absurd h.symm huv
                · left; rfl
                · right; rfl
                · rcases hu1 with h | h <;> exact absurd h huv
              | cons c l'' => rw [hlist] at hsub_len; simp at hsub_len
        have hvarsL : ∀ i : Fin n, Sum.inl i ∈ t₁.vars ∪ t₂.vars ↔ i.val ∈ reach C (2 * n) w := by
          intro i
          rw [Finset.mem_union, hL₁, hL₂]
          conv_rhs => rw [reach_eq, hp_eq]
          simp only [Finset.mem_insert, Finset.biUnion_insert, Finset.biUnion_singleton, Finset.mem_union]
          have hne_w : i.val ≠ w := by omega
          simp [hne_w]
        have hvarsR : ∀ i : Fin n, Sum.inr i ∈ t₁.vars ∪ t₂.vars ↔ n + i.val ∈ reach C (2 * n) w := by
          intro i
          rw [Finset.mem_union, hR₁, hR₂]
          conv_rhs => rw [reach_eq, hp_eq]
          simp only [Finset.mem_insert, Finset.biUnion_insert, Finset.biUnion_singleton, Finset.mem_union]
          have hne_w : n + i.val ≠ w := by omega
          simp [hne_w]
        have hu_lt : u < w := mem_gateParents_lt C (2 * n) w u hu_mem
        have hv_lt : v < w := mem_gateParents_lt C (2 * n) w v hv_mem
        have hop := (hM _ (List.getElem_mem hj)).1
        rcases hop with hop_and | hop_or
        · refine ⟨MTree.and t₁ t₂, ⟨hro₁, hro₂, hdisj_t⟩, hvarsL, hvarsR, ?_⟩
          intro x y
          have hwm : w = (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          conv_rhs => rw [hwm]
          rw [wires_getD_gate C (List.ofFn x ++ List.ofFn y) (w - 2 * n) hj]
          simp only [MTree.eval, hev₁, hev₂, hop_and]
          have hul : u < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          have hvl : v < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          rcases hlist_pair with hlp | hlp
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.all_cons, List.all_nil, id_eq, Bool.and_true]
            exact Bool.and_comm _ _
        · refine ⟨MTree.or t₁ t₂, ⟨hro₁, hro₂, hdisj_t⟩, hvarsL, hvarsR, ?_⟩
          intro x y
          have hwm : w = (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          conv_rhs => rw [hwm]
          rw [wires_getD_gate C (List.ofFn x ++ List.ofFn y) (w - 2 * n) hj]
          simp at hop_or
          simp only [MTree.eval, hev₁, hev₂, hop_or]
          have hul : u < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          have hvl : v < (List.ofFn x ++ List.ofFn y).length + (w - 2 * n) := by simp; omega
          rcases hlist_pair with hlp | hlp
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · rw [hlp]
            simp only [GateOp.eval, List.map_cons, List.map_nil, hul, hvl, ↓reduceIte,
              List.any_cons, List.any_nil, id_eq, Bool.or_false]
            exact Bool.or_comm _ _
  obtain ⟨t, hro, hL, hR, hev⟩ := hbuild C.output (self_mem_reach C (2 * n) C.output)
  have hL' : ∀ i : Fin n, Sum.inl i ∈ t.vars ↔ i ∈ (Finset.univ : Finset (Fin n)) := by
    intro i; simp [hL, hall_inp i.val (by omega)]
  have hR' : ∀ i : Fin n, Sum.inr i ∈ t.vars ↔ i ∈ (Finset.univ : Finset (Fin n)) := by
    intro i; simp [hR, hall_inp (n + i.val) (by omega)]
  have hS_ne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hdiag : ∀ i ∈ (Finset.univ : Finset (Fin n)), t.eval (unitVec i) (unitVec i) = true := by
    intro i _; rw [hev]; change C.eval (oneEach i i) = true; rw [hrep i i]; simp
  have hoff : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → t.eval (unitVec i) (unitVec j) = false := by
    intro i _ j _ hij; rw [hev]; change C.eval (oneEach i j) = false; rw [hrep i j]; simp [hij]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      t.eval (unitVec i) (fun _ => false) = false ∧ t.eval (fun _ => false) (unitVec i) = false := by
    intro i _; rw [hev, hev]; exact ⟨heval_zeroR i, heval_zeroL i⟩
  obtain ⟨M, hM_match, hM_eq⟩ := classify_mtree t Finset.univ hS_ne hro hL' hR' hdiag hoff hzero
  refine ⟨M, hM_match, ?_⟩
  intro x y
  unfold Circuit.eval
  rw [← hev x y, hM_eq x y]
  simp [matchFn, matchFnOn]

private lemma exists_circuit_of_matching {n : ℕ} (hn : 2 ≤ n) (M : Finset (Finset (Fin n)))
    (hM : IsMatching Finset.univ M) :
    ∃ C : Circuit, Monotone2 C ∧ C.size + 1 ≤ 2 * n ∧
      Represents (fun i j : Fin n => decide (i = j)) C ∧
      ∀ x y, matchFn M x y = C.eval (List.ofFn x ++ List.ofFn y) := by
  let covered : Finset (Fin n) := M.biUnion id
  let free : List (Fin n) := (Finset.univ \ covered).toList
  let pairs : List (Finset (Fin n)) := M.toList
  have hcov_card : covered.card = 2 * M.card := by
    rw [Finset.card_biUnion]
    · simp only [id_eq]
      calc
        ∑ e ∈ M, e.card = ∑ _e ∈ M, 2 := Finset.sum_congr rfl (fun e he => (hM.1 e he).1)
        _ = 2 * M.card := by simp [mul_comm]
    · intro e₁ he₁ e₂ he₂ hne; exact hM.2 e₁ he₁ e₂ he₂ hne
  have hfree_len : free.length = n - 2 * M.card := by
    simp only [free, Finset.length_toList]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hcov_card]
  have hpairs_len : pairs.length = M.card := Finset.length_toList M
  have h2M_le : 2 * M.card ≤ n := by
    rw [← hcov_card]
    exact le_trans (Finset.card_le_univ covered) (by simp)
  let gFree : List Gate := free.map (fun i => Gate.mk .and [i.val, n + i.val])
  let pairGateFn : Finset (Fin n) → ℕ → List Gate := fun e base =>
    if h : e.Nonempty then
      let a := e.min' h
      let b := e.max' h
      [Gate.mk .or [a.val, n + b.val],
       Gate.mk .or [b.val, n + a.val],
       Gate.mk .and [base, base + 1]]
    else []
  let buildPairs : List (Finset (Fin n)) → ℕ → List Gate × List ℕ :=
    fun ps base => ps.foldl (fun (acc : List Gate × List ℕ) e =>
      let b := base + acc.1.length
      (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) ([], [])
  let bp := buildPairs pairs (2 * n + gFree.length)
  let freeWires : List ℕ := (List.range free.length).map (fun k => 2 * n + k)
  let allWires : List ℕ := freeWires ++ bp.2
  have hbp_len : bp.1.length = 3 * M.card ∧ bp.2.length = M.card ∧
      (∀ g ∈ bp.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
    have hgen : ∀ (ps : List (Finset (Fin n))) (base : ℕ),
        (∀ e ∈ ps, e.card = 2) →
        (buildPairs ps base).1.length = 3 * ps.length ∧
        (buildPairs ps base).2.length = ps.length ∧
        (∀ g ∈ (buildPairs ps base).1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
      intro ps base hps
      have hfold : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
          (∀ e ∈ qs, e.card = 2) →
          (∀ g ∈ accG, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
          let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
            let b := base + acc.1.length
            (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
          res.1.length = accG.length + 3 * qs.length ∧
          res.2.length = accW.length + qs.length ∧
          (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) := by
        intro qs
        induction qs with
        | nil =>
          intro accG accW _ hacc
          exact ⟨by simp, by simp, hacc⟩
        | cons e qs ih =>
          intro accG accW hqs hacc
          have he2 : e.card = 2 := hqs e (List.mem_cons_self)
          have hne : e.Nonempty := Finset.card_pos.mp (by omega)
          have hpg_len : (pairGateFn e (base + accG.length)).length = 3 := by
            simp [pairGateFn, hne]
          have hpg_ok : ∀ g ∈ pairGateFn e (base + accG.length),
              g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
            intro g hg
            simp only [pairGateFn, hne, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hg
            rcases hg with rfl | rfl | rfl <;> simp
          simp only [List.foldl_cons]
          have hrec := ih (accG ++ pairGateFn e (base + accG.length)) (accW ++ [base + accG.length + 2])
            (fun e' he' => hqs e' (List.mem_cons_of_mem _ he'))
            (fun g hg => by
              rcases List.mem_append.mp hg with h1 | h2
              · exact hacc g h1
              · exact hpg_ok g h2)
          refine ⟨?_, ?_, hrec.2.2⟩
          · rw [hrec.1, List.length_append, hpg_len]; simp; omega
          · rw [hrec.2.1, List.length_append]; simp; omega
      have h := hfold ps [] [] hps (by simp)
      simpa [buildPairs] using h
    have h := hgen pairs (2 * n + gFree.length) (fun e he => (hM.1 e (Finset.mem_toList.mp he)).1)
    simpa [bp, hpairs_len] using h
  have hallW_len : allWires.length = n - M.card := by
    simp only [allWires, freeWires, List.length_append, List.length_map, List.length_range,
      hfree_len, hbp_len.2.1]
    omega
  have hallW_pos : 0 < allWires.length := by omega
  let orFold : ℕ → List ℕ → ℕ → List Gate × ℕ := fun cur ws base =>
    ws.foldl (fun (acc : List Gate × ℕ) w =>
      (acc.1 ++ [Gate.mk .or [acc.2, w]], base + acc.1.length)) ([], cur)
  have horFold_props : ∀ (cur : ℕ) (ws : List ℕ) (base : ℕ),
      (orFold cur ws base).1.length = ws.length ∧
      (∀ g ∈ (orFold cur ws base).1, g.op = .or ∧ g.inputs.length = 2) ∧
      ∀ (pre : List Gate) (inp : List Bool), inp.length + pre.length = base →
        cur < base → (∀ w ∈ ws, w < base) →
        ((Circuit.mk (pre ++ (orFold cur ws base).1) 0).wires inp).getD (orFold cur ws base).2 false =
          (((Circuit.mk pre 0).wires inp).getD cur false ||
            ws.any (fun w => ((Circuit.mk pre 0).wires inp).getD w false)) := by
    intro cur ws base
    have hgen : ∀ (qs : List ℕ) (accG : List Gate) (accW : ℕ),
        (∀ g ∈ accG, g.op = .or ∧ g.inputs.length = 2) →
        let res := qs.foldl (fun (acc : List Gate × ℕ) w =>
          (acc.1 ++ [Gate.mk .or [acc.2, w]], base + acc.1.length)) (accG, accW)
        res.1.length = accG.length + qs.length ∧
        (∀ g ∈ res.1, g.op = .or ∧ g.inputs.length = 2) ∧
        ∀ (pre : List Gate) (inp : List Bool), inp.length + pre.length = base →
          accW < base + accG.length → (∀ w ∈ qs, w < base) →
          ((Circuit.mk (pre ++ res.1) 0).wires inp).getD res.2 false =
            (((Circuit.mk (pre ++ accG) 0).wires inp).getD accW false ||
              qs.any (fun w => ((Circuit.mk pre 0).wires inp).getD w false)) := by
      intro qs
      induction qs with
      | nil =>
        intro accG accW hacc
        refine ⟨by simp, hacc, ?_⟩
        intro pre inp _ _ _
        simp
      | cons w qs ih =>
        intro accG accW hacc
        simp only [List.foldl_cons]
        have hacc' : ∀ g ∈ accG ++ [Gate.mk .or [accW, w]], g.op = .or ∧ g.inputs.length = 2 := by
          intro g hg
          rcases List.mem_append.mp hg with h1 | h2
          · exact hacc g h1
          · rw [List.mem_singleton.mp h2]; exact ⟨rfl, rfl⟩
        have hrec := ih (accG ++ [Gate.mk .or [accW, w]]) (base + accG.length) hacc'
        refine ⟨?_, hrec.2.1, ?_⟩
        · rw [hrec.1, List.length_append]; simp; omega
        · intro pre inp hbase haccW hqs
          have hw_lt : w < base := hqs w (List.mem_cons_self)
          have hstep := hrec.2.2 pre inp hbase (by rw [List.length_append]; simp)
            (fun w' hw' => hqs w' (List.mem_cons_of_mem _ hw'))
          rw [hstep]
          have hgate : ((Circuit.mk (pre ++ (accG ++ [Gate.mk .or [accW, w]])) 0).wires inp).getD
              (base + accG.length) false =
              (((Circuit.mk (pre ++ accG) 0).wires inp).getD accW false ||
                ((Circuit.mk pre 0).wires inp).getD w false) := by
            rw [← List.append_assoc]
            have hidx : base + accG.length = inp.length + (pre ++ accG).length := by
              rw [List.length_append]; omega
            rw [hidx, wires_getD_step (pre ++ accG) (Gate.mk .or [accW, w]) inp 0]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
              id_eq, Bool.or_false]
            congr 1
            rw [wires_append]
            exact wires_getD_prefix accG _ 0 w (by rw [wires_length]; omega)
          rw [hgate]
          simp [Bool.or_assoc]
    have h := hgen ws [] cur (by simp)
    simpa [orFold] using h
  cases hallW_eq : allWires with
  | nil => rw [hallW_eq] at hallW_pos; simp at hallW_pos
  | cons w0 ws =>
    let baseOr := 2 * n + gFree.length + bp.1.length
    let of := orFold w0 ws baseOr
    let C : Circuit := ⟨gFree ++ bp.1 ++ of.1, of.2⟩
    have hC_mono : Monotone2 C := by
      intro g hg
      simp only [C, List.mem_append] at hg
      rcases hg with (hg1 | hg2) | hg3
      · simp only [gFree, List.mem_map] at hg1
        rcases hg1 with ⟨i, _, rfl⟩
        simp
      · exact hbp_len.2.2 g hg2
      · have h := (horFold_props w0 ws baseOr).2.1 g hg3
        exact ⟨Or.inr h.1, by omega⟩
    have hC_sz : C.size + 1 ≤ 2 * n := by
      simp only [C, Circuit.size, List.length_append]
      have hws : ws.length + 1 = n - M.card := by
        have := hallW_len; rw [hallW_eq] at this; simp at this; exact this
      have hgf : gFree.length = n - 2 * M.card := by simp [gFree, hfree_len]
      have hof : of.1.length = ws.length := (horFold_props w0 ws baseOr).1
      omega
    have hC_eval : ∀ x y, matchFn M x y = C.eval (List.ofFn x ++ List.ofFn y) := by
      intro x y
      let inp := List.ofFn x ++ List.ofFn y
      have hinp_len : inp.length = 2 * n := by simp [inp]; omega
      have hinp_L : ∀ i : Fin n, inp.getD i.val false = x i := by
        intro i; simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]
      have hinp_R : ∀ i : Fin n, inp.getD (n + i.val) false = y i := by
        intro i; simp [inp, List.getD_eq_getElem?_getD, List.getElem?_append_right]
      have hpre_free : ∀ k (hk : k < free.length),
          ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD (2 * n + k) false =
            (x (free[k]) && y (free[k])) := by
        intro k hk
        rw [wires_append]
        have hlen_f : ((Circuit.mk gFree 0).wires inp).length = 2 * n + gFree.length := by
          rw [wires_length, hinp_len]
        have hk_g : k < gFree.length := by simp [gFree, hk]
        rw [wires_getD_prefix bp.1 _ 0 (2 * n + k) (by rw [hlen_f]; omega)]
        rw [← hinp_len, wires_getD_gate (Circuit.mk gFree 0) inp k hk_g]
        have hgk : gFree[k] = Gate.mk .and [(free[k]).val, n + (free[k]).val] := by
          simp [gFree]
        rw [hgk]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true]
        have hlt1 : (free[k]).val < inp.length + k := by omega
        have hlt2 : n + (free[k]).val < inp.length + k := by omega
        simp only [hlt1, hlt2, ↓reduceIte]
        rw [wires_getD_prefix gFree inp 0 _ (by omega),
            wires_getD_prefix gFree inp 0 _ (by omega),
            hinp_L, hinp_R]
      have hpre_pairs : ∀ w ∈ bp.2, w < baseOr ∧
          ∃ e ∈ M, ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false =
            decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
        have hgen_ev : ∀ (ps : List (Finset (Fin n))) (pre : List Gate),
            (∀ e ∈ ps, e ∈ M) →
            let base := inp.length + pre.length
            let res := buildPairs ps base
            (∀ w ∈ res.2, w < base + res.1.length) ∧
            (∀ w ∈ res.2, ∃ e ∈ ps,
              ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) ∧
            (∀ e ∈ ps, ∃ w ∈ res.2,
              ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
          intro ps pre hps
          let base := inp.length + pre.length
          have hfold_ev : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
              (∀ e ∈ qs, e ∈ M) →
              (∀ w ∈ accW, w < base + accG.length) →
              (∀ w ∈ accW, ∃ e ∈ ps,
                ((Circuit.mk (pre ++ accG) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) →
              (∀ e ∈ qs, e ∈ ps) →
              let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
                let b := base + acc.1.length
                (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
              (∀ w ∈ res.2, w < base + res.1.length) ∧
              (∀ w ∈ res.2, ∃ e ∈ ps,
                ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) ∧
              (∀ e ∈ qs, ∃ w ∈ res.2,
                ((Circuit.mk (pre ++ res.1) 0).wires inp).getD w false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true))) := by
            intro qs
            induction qs with
            | nil =>
              intro accG accW _ hlt hev _
              exact ⟨hlt, hev, by simp⟩
            | cons e qs ih =>
              intro accG accW hqs hlt hev hsub
              have heM : e ∈ M := hqs e (List.mem_cons_self)
              have he2 : e.card = 2 := (hM.1 e heM).1
              have hne : e.Nonempty := Finset.card_pos.mp (by omega)
              let a := e.min' hne
              let b := e.max' hne
              have hab : a ≠ b := by
                intro h
                have : ∀ z ∈ e, z = a := fun z hz =>
                  le_antisymm (h ▸ Finset.le_max' e z hz) (Finset.min'_le e z hz)
                have hsub1 : e ⊆ {a} := fun z hz => Finset.mem_singleton.mpr (this z hz)
                have hle1 := Finset.card_le_card hsub1
                simp at hle1; omega
              have he_eq : e = {a, b} := by
                have hsub2 : ({a, b} : Finset (Fin n)) ⊆ e := by
                  intro z hz
                  rcases Finset.mem_insert.mp hz with rfl | hz
                  · exact Finset.min'_mem e hne
                  · rw [Finset.mem_singleton.mp hz]; exact Finset.max'_mem e hne
                exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hab, he2])).symm
              let base0 := base + accG.length
              have hpg_eq : pairGateFn e base0 =
                  [Gate.mk .or [a.val, n + b.val],
                   Gate.mk .or [b.val, n + a.val],
                   Gate.mk .and [base0, base0 + 1]] := by
                simp [pairGateFn, hne, a, b]
              let accG' := accG ++ pairGateFn e base0
              have hlen_accG' : accG'.length = accG.length + 3 := by simp [accG', hpg_eq]
              have hval_e : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 2) false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
                have h0 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD base0 false = (x a || y b) := by
                  have hsplit : pre ++ accG' = ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val], Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 = inp.length + (pre ++ accG).length := by
                      simp [base0, base, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 a.val (by omega),
                        wires_getD_prefix _ inp 0 (n + b.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, List.length_append]; omega
                have h1 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 1) false = (x b || y a) := by
                  have hsplit : pre ++ accG' = (((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val]]) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 + 1 = inp.length + ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]).length := by
                      simp [base0, base, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 b.val (by omega),
                        wires_getD_prefix _ inp 0 (n + a.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, List.length_append]; omega
                have h2 : ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 2) false =
                    (((Circuit.mk (pre ++ accG') 0).wires inp).getD base0 false &&
                      ((Circuit.mk (pre ++ accG') 0).wires inp).getD (base0 + 1) false) := by
                  have hsplit : pre ++ accG' = (((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]])) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit]
                  have hidx : base0 + 2 = inp.length + ((pre ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]]).length := by
                    simp [base0, base, List.length_append]; omega
                  rw [hidx, wires_getD_step]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  congr 1
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil, base0, base]; omega
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil, base0, base]; omega
                rw [h2, h0, h1, he_eq]
                simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
                  forall_eq_or_imp, forall_eq]
                cases x a <;> cases x b <;> cases y a <;> cases y b <;> decide
              simp only [List.foldl_cons]
              have hrec := ih accG' (accW ++ [base0 + 2])
                (fun e' he' => hqs e' (List.mem_cons_of_mem _ he'))
                (fun w hw => by
                  rcases List.mem_append.mp hw with h1 | h2
                  · have := hlt w h1; omega
                  · rw [List.mem_singleton.mp h2]; omega)
                (fun w hw => by
                  rcases List.mem_append.mp hw with h1 | h2
                  · obtain ⟨e', he', hev'⟩ := hev w h1
                    refine ⟨e', he', ?_⟩
                    have hpref : ((Circuit.mk (pre ++ accG') 0).wires inp).getD w false =
                        ((Circuit.mk (pre ++ accG) 0).wires inp).getD w false := by
                      have : pre ++ accG' = (pre ++ accG) ++ pairGateFn e base0 := by simp [accG', List.append_assoc]
                      rw [this, wires_append]
                      refine wires_getD_prefix _ _ 0 w ?_
                      have hlw : ((Circuit.mk (pre ++ accG) 0).wires inp).length = inp.length + pre.length + accG.length := by
                        simp only [wires_length, List.length_append, Nat.add_assoc]
                      rw [hlw]; exact hlt w h1
                    rw [hpref, hev']
                  · rw [List.mem_singleton.mp h2]
                    exact ⟨e, hsub e (List.mem_cons_self), hval_e⟩)
                (fun e' he' => hsub e' (List.mem_cons_of_mem _ he'))
              refine ⟨hrec.1, hrec.2.1, ?_⟩
              intro e' he'
              rcases List.mem_cons.mp he' with rfl | he_qs
              · have hmem_res : base0 + 2 ∈ (qs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG', accW ++ [base0 + 2])).2 := by
                  have hmono : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                      z ∈ aw → z ∈ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                        let b := base + acc.1.length
                        (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).2 := by
                    intro rs
                    induction rs with
                    | nil => intro _ _ _ hz; exact hz
                    | cons r rs ihr =>
                      intro ag aw z hz; simp only [List.foldl_cons]
                      exact ihr _ _ z (List.mem_append_left _ hz)
                  exact hmono qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by simp)
                have hpref_res : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                    z < base + ag.length →
                    ((Circuit.mk (pre ++ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                      let b := base + acc.1.length
                      (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).1) 0).wires inp).getD z false =
                    ((Circuit.mk (pre ++ ag) 0).wires inp).getD z false := by
                  intro rs
                  induction rs with
                  | nil => intro _ _ _ _; rfl
                  | cons r rs ihr =>
                    intro ag aw z hz
                    simp only [List.foldl_cons]
                    rw [ihr (ag ++ pairGateFn r (base + ag.length)) (aw ++ [base + ag.length + 2]) z
                      (by rw [List.length_append]; omega)]
                    have : pre ++ (ag ++ pairGateFn r (base + ag.length)) =
                        (pre ++ ag) ++ pairGateFn r (base + ag.length) := by simp [List.append_assoc]
                    rw [this, wires_append]
                    refine wires_getD_prefix _ _ 0 z ?_
                    have hlw : ((Circuit.mk (pre ++ ag) 0).wires inp).length = inp.length + pre.length + ag.length := by
                      simp only [wires_length, List.length_append, Nat.add_assoc]
                    rw [hlw]; exact hz
                refine ⟨base0 + 2, hmem_res, ?_⟩
                rw [hpref_res qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by omega), hval_e]
              · exact hrec.2.2 e' he_qs
          have h := hfold_ev ps [] [] hps (by simp) (by simp) (fun _ h => h)
          simpa [buildPairs, base] using h
        have h := hgen_ev pairs gFree (fun e he => Finset.mem_toList.mp he)
        have hbp_eq : bp = buildPairs pairs (inp.length + gFree.length) := by simp [bp, hinp_len]
        intro w hw
        rw [hbp_eq] at hw
        refine ⟨?_, ?_⟩
        · have h1 := h.1 w hw
          simpa [bp, baseOr, hinp_len, Nat.add_assoc] using h1
        · obtain ⟨e, he, hev⟩ := h.2.1 w hw
          exact ⟨e, Finset.mem_toList.mp he, by simpa [bp, hinp_len] using hev⟩
      have hpair_hit : ∀ e ∈ M, ∃ w ∈ bp.2,
          ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false =
            decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
        have hgen_hit : ∀ (qs : List (Finset (Fin n))) (accG : List Gate) (accW : List ℕ),
            (∀ e ∈ qs, e ∈ M) →
            let base := 2 * n + gFree.length
            let res := qs.foldl (fun (acc : List Gate × List ℕ) e =>
              let b := base + acc.1.length
              (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (accG, accW)
            ∀ e ∈ qs, ∃ w ∈ res.2,
              ((Circuit.mk (gFree ++ res.1) 0).wires inp).getD w false =
                decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
          intro qs
          induction qs with
          | nil => intro _ _ _ _ _ _ h; cases h
          | cons e qs ih =>
            intro accG accW hqs
            dsimp only
            have heM : e ∈ M := hqs e (List.mem_cons_self)
            have he2 : e.card = 2 := (hM.1 e heM).1
            have hne : e.Nonempty := Finset.card_pos.mp (by omega)
            let a := e.min' hne
            let b := e.max' hne
            have hab : a ≠ b := by
              intro h
              have : ∀ z ∈ e, z = a := fun z hz =>
                le_antisymm (h ▸ Finset.le_max' e z hz) (Finset.min'_le e z hz)
              have hle1 := Finset.card_le_card (fun z hz => Finset.mem_singleton.mpr (this z hz))
              simp at hle1; omega
            have he_eq : e = {a, b} := by
              have hsub2 : ({a, b} : Finset (Fin n)) ⊆ e := by
                intro z hz
                rcases Finset.mem_insert.mp hz with rfl | hz
                · exact Finset.min'_mem e hne
                · rw [Finset.mem_singleton.mp hz]; exact Finset.max'_mem e hne
              exact (Finset.eq_of_subset_of_card_le hsub2 (by rw [Finset.card_pair hab, he2])).symm
            let base := 2 * n + gFree.length
            let base0 := base + accG.length
            have hpg_eq : pairGateFn e base0 =
                [Gate.mk .or [a.val, n + b.val],
                 Gate.mk .or [b.val, n + a.val],
                 Gate.mk .and [base0, base0 + 1]] := by simp [pairGateFn, hne, a, b]
            let accG' := accG ++ pairGateFn e base0
            have hlen_accG' : accG'.length = accG.length + 3 := by simp [accG', hpg_eq]
            intro e' he'
            rw [List.foldl_cons]
            rcases List.mem_cons.mp he' with he'eq | he_qs
            · rw [he'eq]
              have hval_e : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 2) false =
                  decide ((∃ i ∈ e, x i = true ∧ y i = true) ∨ (∀ i ∈ e, x i = true) ∨ (∀ i ∈ e, y i = true)) := by
                have h0 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD base0 false = (x a || y b) := by
                  have hsplit : gFree ++ accG' = ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val], Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 = inp.length + (gFree ++ accG).length := by
                      simp [base0, base, hinp_len, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 a.val (by omega),
                        wires_getD_prefix _ inp 0 (n + b.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, hinp_len, List.length_append]; omega
                have h1 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 1) false = (x b || y a) := by
                  have hsplit : gFree ++ accG' = (((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]) ++
                      [Gate.mk .or [b.val, n + a.val]]) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit, wires_append, wires_getD_prefix]
                  · have hidx : base0 + 1 = inp.length + ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val]]).length := by
                      simp [base0, base, hinp_len, List.length_append]; omega
                    rw [hidx, wires_getD_step]
                    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
                      id_eq, Bool.or_false]
                    rw [wires_getD_prefix _ inp 0 b.val (by omega),
                        wires_getD_prefix _ inp 0 (n + a.val) (by omega),
                        hinp_L, hinp_R]
                  · rw [wires_length]; simp [base0, base, hinp_len, List.length_append]; omega
                have h2 : ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 2) false =
                    (((Circuit.mk (gFree ++ accG') 0).wires inp).getD base0 false &&
                      ((Circuit.mk (gFree ++ accG') 0).wires inp).getD (base0 + 1) false) := by
                  have hsplit : gFree ++ accG' = (((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]])) ++ [Gate.mk .and [base0, base0 + 1]] := by
                    simp [accG', hpg_eq, List.append_assoc]
                  rw [hsplit]
                  have hidx : base0 + 2 = inp.length + ((gFree ++ accG) ++ [Gate.mk .or [a.val, n + b.val],
                      Gate.mk .or [b.val, n + a.val]]).length := by
                    simp [base0, base, hinp_len, List.length_append]; omega
                  rw [hidx, wires_getD_step]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                    id_eq, Bool.and_true]
                  congr 1
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil,
                      base0, base, inp, List.length_ofFn]; omega
                  · conv_rhs => rw [wires_append]
                    refine (wires_getD_prefix _ _ 0 _ ?_).symm
                    simp only [wires_length, List.length_append, List.length_cons, List.length_nil,
                      base0, base, inp, List.length_ofFn]; omega
                rw [h2, h0, h1, he_eq]
                simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
                  forall_eq_or_imp, forall_eq]
                cases x a <;> cases x b <;> cases y a <;> cases y b <;> decide
              have hmono : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                  z ∈ aw → z ∈ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).2 := by
                intro rs
                induction rs with
                | nil => intro _ _ _ hz; exact hz
                | cons r rs ihr =>
                  intro ag aw z hz; simp only [List.foldl_cons]
                  exact ihr _ _ z (List.mem_append_left _ hz)
              have hpref_res : ∀ (rs : List (Finset (Fin n))) (ag : List Gate) (aw : List ℕ) (z : ℕ),
                  z < base + ag.length →
                  ((Circuit.mk (gFree ++ (rs.foldl (fun (acc : List Gate × List ℕ) e =>
                    let b := base + acc.1.length
                    (acc.1 ++ pairGateFn e b, acc.2 ++ [b + 2])) (ag, aw)).1) 0).wires inp).getD z false =
                  ((Circuit.mk (gFree ++ ag) 0).wires inp).getD z false := by
                intro rs
                induction rs with
                | nil => intro _ _ _ _; rfl
                | cons r rs ihr =>
                  intro ag aw z hz
                  simp only [List.foldl_cons]
                  rw [ihr (ag ++ pairGateFn r (base + ag.length)) (aw ++ [base + ag.length + 2]) z
                    (by rw [List.length_append]; omega)]
                  have : gFree ++ (ag ++ pairGateFn r (base + ag.length)) =
                      (gFree ++ ag) ++ pairGateFn r (base + ag.length) := by simp [List.append_assoc]
                  rw [this, wires_append]
                  refine wires_getD_prefix _ _ 0 z ?_
                  have hlw : ((Circuit.mk (gFree ++ ag) 0).wires inp).length = 2 * n + gFree.length + ag.length := by
                    rw [wires_length, hinp_len, List.length_append, Nat.add_assoc]
                  rw [hlw]; exact hz
              refine ⟨base0 + 2, hmono qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by simp), ?_⟩
              rw [hpref_res qs accG' (accW ++ [base0 + 2]) (base0 + 2) (by omega), hval_e]
            · exact ih accG' (accW ++ [base0 + 2]) (fun e'' he'' => hqs e'' (List.mem_cons_of_mem _ he'')) e' he_qs
        intro e he
        exact hgen_hit pairs [] [] (fun e' he' => Finset.mem_toList.mp he') e (Finset.mem_toList.mpr he)
      have hall_lt : ∀ w ∈ allWires, w < baseOr := by
        intro w hw
        rcases List.mem_append.mp hw with h1 | h2
        · simp only [freeWires, List.mem_map, List.mem_range] at h1
          rcases h1 with ⟨k, hk, rfl⟩
          have : gFree.length = free.length := by simp [gFree]
          omega
        · exact (hpre_pairs w h2).1
      have hC_any : C.eval inp =
          allWires.any (fun w => ((Circuit.mk (gFree ++ bp.1) 0).wires inp).getD w false) := by
        unfold Circuit.eval
        change ((Circuit.mk ((gFree ++ bp.1) ++ of.1) of.2).wires inp).getD of.2 false = _
        have h := (horFold_props w0 ws baseOr).2.2 (gFree ++ bp.1) inp
          (by rw [hinp_len, List.length_append]; omega)
          (hall_lt w0 (by rw [hallW_eq]; simp))
          (fun w hw => hall_lt w (by rw [hallW_eq]; exact List.mem_cons_of_mem _ hw))
        rw [hallW_eq, List.any_cons]
        exact h
      rw [hC_any]
      apply Bool.eq_iff_iff.mpr
      simp only [matchFn, decide_eq_true_eq, List.any_eq_true]
      constructor
      · rintro (⟨i, hxi, hyi⟩ | ⟨e, he, hex⟩)
        · by_cases hi : i ∈ covered
          · rcases Finset.mem_biUnion.mp hi with ⟨e, heM, hie⟩
            obtain ⟨w, hw, hwev⟩ := hpair_hit e heM
            refine ⟨w, List.mem_append_right _ hw, ?_⟩
            rw [hwev]
            exact decide_eq_true (Or.inl ⟨i, hie, hxi, hyi⟩)
          · have hi_free : i ∈ free := Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
            obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hi_free
            refine ⟨2 * n + k, List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩), ?_⟩
            rw [hpre_free k hk, hxi, hyi]; rfl
        · obtain ⟨w, hw, hwev⟩ := hpair_hit e he
          refine ⟨w, List.mem_append_right _ hw, ?_⟩
          rw [hwev]
          exact decide_eq_true (Or.inr hex)
      · rintro ⟨w, hw, hwt⟩
        rcases List.mem_append.mp hw with h1 | h2
        · simp only [freeWires, List.mem_map, List.mem_range] at h1
          rcases h1 with ⟨k, hk, rfl⟩
          rw [hpre_free k hk, Bool.and_eq_true] at hwt
          exact Or.inl ⟨free[k], hwt.1, hwt.2⟩
        · obtain ⟨e, heM, hwev⟩ := (hpre_pairs w h2).2
          rw [hwev, decide_eq_true_eq] at hwt
          rcases hwt with ⟨i, _, hxi, hyi⟩ | hex
          · exact Or.inl ⟨i, hxi, hyi⟩
          · exact Or.inr ⟨e, heM, hex⟩
    refine ⟨C, hC_mono, hC_sz, ?_, hC_eval⟩
    intro u v
    have h1 := (hC_eval (unitVec u) (unitVec v)).symm
    change C.eval (List.ofFn (unitVec u) ++ List.ofFn (unitVec v)) = decide (u = v)
    rw [h1]
    simp only [matchFn, unitVec]
    by_cases huv : u = v
    · rw [decide_eq_true huv]
      exact decide_eq_true (Or.inl ⟨u, by simp, by simp [huv]⟩)
    · rw [decide_eq_false huv]
      apply decide_eq_false
      rintro (⟨i, hiu, hiv⟩ | ⟨e, he, hL | hR⟩)
      · simp only [decide_eq_true_eq] at hiu hiv
        exact huv (hiu.symm.trans hiv)
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hM.1 e he).1
        have ha : a = u := decide_eq_true_eq.mp (hL a (Finset.mem_insert_self _ _))
        have hb : b = u := decide_eq_true_eq.mp (hL b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        exact hab (ha.trans hb.symm)
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hM.1 e he).1
        have ha : a = v := decide_eq_true_eq.mp (hR a (Finset.mem_insert_self _ _))
        have hb : b = v := decide_eq_true_eq.mp (hR b (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
        exact hab (ha.trans hb.symm)

private lemma matchFn_obs_empty {n : ℕ} (M : Finset (Finset (Fin n))) (hM : IsMatching Finset.univ M)
    (R : Finset (Fin n)) :
    matchFn M (fun i => decide (i ∈ R)) (fun _ => decide (False)) = true ↔
      ∃ e ∈ M, e ⊆ R := by
  simp only [matchFn, decide_eq_true_eq, decide_false, reduceCtorEq, and_false, exists_false,
    false_or]
  constructor
  · rintro ⟨e, he, hL | hR⟩
    · exact ⟨e, he, fun i hi => hL i hi⟩
    · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [(hM.1 e he).1]; decide)
      exact False.elim (hR a ha)
  · rintro ⟨e, he, hsub⟩
    exact ⟨e, he, Or.inl (fun i hi => hsub hi)⟩

private lemma matchFn_obs_pair {n : ℕ} (M : Finset (Finset (Fin n))) (hM : IsMatching Finset.univ M)
    (R S : Finset (Fin n)) :
    matchFn M (fun i => decide (i ∈ R)) (fun j => decide (j ∈ S)) = false ↔
      Disjoint R S ∧ ∀ e ∈ M, ¬ (e ⊆ R) ∧ ¬ (e ⊆ S) := by
  simp only [matchFn, decide_eq_false_iff_not, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Finset.disjoint_left.mpr (fun i hiR hiS => h1 i (decide_eq_true hiR) (decide_eq_true hiS)), ?_⟩
    intro e he
    have h := h2 e he
    push_neg at h
    exact ⟨fun hsub => by rcases h.1 with ⟨i, hi, hni⟩; exact hni (decide_eq_true (hsub hi)),
           fun hsub => by rcases h.2 with ⟨i, hi, hni⟩; exact hni (decide_eq_true (hsub hi))⟩
  · rintro ⟨hd, h2⟩
    refine ⟨fun i hiR hiS => Finset.disjoint_left.mp hd (decide_eq_true_eq.mp hiR) (decide_eq_true_eq.mp hiS), ?_⟩
    intro e he
    exact ⟨fun hL => (h2 e he).1 (fun i hi => decide_eq_true_eq.mp (hL i hi)),
           fun hR => (h2 e he).2 (fun i hi => decide_eq_true_eq.mp (hR i hi))⟩

private lemma matchFn_inj {n : ℕ} {M₁ M₂ : Finset (Finset (Fin n))}
    (h1 : IsMatching Finset.univ M₁) (h2 : IsMatching Finset.univ M₂)
    (heq : matchFn M₁ = matchFn M₂) : M₁ = M₂ := by
  ext e
  constructor
  · intro he1
    have hobs : matchFn M₁ (fun i => decide (i ∈ e)) (fun _ => decide False) = true :=
      (matchFn_obs_empty M₁ h1 e).mpr ⟨e, he1, subset_refl e⟩
    rw [heq, matchFn_obs_empty M₂ h2 e] at hobs
    rcases hobs with ⟨e', he2, hsub⟩
    have hcard_eq : e'.card = e.card := by rw [(h2.1 e' he2).1, (h1.1 e he1).1]
    rwa [← Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)]
  · intro he2
    have hobs : matchFn M₂ (fun i => decide (i ∈ e)) (fun _ => decide False) = true :=
      (matchFn_obs_empty M₂ h2 e).mpr ⟨e, he2, subset_refl e⟩
    rw [← heq, matchFn_obs_empty M₁ h1 e] at hobs
    rcases hobs with ⟨e', he1, hsub⟩
    have hcard_eq : e'.card = e.card := by rw [(h1.1 e' he1).1, (h2.1 e he2).1]
    rwa [← Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)]


def Fits {n : Nat} (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n)))
    (f : (Fin n → Bool) → (Fin n → Bool) → Bool) : Prop :=
  (∃ C : Circuit, Monotone2 C ∧ C.size+1 ≤ 2*n ∧ Represents (fun i j : Fin n => decide (i=j)) C ∧
    ∀ x y, f x y = C.eval (List.ofFn x ++ List.ofFn y)) ∧
  (∀ R ∈ pos, f (fun i => decide (i ∈ R)) (fun j => decide (j ∈ (∅ : Finset (Fin n)))) = true) ∧
  (∀ z ∈ neg, f (fun i => decide (i ∈ z.1)) (fun j => decide (j ∈ z.2)) = false)

def Eligible {n : Nat} (pos : List (Finset (Fin n))) (neg : List (Finset (Fin n) × Finset (Fin n)))
    (M : Finset (Finset (Fin n))) : Prop :=
  IsMatching Finset.univ M ∧ (∀ R ∈ pos, ∃ e ∈ M, e ⊆ R) ∧
  ∀ z ∈ neg, Disjoint z.1 z.2 ∧ ∀ e ∈ M, ¬ e ⊆ z.1 ∧ ¬ e ⊆ z.2

theorem fitting_count {n : Nat} (hn : 2 ≤ n) (pos : List (Finset (Fin n)))
    (neg : List (Finset (Fin n) × Finset (Fin n))) :
    Nat.card {f // Fits pos neg f} = Nat.card {M // Eligible pos neg M} := by
  classical
  let F : {M // Eligible pos neg M} → {f // Fits pos neg f} := fun ⟨M,hM⟩ =>
    ⟨matchFn M,exists_circuit_of_matching hn M hM.1,
      fun R hR => by simpa only [Finset.notMem_empty, decide_false] using (matchFn_obs_empty M hM.1 R).mpr (hM.2.1 R hR),
      fun z hz => (matchFn_obs_pair M hM.1 z.1 z.2).mpr (hM.2.2 z hz)⟩
  apply Nat.card_congr (Equiv.ofBijective F ?_).symm
  constructor
  · intro M N h
    apply Subtype.ext
    exact matchFn_inj M.property.1 N.property.1 (congrArg Subtype.val h)
  · rintro ⟨f,⟨C,hm,hs,hr,hv⟩,hp,hnn⟩
    obtain ⟨M,hM,he⟩ := optimal_circuit_is_matchFn hn C hm hs hr
    have hf : f = matchFn M := funext fun x => funext fun y => (hv x y).trans (he x y)
    subst f
    have hgood : Eligible pos neg M := by
      refine ⟨hM,?_,fun z hz => (matchFn_obs_pair M hM z.1 z.2).mp (hnn z hz)⟩
      intro R hR
      apply (matchFn_obs_empty M hM R).mp
      simpa only [Finset.notMem_empty, decide_false] using hp R hR
    exact ⟨⟨M,hgood⟩,rfl⟩

def banned {n : Nat} (E : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ.filter (fun e : Finset (Fin n) => e.card = 2)) \ E

noncomputable def negated {n : Nat} (E : Finset (Finset (Fin n))) :
    List (Finset (Fin n) × Finset (Fin n)) :=
  (banned E).toList.map (fun e => (e,∅))

theorem eligible_graph {n : Nat} (E M : Finset (Finset (Fin n))) :
    Eligible [] (negated E) M ↔ IsMatching Finset.univ M ∧ M ⊆ E := by
  constructor
  · intro h
    refine ⟨h.1,?_⟩
    intro e he
    by_contra bad
    have ban : e ∈ banned E := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h.1.1 e he).1⟩,bad⟩
    have row : (e, (∅ : Finset (Fin n))) ∈ negated E :=
      List.mem_map.mpr ⟨e,Finset.mem_toList.mpr ban,rfl⟩
    exact ((h.2.2 _ row).2 e he).1 (subset_refl e)
  · rintro ⟨hm,sub⟩
    refine ⟨hm,by simp,?_⟩
    intro z hz
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hz
    have bannedE := (Finset.mem_sdiff.mp (Finset.mem_toList.mp he : e ∈ banned E))
    have ec := (Finset.mem_filter.mp bannedE.1).2
    refine ⟨by simp,?_⟩
    intro g hg
    refine ⟨fun hge => ?_,fun hge => ?_⟩
    · have eqn : g = e := Finset.eq_of_subset_of_card_le hge (by rw [ec,(hm.1 g hg).1])
      exact bannedE.2 (eqn ▸ sub hg)
    · have bound := Finset.card_le_card hge
      simpa [(hm.1 g hg).1] using bound

theorem graph_count {n : Nat} (hn : 2 ≤ n) (E : Finset (Finset (Fin n))) :
    Nat.card {f // Fits [] (negated E) f} =
      Nat.card {M : Finset (Finset (Fin n)) // IsMatching Finset.univ M ∧ M ⊆ E} := by
  rw [fitting_count hn]
  exact Nat.card_congr (Equiv.subtypeEquivRight (eligible_graph E))

end PEqualNP.Outside.L_meta_32577

open PEqualNP.Outside.L_meta_32577

theorem PEqualNP.Outside.L_meta_32577 : ∀ (n : Nat), 2 ≤ n → ∀ (E : Finset (Finset (Fin n))), Nat.card {f // Fits [] (negated E) f} = Nat.card {M : Finset (Finset (Fin n)) // IsMatching Finset.univ M ∧ M ⊆ E} := fun _ hn E => graph_count hn E

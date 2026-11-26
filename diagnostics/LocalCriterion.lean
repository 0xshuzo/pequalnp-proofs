import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.Research

/- Wire evaluation and OR-reachability facts from the base proof L-meta-4005. -/
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩

open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]

open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma orIn_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)


open PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma graphFun_pairInput_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hadj, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.ne_of_adj hadj rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (G.ne_of_adj hadj rfl).elim
  · intro hadj
    exact ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩

/-- The OR-reachable input sets of an AND gate are a local test for its
    cleanliness whenever all earlier AND gates are clean. -/
theorem localCriterion {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (model : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and)
    (prior : ∀ j < k, (gateAt C j).op = GateOp.and → BelowF G C j) :
    BelowF G C k ↔
      ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1, G.Adj u v := by
  have hA := ao_of n C model
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  have leftSide : side (n := n) C k 0 = orIn n C a := by simp [side, opnd, hab]
  have rightSide : side (n := n) C k 1 = orIn n C b := by simp [side, opnd, hab]
  rw [leftSide, rightSide]
  constructor
  · intro clean u hu v hv
    let y := pairInput u v
    have input_u : W n C y u = true := by rw [W_input n C y u u.isLt]; simp [y, pairInput]
    have input_v : W n C y v = true := by rw [W_input n C y v v.isLt]; simp [y, pairInput]
    have on_a := orR_mono n C hA y a u ((orIn_iff n C hA a u).mp hu) input_u
    have on_b := orR_mono n C hA y b v ((orIn_iff n C hA b v).mp hv) input_v
    apply (graphFun_pairInput_iff G u v).mp
    apply clean y
    change W n C y (n + k) = true
    simp only [W_and n C y k hk hand a b hab ha hb, on_a, on_b, Bool.and_self]
  · intro adjacent x on_k
    by_contra independent
    change W n C x (n + k) = true at on_k
    rw [W_and n C x k hk hand a b hab ha hb, Bool.and_eq_true] at on_k
    have from_input : ∀ w < n + k, W n C x w = true → ∃ u ∈ orIn n C w, x u = true := by
      intro w hw on_w
      obtain ⟨r, path, leaf, on_r⟩ := orR_leaf_true n C hA x w (by omega) on_w
      rcases leaf with hr | ⟨j, rfl, hj, op⟩
      · refine ⟨⟨r, hr⟩, (orIn_iff n C hA w ⟨r, hr⟩).mpr path, ?_⟩
        rwa [W_input n C x r hr] at on_r
      · have le_w := orR_le n C hA w (n + j) path
        exact (independent (prior j (by omega) op x on_r)).elim
    obtain ⟨u, hu, xu⟩ := from_input a ha on_k.1
    obtain ⟨v, hv, xv⟩ := from_input b hb on_k.2
    exact independent ((graphFun_iff x).mpr ⟨u, v, adjacent u hu v hv, xu, xv⟩)

/-- A circuit has a dirty AND gate exactly when some AND gate has a
    nonadjacent pair in its two OR-reachable input sets. -/
theorem clean_iff_adjacent_sides {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (model : IsAO2 n C) :
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → BelowF G C k) ↔
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1, G.Adj u v) := by
  constructor
  · intro clean k hk hand
    exact (localCriterion G C model k hk hand (fun j hj => clean j (by omega))).mp (clean k hk hand)
  · intro adjacent k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hand
      exact (localCriterion G C model k hk hand (fun j hj => ih j hj (by omega))).mpr
        (adjacent k hk hand)

/-- An input activates some AND gate precisely when it activates an
    OR-reachable input on each side of some AND gate. -/
theorem activated_iff_both_sides {n : ℕ} (C : Circuit) (model : IsAO2 n C) (x : Fin n → Bool) :
    (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ gateVal n C k x = true) ↔
    (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
      (∃ u ∈ side (n := n) C k 0, x u = true) ∧ (∃ v ∈ side (n := n) C k 1, x v = true)) := by
  classical
  have hA := ao_of n C model
  constructor
  · intro existsOn
    let k := Nat.find existsOn
    obtain ⟨hk, hand, on_k⟩ := Nat.find_spec existsOn
    obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
    change W n C x (n + k) = true at on_k
    rw [W_and n C x k hk hand a b hab ha hb, Bool.and_eq_true] at on_k
    have support : ∀ w < n + k, W n C x w = true → ∃ u ∈ orIn n C w, x u = true := by
      intro w hw on_w
      obtain ⟨r, path, leaf, on_r⟩ := orR_leaf_true n C hA x w (by omega) on_w
      rcases leaf with hr | ⟨j, rfl, hj, hop⟩
      · refine ⟨⟨r, hr⟩, (orIn_iff n C hA w ⟨r, hr⟩).mpr path, ?_⟩
        rwa [W_input n C x r hr] at on_r
      · have leafBound := orR_le n C hA w (n + j) path
        have hjk : j < k := by omega
        exact (Nat.find_min existsOn hjk ⟨hj, hop, on_r⟩).elim
    exact ⟨k, hk, hand, by simpa [side, opnd, hab] using support a ha on_k.1,
      by simpa [side, opnd, hab] using support b hb on_k.2⟩
  · rintro ⟨k, hk, hand, ⟨u, hu, xu⟩, ⟨v, hv, xv⟩⟩
    obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
    have hu' : u ∈ orIn n C a := by simpa [side, opnd, hab] using hu
    have hv' : v ∈ orIn n C b := by simpa [side, opnd, hab] using hv
    have on_a := orR_mono n C hA x a u ((orIn_iff n C hA a u).mp hu')
      ((W_input n C x u u.isLt).trans xu)
    have on_b := orR_mono n C hA x b v ((orIn_iff n C hA b v).mp hv')
      ((W_input n C x v v.isLt).trans xv)
    refine ⟨k, hk, hand, ?_⟩
    change W n C x (n + k) = true
    simp only [W_and n C x k hk hand a b hab ha hb, on_a, on_b, Bool.and_self]

/-- At each specified vertex the singleton obstruction is exactly membership
    in the intersection of the two OR-reachable input sets of an AND gate. -/
theorem singleton_iff_common_input {n : ℕ} (C : Circuit) (model : IsAO2 n C) (u : Fin n) :
    (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
      gateVal n C k (PEqualNP.SplitCount.unitInput u) = true) ↔
    (∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧
      u ∈ side (n := n) C k 0 ∧ u ∈ side (n := n) C k 1) := by
  simpa [PEqualNP.SplitCount.unitInput] using activated_iff_both_sides C model (PEqualNP.SplitCount.unitInput u)

/- Gate substitution and erasure lemmas from the base proof L-meta-5126. -/
namespace Exchange
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount Finset
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
lemma nM {α β:Type} {st:List α ->β ->List α} {F:List α ->β ->α} (hst:∀a g,st a g=a++[F a g]) (d:α) (gs:List β) (init:List α):(gs.foldl st init).length=init.length+gs.length/\(∀i< init.length,(gs.foldl st init).getD i d=init.getD i d)/\∀j (hj:j<gs.length),∃p:List α,p.length=init.length+j/\(∀i<p.length,p.getD i d=(gs.foldl st init).getD i d)/\(gs.foldl st init).getD (init.length+j) d=F p gs[j]:=by
 obtain rfl:st=λa g=>a++[F a g]:=by funext a g;exact hst a g
 induction gs using List.reverseRecOn with
 |nil=>simp
 |append_singleton gs g ih=>
  obtain⟨h1,h2,h3⟩:=ih;simp only[List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton];have key:∀i< init.length+gs.length,(gs.foldl (λa g=>a++[F a g]) init++[F (gs.foldl (λa g=>a++[F a g]) init) g]).getD i d=(gs.foldl (λa g=>a++[F a g]) init).getD i d:=λi hi=>by
   simp[List.getD_eq_getElem?_getD,List.getElem?_append_left (h1▸hi)]
  refine⟨by omega,λi hi=>by rw[key i (by omega),h2 i hi],λj hj=>?_⟩;rcases Nat.lt_or_ge j gs.length with h|h
  ·obtain⟨p,hp1,hp2,hp3⟩:=h3 j h;refine⟨p,hp1,λi hi=>by rw[key i (by omega),hp2 i hi],?_⟩;rw[key _ (by omega),hp3,List.getElem_append_left h]
  ·obtain rfl:j=gs.length:=by omega
   refine⟨_,h1,λi hi=>(key i (h1▸hi)).symm,?_⟩;simp[List.getD_eq_getElem?_getD,←h1]
lemma e6 {C:Circuit} {j:ℕ} (hj:j<C.gates.length):gateAt C j=C.gates[j]:=by
 simp[gateAt,hj]
lemma a5 (C:Circuit) (x:Fin n ->Bool):(∀v:Fin n,wireVal n C v x=x v)/\(∀w,n+C.gates.length≤w ->wireVal n C w x=false)/\∀j<C.gates.length,wireVal n C (n+j) x=(gateAt C j).op.eval ((gateAt C j).inputs.map λi=>if i<n+j then wireVal n C i x else false):=by
 have hf:=nM (st:=λ(w:List Bool) (g:Gate)=>w++[g.op.eval (g.inputs.map λi=>w.getD i false)]) (λ_ _=>rfl) false C.gates (List.ofFn x);simp only[List.length_ofFn]at hf;unfold wireVal Circuit.wires;refine⟨λv=>by simpa using hf.2.1 v v.2,λw hw=>?_,λj hj=>?_⟩
 ·rw[List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)];rfl
 ·obtain⟨p,hp1,hp2,hp3⟩:=hf.2.2 j hj;rw[hp3,e6 hj]
  congr 1
  apply List.map_congr_left;intro i _;split_ifs with h
  ·exact hp2 i (by omega)
  ·simp[List.getD_eq_getElem?_getD,List.getElem?_eq_none (show p.length≤ i by omega)]
lemma aZ {i j:ℕ}:InCone n C i j↔j<C.gates.length/\∃k<j,n+k∈(gateAt C j).inputs/\(i=k\/InCone n C i k):=by
 have hf:=nM (st:=coneStep n) (λ_ _=>rfl) [] C.gates [];unfold InCone cones;by_cases hj:j<C.gates.length
 ·obtain⟨p,hp1,hp2,hp3⟩:=hf.2.2 j hj;simp only[List.length_nil,Nat.zero_add]at hp1 hp3;rw[hp3,e6 hj];simp only[List.mem_flatMap,List.mem_filter,decide_eq_true_eq,List.mem_cons,hp1];constructor
  ·rintro⟨w,⟨hw,h1,h2⟩,h3⟩;refine⟨hj,w-n,by omega,by rwa[show n+(w-n)=w by omega],?_⟩;rwa[hp2 _ (by omega)]at h3
  ·rintro⟨_,k,hk,hw,h3⟩;refine⟨n+k,⟨hw,by omega,by omega⟩,?_⟩;rw[show n+k-n=k by omega,hp2 _ (by omega)];exact h3
 ·have h0:(C.gates.foldl (coneStep n) []).getD j []=[]:=by
   rw[List.getD_eq_getElem?_getD,List.getElem?_eq_none (by have:=hf.1;simp at this;omega)];rfl
  rw[h0];simp[hj]
lemma bA (C:Circuit) (x:Fin n ->Bool) (v:Fin n):wireVal n C v x=x v:=(a5 C x).1 v
def jW (C:Circuit):Prop:=∀k<C.gates.length,((gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or)/\(gateAt C k).inputs.length=2
lemma bZ:IsAO2 n C↔jW C/\ReadsBack n C:=by
 have hm:∀g∈C.gates,∃k<C.gates.length,gateAt C k=g:=λg hg=>by
  obtain⟨k,hk,rfl⟩:=List.mem_iff_getElem.mp hg;exact⟨k,hk,e6 hk⟩
 constructor
 ·rintro⟨h1,h2,h3⟩;exact⟨λk hk=>⟨h1 _ (e6 hk▸List.getElem_mem hk),h3 _ (e6 hk▸List.getElem_mem hk)⟩,h2⟩
 ·rintro⟨h1,h2⟩;refine⟨λg hg=>?_,h2,λg hg=>?_⟩<;>obtain⟨k,hk,rfl⟩:=hm g hg
  ·exact(h1 k hk).1
  ·exact(h1 k hk).2
lemma bO {C:Circuit} (h:jW C) {k:ℕ} (hk:k<C.gates.length):(gateAt C k).inputs=[opnd C k 0,opnd C k 1]:=by
 obtain⟨a,b,hab⟩:=List.length_eq_two.mp (h k hk).2;simp[opnd,hab]
lemma eS (h:IsAO2 n C) {k:ℕ} (hk:k<C.gates.length):(gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or:=((bZ.mp h).1 k hk).1
lemma nH (h:jW C) {x y:Fin n ->Bool} (hxy:∀v,x v=true ->y v=true) (w:ℕ):wireVal n C w x=true ->wireVal n C w y=true:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hw|hw
  ·have:=bA C x ⟨w,hw⟩;have:=bA C y ⟨w,hw⟩;simp_all
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rcases Nat.lt_or_ge k C.gates.length with hk|hk
   ·rw[(a5 C x).2.2 k hk,(a5 C y).2.2 k hk];rcases (h k hk).1 with hop|hop<;>simp only[hop,GateOp.eval,List.all_map,List.any_map,List.all_eq_true,List.any_eq_true,Function.comp,id]
    ·intro h1 i hi;have:=h1 i hi;split_ifs at this⊢with hlt;simp_all
    ·rintro⟨i,hi,h1⟩;refine⟨i,hi,?_⟩;split_ifs at h1⊢with hlt;simp_all
   ·simp[(a5 C x).2.1 (n+k) (by omega)]
lemma dJ (x:Fin n ->Bool):graphFun G ∅ x=true↔∃u v,G.Adj u v/\x u=true/\x v=true:=by simp[graphFun]
lemma aT (u v:Fin n):graphFun G ∅ (pairInput u v)=true↔G.Adj u v:=by
 simp only[dJ,pairInput,decide_eq_true_eq];constructor
 ·rintro⟨a,b,hab,rfl|rfl,rfl|rfl⟩;exacts[(G.irrefl hab).elim,hab,hab.symm,(G.irrefl hab).elim]
 ·exact λh=>⟨u,v,h,Or.inl rfl,Or.inr rfl⟩
def dY (m:ℕ) (g:ℕ ->Gate) (o:ℕ):Circuit:=⟨(List.range m).map g,o⟩
@[simp] lemma l1_mk_len (m:ℕ) (g:ℕ ->Gate) (o:ℕ):(dY m g o).gates.length=m:=by
 simp[dY]
lemma bR {m:ℕ} {g:ℕ ->Gate} {o k:ℕ} (hk:k<m):gateAt (dY m g o) k=g k:=by
 simp[dY,gateAt,hk]
lemma kO {n m:ℕ} {g:ℕ ->Gate} {o:ℕ}:IsAO2 n (dY m g o)↔∀k<m,((g k).op=GateOp.and\/(g k).op=GateOp.or)/\(g k).inputs.length=2/\∀i∈(g k).inputs,i<n+k:=by
 simp only[bZ,jW,ReadsBack,l1_mk_len];constructor
 ·rintro⟨h1,h2⟩ k hk;have:=h1 k hk;have:=h2 k hk;rw[bR hk]at*;tauto
 ·intro h;refine⟨λk hk=>?_,λk hk=>?_⟩<;>rw[bR hk]
  ·exact⟨(h k hk).1,(h k hk).2.1⟩
  ·exact(h k hk).2.2
lemma gM {n:ℕ} {C D:Circuit} (x:Fin n ->Bool) {m:ℕ} (hC:m≤C.gates.length) (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k):∀w<n+m,wireVal n C w x=wireVal n D w x:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw;rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA C x ⟨w,hn⟩).trans (bA D x ⟨w,hn⟩).symm
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rw[(a5 C x).2.2 k (by omega),(a5 D x).2.2 k (by omega),h k (by omega)]
   congr 1
   apply List.map_congr_left;intro i _;split_ifs with hi
   ·exact ih i hi (by omega)
   ·rfl
lemma mH {n:ℕ} {C D:Circuit} {m:ℕ} (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k) (i:ℕ):∀j<m,InCone n C i j ->InCone n D i j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hj hc;obtain⟨_,k,hk,hin,h3⟩:=aZ.mp hc;exact aZ.mpr ⟨by omega,k,hk,h j hj▸hin,h3.imp id (ih k hk (by omega))⟩
lemma aP {i:ℕ}:∀{j:ℕ},InCone n C i j ->i<j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hc;obtain⟨_,k,hk,_,rfl|h3⟩:=aZ.mp hc
  ·exact hk
  ·exact(ih k hk h3).trans hk
lemma dI {a k:ℕ} (hak:InCone n C a k):∀{j:ℕ},InCone n C k j ->InCone n C a j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hc;obtain⟨hj,k2,hk2,hin,rfl|h3⟩:=aZ.mp hc
  ·exact aZ.mpr ⟨hj,k,hk2,hin,Or.inr hak⟩
  ·exact aZ.mpr ⟨hj,k2,hk2,hin,Or.inr (ih k2 hk2 h3)⟩
lemma qT {n:ℕ} {D:Circuit} (h:jW D) {w:ℕ} (hw:wireVal n D w (λ_=>true)=false) (x:Fin n ->Bool):wireVal n D w x=false:=Bool.eq_false_iff.mpr λhx=>by
  have:=nH h (y:=λ_=>true) (λ_ _=>rfl) w hx;simp_all
def eJ (n:ℕ) (D:Circuit) (k:ℕ):Prop:=∀i∈(gateAt D k).inputs,i<n+k/\wireVal n D i (λ_=>true)=true
lemma rV {n:ℕ} {D:Circuit} (hD:jW D):∀j≤D.gates.length,∃(g':ℕ ->Gate) (m':ℕ) (κ:ℕ ->ℕ),IsAO2 n (dY m' g' 0)/\(∀w<n+j,wireVal n D w (λ_=>true)=true ->∃w'<n+m',(∀x,wireVal n (dY m' g' 0) w' x=wireVal n D w x)/\(n≤w' ->n≤w/\(w=n+κ (w'-n)\/InCone n D (κ (w'-n)) (w-n))))/\(∀k'<m',κ k'<j/\eJ n D (κ k')/\(g' k').op=(gateAt D (κ k')).op/\(∀x,wireVal n (dY m' g' 0) (n+k') x=wireVal n D (n+κ k') x)/\∀k''<k',κ k''<κ k')/\(∀k<j,eJ n D k ->∃k'<m',κ k'=k)/\(∀a' b',b'<m' ->InCone n (dY m' g' 0) a' b' ->InCone n D (κ a') (κ b')):=by
 intro j
 induction j with
 |zero=>
  intro _;refine⟨λ_=>⟨GateOp.or,[]⟩,0,id,kO.mpr (by simp),λw hw _=>⟨w,hw,λx=>?_,by omega⟩,by simp,by simp,by simp⟩;exact(bA _ x ⟨w,by omega⟩).trans (bA D x ⟨w,by omega⟩).symm
 |succ j ih=>
  intro hj;obtain⟨g',m',κ,ha,hb,hc,hd,he⟩:=ih (by omega);have hjl:j<D.gates.length:=by omega
  have hin:=bO hD hjl;by_cases hK:eJ n D j
  ·have hla:=hK (opnd D j 0) (by rw[hin];simp);have hlb:=hK (opnd D j 1) (by rw[hin];simp);obtain⟨a',ha',hav,haa⟩:=hb _ hla.1 hla.2;obtain⟨b',hb',hbv,hba⟩:=hb _ hlb.1 hlb.2;have hg:∀k<m',gateAt (dY m' g' 0) k=gateAt (dY (m'+1) (Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩) 0) k:=λk hk=>by
    rw[bR hk,bR (by omega),Function.update_of_ne (Nat.ne_of_lt hk)]
   have hW:=λx=>gM (n:=n) x (by simp) (by simp) hg;have hnew:∀x,wireVal n (dY (m'+1) (Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩) 0) (n+m') x=wireVal n D (n+j) x:=λx=>by
    rw[(a5 _ x).2.2 m' (by simp),(a5 D x).2.2 j hjl,bR (by omega),hin];simp[ha',hb',hla.1,hlb.1,←hW x a' ha',←hW x b' hb',hav x,hbv x]
   refine⟨Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩,m'+1,Function.update κ m' j,?_,?_,?_,?_,?_⟩
   ·rw[kO]at ha⊢;intro k hk;rcases Nat.lt_or_ge k m' with h|h
    ·simpa[Function.update_of_ne (Nat.ne_of_lt h)]using ha k h
    ·obtain rfl:k=m':=by omega
     simp[(hD j hjl).1,ha',hb']
   ·intro w hw hv;rcases Nat.lt_or_ge w (n+j)with h|h
    ·obtain⟨w',hw',h1,h2⟩:=hb w h hv;refine⟨w',by omega,λx=>by rw[←hW x w' hw',h1],λh3=>?_⟩;rw[Function.update_of_ne (by omega)];exact h2 h3
    ·obtain rfl:w=n+j:=by omega
     exact⟨n+m',by omega,hnew,λ_=>⟨by omega,Or.inl (by simp)⟩⟩
   ·intro k' hk';rcases Nat.lt_or_ge k' m' with h|h
    ·obtain⟨h1,h2,h3,h4,h5⟩:=hc k' h;rw[Function.update_of_ne (Nat.ne_of_lt h),Function.update_of_ne (Nat.ne_of_lt h)];refine⟨by omega,h2,h3,λx=>by rw[←hW x _ (by omega),h4],λk'' hk''=>?_⟩;rw[Function.update_of_ne (by omega)];exact h5 k'' hk''
    ·obtain rfl:k'=m':=by omega
     simp only[Function.update_self];refine⟨by omega,hK,trivial,hnew,λk'' hk''=>?_⟩;rw[Function.update_of_ne (by omega)];exact(hc k'' hk'').1
   ·intro k hk hKk;rcases Nat.lt_or_ge k j with h|h
    ·obtain⟨k',hk',rfl⟩:=hd k h hKk;exact⟨k',by omega,Function.update_of_ne (by omega) _ _⟩
    ·exact⟨m',by omega,by simp;omega⟩
   ·intro c' d' hd'lt hcone;have hcl:=aP hcone;rw[Function.update_of_ne (show c'≠m' by omega)];have hcg:=λc k hk=>mH (n:=n) (m:=m') (D:=dY m' g' 0) (by simp) (λk hk=>(hg k hk).symm) c k hk;rcases Nat.lt_or_ge d' m' with h|h
    ·rw[Function.update_of_ne (by omega)];exact he c' d' h (hcg c' d' h hcone)
    ·obtain rfl:d'=m':=by omega
     simp only[Function.update_self];obtain⟨_,k'',hk'',hmem,h3⟩:=aZ.mp hcone;rw[bR (by omega)]at hmem;have h3':c'=k''\/InCone n D (κ c') (κ k''):=h3.imp id λh=>he c' k'' hk'' (hcg c' k'' hk'' h);have key:∀u u',u∈(gateAt D j).inputs ->u<n+j ->(n≤u' ->n≤u/\(u=n+κ (u'-n)\/InCone n D (κ (u'-n)) (u-n))) ->n+k''=u' ->InCone n D (κ c') j:=by
      intro u u' hu hul hal heq;obtain⟨hnu,hal⟩:=hal (by omega);rw[←heq,show n+k''-n=k'' by omega]at hal;refine aZ.mpr ⟨hjl,u-n,by omega,by rwa[show n+(u-n)=u by omega],?_⟩;rcases h3' with rfl|h3'<;>rcases hal with hal|hal
      ·left;omega
      ·right;exact hal
      ·right;rwa[show u-n=κ k'' by omega]
      ·right;exact dI h3' hal
     simp only[Function.update_self,List.mem_cons,List.not_mem_nil,or_false]at hmem;rcases hmem with h|h
     ·exact key _ a' (by rw[hin];simp) hla.1 haa h
     ·exact key _ b' (by rw[hin];simp) hlb.1 hba h
  ·refine⟨g',m',κ,ha,?_,λk' hk'=>?_,?_,he⟩
   ·intro w hw hv;rcases Nat.lt_or_ge w (n+j)with h|h
    ·exact hb w h hv
    ·obtain rfl:w=n+j:=by omega
     have key:∀u,u∈(gateAt D j).inputs ->(∀x,wireVal n D (n+j) x=wireVal n D u x) ->u<n+j ->wireVal n D u (λ_=>true)=true ->∃w'<n+m',(∀x,wireVal n (dY m' g' 0) w' x=wireVal n D (n+j) x)/\(n≤w' ->n≤n+j/\(n+j=n+κ (w'-n)\/InCone n D (κ (w'-n)) (n+j-n))):=by
      intro u hu hval hul hut;obtain⟨w',hw',h1,h2⟩:=hb u hul hut;refine⟨w',hw',λx=>by rw[h1,hval],λh3=>⟨by omega,Or.inr ?_⟩⟩;obtain⟨hnu,h2⟩:=h2 h3;rw[show n+j-n=j by omega];refine aZ.mpr ⟨hjl,u-n,by omega,by rwa[show n+(u-n)=u by omega],?_⟩;rcases h2 with h2|h2
      ·left;omega
      ·right;exact h2
     have hval:=λx:Fin n ->Bool=>(a5 D x).2.2 j hjl;simp only[hin]at hval;have hK':¬((opnd D j 0<n+j/\wireVal n D (opnd D j 0) (λ_=>true)=true)/\(opnd D j 1<n+j/\wireVal n D (opnd D j 1) (λ_=>true)=true)):=by
      intro h;apply hK;intro i hi;rw[hin]at hi;simp at hi;rcases hi with rfl|rfl;exacts[h.1,h.2]
     have hd0:∀u,¬(u<n+j/\wireVal n D u (λ_=>true)=true) ->∀x,u<n+j ->wireVal n D u x=false:=λu hu x h=>qT hD (by simpa[h]using hu) x;rw[hval]at hv;rcases (hD j hjl).1 with hop|hop
     ·simp[hop,GateOp.eval]at hv;exact absurd ⟨⟨by tauto,by tauto⟩,⟨by tauto,by tauto⟩⟩ hK'
     ·by_cases h0:opnd D j 0<n+j/\wireVal n D (opnd D j 0) (λ_=>true)=true
      ·have h1:=hd0 _ (λh=>hK' ⟨h0,h⟩)
       exact key _ (by rw[hin];simp) (λx=>by
        rw[hval];simp[hop,GateOp.eval,h0.1]
        exact λhlt hv=>absurd hv (by simp[h1 x hlt])) h0.1 h0.2
      ·have h1:=hd0 _ h0;have h2:opnd D j 1<n+j/\wireVal n D (opnd D j 1) (λ_=>true)=true:=by
        simp[hop,GateOp.eval]at hv;tauto
       exact key _ (by rw[hin];simp) (λx=>by
        rw[hval];simp[hop,GateOp.eval,h2.1]
        exact λhlt hv=>absurd hv (by simp[h1 x hlt])) h2.1 h2.2
   ·obtain⟨h1,h2⟩:=hc k' hk';exact⟨by omega,h2⟩
   ·intro k hk hKk;rcases Nat.lt_or_ge k j with h|h
    ·exact hd k h hKk
    ·exact absurd ((show k=j by omega)▸hKk) hK
theorem lU {n:ℕ} (D:Circuit) (hD:jW D):∃(D':Circuit) (κ:ℕ ->ℕ),IsAO2 n D'/\(wireVal n D D.output (λ_=>true)=true ->circuitFun n D'=circuitFun n D)/\(∀w,wireVal n D w (λ_=>true)=true ->∃w'<n+D'.gates.length,∀x,wireVal n D' w' x=wireVal n D w x)/\(∀k'<D'.gates.length,κ k'<D.gates.length/\eJ n D (κ k')/\(gateAt D' k').op=(gateAt D (κ k')).op/\(∀x,gateVal n D' k' x=gateVal n D (κ k') x)/\∀k''<k',κ k''<κ k')/\(∀k<D.gates.length,eJ n D k ->∃k'<D'.gates.length,κ k'=k)/\(∀a' b',InCone n D' a' b' ->InCone n D (κ a') (κ b')):=by
 obtain⟨g',m',κ,ha,hb,hc,hd,he⟩:=rV (n:=n) hD _ le_rfl;have hlive:∀w,wireVal n D w (λ_=>true)=true ->w<n+D.gates.length:=λw hw=>by
   by_contra h;rw[(a5 D _).2.1 w (by omega)]at hw;cases hw
 obtain⟨o',ho'⟩:∃o',wireVal n D D.output (λ_=>true)=true ->∀x,wireVal n (dY m' g' 0) o' x=wireVal n D D.output x:=by
  by_cases h:wireVal n D D.output (λ_=>true)=true
  ·obtain⟨w',_,h1,_⟩:=hb _ (hlive _ h) h;exact⟨w',λ_=>h1⟩
  ·exact⟨0,λh'=>absurd h' h⟩
 refine⟨dY m' g' o',κ,ha,λh=>funext (ho' h),λw hw=>?_,λk' hk'=>?_,λk hk hK=>?_,λa' b' hc'=>?_⟩
 ·obtain⟨w',h1,h2,_⟩:=hb w (hlive w hw) hw;exact⟨w',by simpa using h1,h2⟩
 ·rw[l1_mk_len]at hk';obtain⟨h1,h2,h3,h4,h5⟩:=hc k' hk';exact⟨h1,h2,by rw[bR hk'];exact h3,h4,h5⟩
 ·simpa using hd k hk hK
 ·exact he a' b' (by simpa using(aZ.mp hc').1) hc'
lemma pJ {m m':ℕ} {κ:ℕ ->ℕ} {K:ℕ ->Prop} (hc:∀k'<m',κ k'<m/\K (κ k')/\∀k''<k',κ k''<κ k') (hd:∀k<m,K k ->∃k'<m',κ k'=k) (S:Finset ℕ):((∀k∈S,k<m/\¬K k) ->m'+S.card≤m)/\((∀k<m,k∉S ->K k) ->m≤m'+S.card):=by
 have hinj:Set.InjOn κ (range m'):=by
  intro a ha b hb hab;simp only[coe_range,Set.mem_Iio]at ha hb;rcases Nat.lt_trichotomy a b with h|h|h
  ·have:=(hc b hb).2.2 a h;omega
  ·exact h
  ·have:=(hc a ha).2.2 b h;omega
 have hcard:=card_image_of_injOn hinj;rw[card_range]at hcard;constructor
 ·intro hS;have hsub:(range m').image κ∪S⊆range m:=by
   intro k hk;simp only[mem_union,mem_image,mem_range]at hk⊢;rcases hk with⟨k',hk',rfl⟩|hk
   ·exact(hc k' hk').1
   ·exact(hS k hk).1
  have hdis:Disjoint ((range m').image κ) S:=by
   rw[disjoint_left];intro k hk hkS;simp only[mem_image,mem_range]at hk;obtain⟨k',hk',rfl⟩:=hk;exact(hS _ hkS).2 (hc k' hk').2.1
  have:=card_le_card hsub;rwa[card_union_of_disjoint hdis,hcard,card_range]at this
 ·intro hS;have hsub:range m⊆(range m').image κ∪S:=by
   intro k hk;simp only[mem_union,mem_image,mem_range]at hk⊢;by_cases hkS:k∈S
   ·exact Or.inr hkS
   ·obtain⟨k',hk',rfl⟩:=hd k hk (hS k hk hkS);exact Or.inl ⟨k',hk',rfl⟩
  have:=(card_le_card hsub).trans (card_union_le _ _);rwa[hcard,card_range]at this
lemma pE {ι:Type} {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) (l:List ι) (f g:ι ->Bool) (h:∀i∈l,f i=true ->g i=true):op.eval (l.map f)=true ->op.eval (l.map g)=true:=by
 rcases hop with rfl|rfl<;>simp only[GateOp.eval,List.all_map,List.any_map,List.all_eq_true,List.any_eq_true,Function.comp,id]
 ·exact λh1 i hi=>h i hi (h1 i hi)
 ·exact λ⟨i,hi,h1⟩=>⟨i,hi,h i hi h1⟩
lemma aA {k:ℕ}:k∈junk G C↔k<C.gates.length/\(gateAt C k).op=GateOp.and/\¬BelowF G C k:=by
 unfold junk gatesWhere;rw[mem_filter,mem_range];unfold IsDirtyAnd IsDirty BelowF;constructor
 ·rintro⟨h1,h2,_,x,hx,hF⟩;exact⟨h1,h2,λh=>by simp[h x hx]at hF⟩
 ·rintro⟨h1,h2,h3⟩;obtain⟨x,hx⟩:=not_forall.mp h3;exact⟨h1,h2,h1,x,(Classical.not_imp.mp hx).1,by simpa using(Classical.not_imp.mp hx).2⟩
lemma eD {n:ℕ} (D:Circuit) (hD:jW D) (hl:wireVal n D D.output (λ_=>true)=true) (S:Finset ℕ) (hS:∀k∈S,k<D.gates.length/\¬eJ n D k):∃C':Circuit,IsAO2 n C'/\circuitFun n C'=circuitFun n D/\C'.size+S.card≤D.size:=by
 obtain⟨D',κ,hA',hfun,-,hc,hd,-⟩:=lU (n:=n) D hD;exact⟨D',hA',hfun hl,(pJ (K:=eJ n D) (λk' hk'=>⟨(hc k' hk').1,(hc k' hk').2.1,(hc k' hk').2.2.2.2⟩) hd S).1 hS⟩
lemma uO (h:IsAO2 n C) (hle:∀x,circuitFun n C x=true ->graphFun G ∅ x=true) (hacc:∀u v,G.Adj u v ->circuitFun n C (pairInput u v)=true):circuitFun n C=graphFun G ∅:=by
 funext x
 rw[Bool.eq_iff_iff];refine⟨hle x,λhx=>?_⟩;obtain⟨u,v,huv,hu,hv⟩:=(dJ x).mp hx
 exact nH (bZ.mp h).1 (x:=pairInput u v) (λw hw=>by
  simp only[pairInput,decide_eq_true_eq]at hw;rcases hw with rfl|rfl<;>assumption)
  C.output (hacc u v huv)
def aL (C:Circuit) (j:ℕ) (g:Gate):Circuit:=dY C.gates.length (Function.update (gateAt C) j g) C.output
lemma b7 (h:IsAO2 n C) {j:ℕ} (hj:j<C.gates.length) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) {a b:ℕ} (ha:a<n+j) (hb:b<n+j) (x:Fin n ->Bool):IsAO2 n (aL C j ⟨op,[a,b]⟩)/\(aL C j ⟨op,[a,b]⟩).size=C.size/\(aL C j ⟨op,[a,b]⟩).output=C.output/\(∀k<C.gates.length,k≠j ->gateAt (aL C j ⟨op,[a,b]⟩) k=gateAt C k)/\(∀w<n+j,wireVal n (aL C j ⟨op,[a,b]⟩) w x=wireVal n C w x)/\wireVal n (aL C j ⟨op,[a,b]⟩) (n+j) x=op.eval [wireVal n C a x,wireVal n C b x]:=by
 have hg:∀k<C.gates.length,gateAt (aL C j ⟨op,[a,b]⟩) k=Function.update (gateAt C) j ⟨op,[a,b]⟩ k:=λk hk=>bR hk;have hl:(aL C j ⟨op,[a,b]⟩).gates.length=C.gates.length:=by simp[aL]
 have hW:=gM x (m:=j) (hl▸hj.le) hj.le λk hk=>by
  rw[hg k (by omega),Function.update_of_ne (by omega)]
 refine⟨kO.mpr λk hk=>?_,hl,rfl,λk hk hkj=>by rw[hg k hk,Function.update_of_ne hkj],hW,?_⟩
 ·rcases eq_or_ne k j with rfl|hkj
  ·rw[Function.update_self];exact⟨hop,rfl,by simp[ha,hb]⟩
  ·rw[Function.update_of_ne hkj];exact⟨((bZ.mp h).1 k hk).1,((bZ.mp h).1 k hk).2,(bZ.mp h).2 k hk⟩
 ·rw[(a5 _ x).2.2 j (by omega),hg j hj,Function.update_self];simp[ha,hb,hW a ha,hW b hb]
lemma lW {j:ℕ} {g:Gate} (hj:j<C.gates.length) (x:Fin n ->Bool) (he:g.op.eval (g.inputs.map λi=>if i<n+j then wireVal n C i x else false)=wireVal n C (n+j) x) (w:ℕ):wireVal n (aL C j g) w x=wireVal n C w x:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA _ x ⟨w,hn⟩).trans (bA C x ⟨w,hn⟩).symm
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hm:∀l:List ℕ,(l.map λi=>if i<n+k then wireVal n (aL C j g) i x else false)=l.map λi=>if i<n+k then wireVal n C i x else false:=λl=>List.map_congr_left λi _=>by split_ifs with h;exacts[ih i h,rfl]
  rcases Nat.lt_or_ge k C.gates.length with hk|hk
  ·rw[(a5 _ x).2.2 k (by simpa[aL]using hk),
    show gateAt (aL C j g) k=_ from bR hk,hm]
   rcases eq_or_ne k j with rfl|hkj
   ·rw[Function.update_self];exact he
   ·rw[Function.update_of_ne hkj];exact((a5 C x).2.2 k hk).symm
  ·rw[(a5 _ x).2.1 _ (by simp[aL];omega),(a5 C x).2.1 _ (by omega)]
theorem uJ (hA:IsAO2 n C) {j w:ℕ} (hj:j<C.gates.length) (hw:w<n+j) (he:∀x,wireVal n C (n+j) x=wireVal n C w x):∃C':Circuit,IsAO2 n C'/\circuitFun n C'=circuitFun n C/\C'.size+1≤C.size:=by
 have hv:=λx:Fin n ->Bool=>lW (g:=⟨GateOp.or,[w,n+C.gates.length]⟩) hj x (by simp[GateOp.eval,hw,he,not_lt.mpr hj.le]);have hl:(aL C j ⟨GateOp.or,[w,n+C.gates.length]⟩).gates.length=C.gates.length:=by
  simp[aL]
 have hg:∀k<C.gates.length,gateAt (aL C j ⟨GateOp.or,[w,n+C.gates.length]⟩) k=Function.update (gateAt C) j ⟨GateOp.or,[w,n+C.gates.length]⟩ k:=λk hk=>bR hk;by_cases hlive:wireVal n C C.output (λ_=>true)=true
 ·obtain⟨C',hA',hfun,hsz⟩:=eD _ (λk hk=>by
    rw[hl]at hk;rw[hg k hk];rcases eq_or_ne k j with rfl|hkj
    ·simp
    ·rw[Function.update_of_ne hkj];exact(bZ.mp hA).1 k hk)
   (by rw[hv];exact hlive) {j} λk hk=>by
    rw[mem_singleton.mp hk,hl];refine⟨hj,λhK=>?_⟩;have:=(hK (n+C.gates.length) (by rw[hg j hj,Function.update_self];simp)).1;omega
  exact⟨C',hA',hfun.trans (funext λx=>hv x C.output),by
   simp only[Circuit.size,hl,card_singleton]at hsz⊢;omega⟩
 ·refine⟨⟨[],n⟩,by simp[IsAO2,AndOrOnly,ReadsBack],funext λx=>?_,
   show 0+1≤C.gates.length by omega⟩
  show wireVal n ⟨[],n⟩ n x=wireVal n C C.output x;rw[(a5 _ x).2.1 n (by simp),qT (bZ.mp hA).1 (by simpa using hlive) x]
theorem d3 (hC:IsLeastAO G C) {j w:ℕ} (hj:j<C.gates.length) (hw:w<n+j):¬∀x,wireVal n C (n+j) x=wireVal n C w x:=λhe=>by
 obtain⟨C',hA',hf,hsz⟩:=uJ hC.1 hj hw he;have:=hC.2.2 C' hA' (hf.trans hC.2.1);omega
def fY (C D:Circuit) (j:ℕ):Prop:=D.gates.length=C.gates.length/\∀k<C.gates.length,k≠j ->gateAt D k=gateAt C k
def aG (n:ℕ) (C:Circuit) (j:ℕ):Circuit:=aL C j ⟨GateOp.and,[n+j,n+j]⟩
lemma cV (j:ℕ) (g:Gate):fY C (aL C j g) j:=⟨by simp[aL],λk hk hkj=>by
  rw[show gateAt (aL C j g) k=_ from bR hk,Function.update_of_ne hkj]⟩
lemma bJ (j:ℕ):fY C (aG n C j) j:=cV j _
lemma mJ {j:ℕ} (hj:j<C.gates.length) (x:Fin n ->Bool):wireVal n (aG n C j) (n+j) x=false:=by
 rw[aG,(a5 _ x).2.2 j (by simpa[aL]using hj),
  show gateAt (aL C j _) j=_ from bR hj,Function.update_self]
 simp[GateOp.eval]
lemma kQ {C₁ C₂:Circuit} {m j:ℕ} (h1:m≤C₁.gates.length) (h2:m≤C₂.gates.length) (hg:∀k<m,k≠j ->gateAt C₁ k=gateAt C₂ k) (hop:∀k<m,k≠j ->(gateAt C₁ k).op=GateOp.and\/(gateAt C₁ k).op=GateOp.or) (x:Fin n ->Bool) (hj:wireVal n C₁ (n+j) x=true ->wireVal n C₂ (n+j) x=true):∀w<n+m,wireVal n C₁ w x=true ->wireVal n C₂ w x=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw hx;rcases Nat.lt_or_ge w n with hn|hn
  ·rwa[bA C₂ x ⟨w,hn⟩,←bA C₁ x ⟨w,hn⟩]
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;by_cases hkj:k=j
  ·subst hkj;exact hj hx
  rw[(a5 C₁ x).2.2 k (by omega)]at hx;rw[(a5 C₂ x).2.2 k (by omega),←hg k (by omega) hkj];refine pE (hop k (by omega) hkj) _ _ _ (λi _ hi=>?_) hx;split_ifs at hi⊢with hik;exact ih i (by omega) (by omega) hi
lemma eB {D:Circuit} {j:ℕ} (hD:fY C D j) (x:Fin n ->Bool):∀w,w≠n+j ->(n≤w ->¬InCone n C j (w-n)) ->wireVal n D w x=wireVal n C w x:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hwj hc;rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA D x ⟨w,hn⟩).trans (bA C x ⟨w,hn⟩).symm
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hkj:k≠j:=λh=>hwj (by rw[h]);have hc':¬InCone n C j k:=by simpa using hc hn
  rcases Nat.lt_or_ge k C.gates.length with hk|hk
  ·rw[(a5 D x).2.2 k (by rw[hD.1];exact hk),(a5 C x).2.2 k hk,hD.2 k hk hkj]
   congr 1
   refine List.map_congr_left λi hi=>?_;split_ifs with hik
   ·refine ih i hik (λhe=>hc' (aZ.mpr ⟨hk,j,by omega,he▸hi,Or.inl rfl⟩)) λhni hcj=>hc' (aZ.mpr ⟨hk,i-n,by omega,by rwa[show n+(i-n)=i by omega],Or.inr hcj⟩)
   ·rfl
  ·rw[(a5 D x).2.1 _ (by rw[hD.1];omega),(a5 C x).2.1 _ (by omega)]
theorem cT (hC:IsLeastAO G C) {j:ℕ} (hj:j<C.gates.length) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) {a b:ℕ} (ha:a<n+j) (hb:b<n+j) (hle:∀x,op.eval [wireVal n C a x,wireVal n C b x]=true ->gateVal n C j x=true) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C j) C.output (pairInput u v)=true\/op.eval [wireVal n C a (pairInput u v),wireVal n C b (pairInput u v)]=true):IsLeastAO G (aL C j ⟨op,[a,b]⟩)/\(∀k∈junk G (aL C j ⟨op,[a,b]⟩),k=j\/k∈junk G C)/\∀k∈junk G C,k≠j ->¬InCone n C j k ->k∈junk G (aL C j ⟨op,[a,b]⟩):=by
 have hA:=hC.1;obtain⟨hA',hsz,hout,-,-,hval⟩:=b7 hA hj hop ha hb (λ_=>true);have hD:=cV (C:=C) j ⟨op,[a,b]⟩;set D:=aL C j ⟨op,[a,b]⟩;have hopC:∀k<C.gates.length,k≠j ->(gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or:=λk hk _=>eS hA hk;have hlen:=hD.1
 have hDC:∀x,∀w<n+C.gates.length,wireVal n D w x=true ->wireVal n C w x=true:=λx=>kQ (C₁:=D) (C₂:=C) (m:=C.gates.length) hlen.ge le_rfl (λk hk hkj=>hD.2 k hk hkj) (λk hk hkj=>by rw[hD.2 k hk hkj];exact eS hA hk) x (λh1=>by
    rw[(b7 hA hj hop ha hb x).2.2.2.2.2]at h1;exact hle x h1)
 have hlow:∀x,wireVal n D C.output x=true ->graphFun G ∅ x=true:=λx h1=>by
  rw[←show wireVal n C C.output x=graphFun G ∅ x from congrFun hC.2.1 x];by_cases ho:C.output<n+C.gates.length
  ·exact hDC x _ ho h1
  ·rw[(a5 D x).2.1 _ (by rw[hlen];omega)]at h1;cases h1
 have hacc':∀u v,G.Adj u v ->wireVal n D C.output (pairInput u v)=true:=by
  intro u v huv;have hF:wireVal n C C.output (pairInput u v)=true:=by
   rw[show wireVal n C C.output _=graphFun G ∅ _ from congrFun hC.2.1 _,aT];exact huv
  rcases hacc u v huv with h1|h1
  ·by_cases ho:C.output<n+C.gates.length
   ·have hK:fY C (aG n C j) j:=bJ j;refine kQ (C₁:=aG n C j) (C₂:=D) (m:=C.gates.length) hK.1.ge hlen.ge (λk hk hkj=>(hK.2 k hk hkj).trans (hD.2 k hk hkj).symm) (λk hk hkj=>by rw[hK.2 k hk hkj];exact eS hA hk) _ (λh2=>by rw[mJ hj]at h2;cases h2) _ ho h1
   ·rw[(a5 (aG n C j) _).2.1 _ (by simp[aG,aL];omega)]at h1;cases h1
  ·rw[lW hj _ (by simpa[ha,hb]using(show op.eval [wireVal n C a _,wireVal n C b _]=wireVal n C (n+j) _ from by rw[h1];exact(hle _ h1).symm))];exact hF
 have hF:circuitFun n D=graphFun G ∅:=by
  have:=uO (G:=G) hA' (λx h1=>hlow x (by rw[←hout];exact h1)) (λu v huv=>by show wireVal n D D.output _=true;rw[hout];exact hacc' u v huv);exact this
 refine⟨⟨hA',hF,λC' h1 h2=>hsz▸hC.2.2 C' h1 h2⟩,λk hk=>?_,λk hk hkj hc=>?_⟩
 ·obtain⟨hkl,hkop,hkb⟩:=aA.mp hk;rcases eq_or_ne k j with rfl|hkj
  ·exact Or.inl rfl
  right;rw[hlen]at hkl;rw[hD.2 k hkl hkj]at hkop;exact aA.mpr ⟨hkl,hkop,λhb'=>hkb λx hx=>hb' x (hDC x _ (by omega) hx)⟩
 ·obtain⟨hkl,hkop,hkb⟩:=aA.mp hk;have he:∀x,gateVal n D k x=gateVal n C k x:=λx=>eB hD x (n+k) (by omega) λ_=>by simpa using hc
  refine aA.mpr ⟨by rw[hlen];exact hkl,by rw[hD.2 k hkl hkj];exact hkop,λhb'=>hkb λx hx=>hb' x (by rw[he];exact hx)⟩
end Exchange

open PEqualNP.CleanedNonEdge

/-- If an earlier wire is below gate k, cutting out k loses an edge on which
    the earlier wire is false. Otherwise that wire could replace k. -/
theorem essential_edge_missed_by_subwire {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) (k w : ℕ) (hk : k < C.gates.length) (hw : w < n + k)
    (smaller : ∀ x, wireVal n C w x = true → gateVal n C k x = true) :
    ∃ a b : Fin n, G.Adj a b ∧
      wireVal n (Exchange.aG n C k) C.output (pairInput a b) = false ∧
      wireVal n C w (pairInput a b) = false := by
  classical
  by_contra noEdge
  let D := Exchange.aL C k ⟨GateOp.or, [w,w]⟩
  have low : ∀ x, GateOp.or.eval [wireVal n C w x, wireVal n C w x] = true →
      gateVal n C k x = true := by simpa [GateOp.eval] using smaller
  have covers : ∀ a b, G.Adj a b →
      wireVal n (Exchange.aG n C k) C.output (pairInput a b) = true ∨
      GateOp.or.eval [wireVal n C w (pairInput a b), wireVal n C w (pairInput a b)] = true := by
    intro a b adj
    cases hCut : wireVal n (Exchange.aG n C k) C.output (pairInput a b) with
    | true => exact Or.inl rfl
    | false =>
      right
      cases hWire : wireVal n C w (pairInput a b) with
      | false => exact (noEdge ⟨a,b,adj,hCut,hWire⟩).elim
      | true => rfl
  have leastD : IsLeastAO G D :=
    (Exchange.cT least hk (Or.inr rfl) hw hw low covers).1
  have hkD : k < D.gates.length := by simpa [D, Exchange.aL] using hk
  apply Exchange.d3 leastD hkD hw
  intro x
  have replaced := Exchange.b7 least.1 hk (op := GateOp.or) (Or.inr rfl) hw hw x
  change wireVal n (Exchange.aL C k ⟨GateOp.or, [w,w]⟩) (n+k) x =
    wireVal n (Exchange.aL C k ⟨GateOp.or, [w,w]⟩) w x
  rw [replaced.2.2.2.2.2, replaced.2.2.2.2.1 w hw]
  simp [GateOp.eval]

/-- A shared singleton at a product in a least circuit forces an indispensable
    edge with neither endpoint equal to that singleton. -/
theorem essential_edge_avoids_common_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (least : IsLeastAO G C) (k : ℕ) (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) (u : Fin n)
    (hu₀ : u ∈ side (n := n) C k 0) (hu₁ : u ∈ side (n := n) C k 1) :
    ∃ a b : Fin n, G.Adj a b ∧ a ≠ u ∧ b ≠ u ∧
      wireVal n (Exchange.aG n C k) C.output (pairInput a b) = false := by
  have model := ao_of n C least.1
  obtain ⟨_, l, r, ops, hl, hr⟩ := model k hk
  have lh : u ∈ orIn n C l := by simpa [side, opnd, ops] using hu₀
  have rh : u ∈ orIn n C r := by simpa [side, opnd, ops] using hu₁
  have smaller : ∀ x, wireVal n C u x = true → gateVal n C k x = true := by
    intro x xu
    have xl := orR_mono n C model x l u ((orIn_iff n C model l u).mp lh) xu
    have xr := orR_mono n C model x r u ((orIn_iff n C model r u).mp rh) xu
    change W n C x (n+k) = true
    simp only [W_and n C x k hk hand l r ops hl hr, xl, xr, Bool.and_self]
  obtain ⟨a,b,hab,cut,miss⟩ := essential_edge_missed_by_subwire G C least k u hk (by omega) smaller
  rw [Exchange.bA] at miss
  have neu : u ≠ a ∧ u ≠ b := by simpa [pairInput] using miss
  exact ⟨a,b,hab,Ne.symm neu.1,Ne.symm neu.2,cut⟩

end PEqualNP.Outside.L_meta_3754.Research

import PEqualNP.Defs

namespace PEqualNP.Outside.AuxSmall7971

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2)
open PEqualNP.MetaComplexity.NestedCover (gateAt ReadsBack)
open PEqualNP.EdgeOwnership (InCone cones coneStep)
open PEqualNP.GenericRejection (incidenceInput)

def appendStep {α : Type} (next : List α → Gate → α) (xs : List α) (g : Gate) :
    List α := xs ++ [next xs g]

lemma fold_length {α : Type} (next : List α → Gate → α) (gs : List Gate) (xs : List α) :
    (gs.foldl (appendStep next) xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, appendStep, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma fold_getD_lt {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    (gs.foldl (appendStep next) xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [appendStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma fold_prefix {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (j i : ℕ) (d : α)
    (hi : i < ((gs.take j).foldl (appendStep next) xs).length) :
    (gs.foldl (appendStep next) xs).getD i d =
      ((gs.take j).foldl (appendStep next) xs).getD i d := by
  calc
    _ = ((gs.take j ++ gs.drop j).foldl (appendStep next) xs).getD i d := by
      rw [List.take_append_drop]
    _ = _ := by rw [List.foldl_append, fold_getD_lt next _ _ i d hi]

lemma fold_at {α : Type} (next : List α → Gate → α) (gs : List Gate)
    (xs : List α) (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (appendStep next) xs).getD (xs.length + j) d =
      next ((gs.take j).foldl (appendStep next) xs) gs[j] := by
  let pre := (gs.take j).foldl (appendStep next) xs
  have hlen : pre.length = xs.length + j := by
    simp [pre, fold_length, Nat.min_eq_left (Nat.le_of_lt hj)]
  calc
    _ = ((gs.take j ++ gs.drop j).foldl (appendStep next) xs).getD (xs.length + j) d := by
      rw [List.take_append_drop]
    _ = _ := by
      rw [List.foldl_append, List.drop_eq_getElem_cons hj, List.foldl_cons]
      change ((gs.drop (j + 1)).foldl (appendStep next)
        (appendStep next pre gs[j])).getD (xs.length + j) d = _
      rw [← hlen, fold_getD_lt next _ _ _ _ (by simp [appendStep])]
      simp only [appendStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl pre.length),
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rfl

def wireNext (xs : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

def coneNext (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
    (fun w => (w - 26) :: cs.getD (w - 26) [])

def value (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) : Bool :=
  (C.wires (incidenceInput S.toLeft S.toRight)).getD w false

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gate_spec (C : Circuit) (hm : Monotone2 C) (j : ℕ) (hj : j < C.gates.length) :
    ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧
      (gateAt C j).inputs.length ≤ 2 := by
  rw [gateAt_eq C j hj]
  simpa using hm C.gates[j] (List.getElem_mem hj)

lemma input_length (S : Finset (Fin 13 ⊕ Fin 13)) :
    (incidenceInput S.toLeft S.toRight).length = 26 := by
  simp [incidenceInput]

def inputVertex (w : ℕ) (hw : w < 26) : Fin 13 ⊕ Fin 13 :=
  if hl : w < 13 then Sum.inl ⟨w, hl⟩ else Sum.inr ⟨w - 13, by omega⟩

lemma value_input (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) (hw : w < 26) :
    value C S w = true ↔ inputVertex w hw ∈ S := by
  let x := incidenceInput S.toLeft S.toRight
  change (C.gates.foldl (appendStep wireNext) x).getD w false = true ↔ _
  rw [fold_getD_lt wireNext _ x w false (by simpa [x, input_length] using hw)]
  simp only [x, incidenceInput, List.getD_eq_getElem?_getD]
  by_cases hl : w < 13
  · rw [List.getElem?_append_left (by simpa using hl)]
    simp only [List.getElem?_ofFn, hl, ↓reduceDIte, Option.getD_some,
      decide_eq_true_eq, inputVertex, Finset.mem_toLeft]
  · have hr : w - 13 < 13 := by omega
    rw [List.getElem?_append_right (by simpa using Nat.le_of_not_lt hl)]
    simp only [List.length_ofFn, List.getElem?_ofFn, hr, ↓reduceDIte, Option.getD_some,
      decide_eq_true_eq, inputVertex, hl, Finset.mem_toRight]

lemma value_oob (C : Circuit) (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ)
    (hw : 26 + C.gates.length ≤ w) : value C S w = false := by
  change (C.gates.foldl (appendStep wireNext) (incidenceInput S.toLeft S.toRight)).getD w false = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · simpa only [fold_length, input_length] using hw

lemma value_gate (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) :
    value C S (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (value C S)) := by
  let x := incidenceInput S.toLeft S.toRight
  have hx : x.length = 26 := input_length S
  change (C.gates.foldl (appendStep wireNext) x).getD (26 + j) false = _
  rw [← hx, fold_at wireNext _ x j hj false, gateAt_eq C j hj]
  unfold wireNext
  congr 1
  apply List.map_congr_left
  intro i hi
  have hlt := hb j hj i (by simpa only [gateAt_eq C j hj] using hi)
  exact (fold_prefix wireNext C.gates x j i false
    (by simpa [fold_length, hx, Nat.min_eq_left (Nat.le_of_lt hj)] using hlt)).symm

lemma cone_of_read (C : Circuit) (j w i : ℕ) (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) (hn : 26 ≤ w) (hlt : w < 26 + j)
    (hi : i = w - 26 ∨ InCone 26 C i (w - 26)) : InCone 26 C i j := by
  change i ∈ (C.gates.foldl (appendStep coneNext) []).getD j []
  have h := fold_at coneNext C.gates [] j hj []
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  refine List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
  · simpa only [gateAt_eq C j hj] using hw
  · simpa [fold_length, Nat.min_eq_left (Nat.le_of_lt hj)] using And.intro hn hlt
  · apply List.mem_cons.mpr
    rcases hi with rfl | hi
    · exact Or.inl rfl
    · right
      change i ∈ (C.gates.foldl (appendStep coneNext) []).getD (w - 26) [] at hi
      rw [fold_prefix coneNext C.gates [] j (w - 26) [] (by
        simp only [fold_length, List.length_nil, Nat.zero_add, List.length_take,
          Nat.min_eq_left (Nat.le_of_lt hj)]
        omega)] at hi
      exact hi

lemma and_value (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .and) :
    value C S (26 + j) = true ↔ ∀ w ∈ (gateAt C j).inputs, value C S w = true := by
  rw [value_gate C hb S j hj, ho]
  simp [GateOp.eval, List.all_eq_true]

lemma or_value (C : Circuit) (hb : ReadsBack 26 C) (S : Finset (Fin 13 ⊕ Fin 13))
    (j : ℕ) (hj : j < C.gates.length) (ho : (gateAt C j).op = .or) :
    value C S (26 + j) = true ↔ ∃ w ∈ (gateAt C j).inputs, value C S w = true := by
  rw [value_gate C hb S j hj, ho]
  simp [GateOp.eval, List.any_eq_true]

lemma value_mono (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    {S T : Finset (Fin 13 ⊕ Fin 13)} (hST : S ⊆ T) (w : ℕ) :
    value C S w = true → value C T w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hin : w < 26
    · rw [value_input C S w hin, value_input C T w hin]
      exact fun h => hST h
    by_cases hout : 26 + C.gates.length ≤ w
    · simp [value_oob C S w hout]
    let j := w - 26
    have hj : j < C.gates.length := by omega
    have hw : w = 26 + j := by omega
    rcases (gate_spec C hm j hj).1 with ha | ho
    · rw [hw, and_value C hb S j hj ha, and_value C hb T j hj ha]
      exact fun h i hi => ih i (by rw [hw]; exact hb j hj i hi) (h i hi)
    · rw [hw, or_value C hb S j hj ho, or_value C hb T j hj ho]
      rintro ⟨i, hi, ht⟩
      exact ⟨i, hi, ih i (by rw [hw]; exact hb j hj i hi) ht⟩

def AndFree (C : Circuit) (w : ℕ) : Prop :=
  26 ≤ w → (gateAt C (w - 26)).op ≠ .and ∧
    ∀ i, InCone 26 C i (w - 26) → (gateAt C i).op ≠ .and

lemma read_andFree (C : Circuit) (hb : ReadsBack 26 C) (j w : ℕ)
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs)
    (hfree : ∀ i, InCone 26 C i j → (gateAt C i).op ≠ .and) : AndFree C w := by
  intro hn
  have hlt := hb j hj w hw
  exact ⟨hfree _ (cone_of_read C j w _ hj hw hn hlt (Or.inl rfl)),
    fun i hi => hfree i (cone_of_read C j w i hj hw hn hlt (Or.inr hi))⟩

lemma collect_witnesses (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (S : Finset (Fin 13 ⊕ Fin 13)) (ws : List ℕ)
    (h : ∀ w ∈ ws, ∃ T ⊆ S, T.card ≤ 1 ∧ value C T w = true) :
    ∃ T ⊆ S, T.card ≤ ws.length ∧ ∀ w ∈ ws, value C T w = true := by
  induction ws with
  | nil => exact ⟨∅, Finset.empty_subset _, by simp⟩
  | cons w ws ih =>
    obtain ⟨U, hUS, hU, hu⟩ := h w (List.mem_cons_self ..)
    obtain ⟨V, hVS, hV, hv⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    refine ⟨U ∪ V, Finset.union_subset hUS hVS, ?_, ?_⟩
    · have hcard := Finset.card_union_le U V
      simp only [List.length_cons]
      omega
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact value_mono C hm hb Finset.subset_union_left _ hu
      · exact value_mono C hm hb Finset.subset_union_right _ (hv i hi)

lemma small_witness (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (hnest : ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j)
    (S : Finset (Fin 13 ⊕ Fin 13)) (w : ℕ) :
    ∀ k : ℕ, 1 ≤ k → (k < 2 → AndFree C w) → value C S w = true →
      ∃ T ⊆ S, T.card ≤ k ∧ value C T w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hk hfree htrue
    by_cases hin : w < 26
    · refine ⟨{inputVertex w hin}, Finset.singleton_subset_iff.mpr
        ((value_input C S w hin).mp htrue), by simpa using hk, ?_⟩
      exact (value_input C _ w hin).mpr (Finset.mem_singleton_self _)
    by_cases hout : 26 + C.gates.length ≤ w
    · simp [value_oob C S w hout] at htrue
    let j := w - 26
    have hj : j < C.gates.length := by omega
    have hw : w = 26 + j := by omega
    have hlt (i : ℕ) (hi : i ∈ (gateAt C j).inputs) : i < w := by
      rw [hw]
      exact hb j hj i hi
    rcases gate_spec C hm j hj with ⟨ha | ho, hlen⟩
    · have hk2 : 2 ≤ k := by
        by_contra! hk2
        exact ((hfree hk2) (by omega)).1 ha
      have hbelow (i : ℕ) (hi : InCone 26 C i j) : (gateAt C i).op ≠ .and :=
        fun hai => hnest ⟨i, j, hai, ha, hi⟩
      rw [hw, and_value C hb S j hj ha] at htrue
      obtain ⟨T, hTS, hT, ht⟩ := collect_witnesses C hm hb S (gateAt C j).inputs
        (fun i hi => ih i (hlt i hi) 1 (by decide)
          (fun _ => read_andFree C hb j i hj hi hbelow) (htrue i hi))
      exact ⟨T, hTS, hT.trans (hlen.trans hk2), by
        rw [hw, and_value C hb T j hj ha]
        exact ht⟩
    · rw [hw, or_value C hb S j hj ho] at htrue
      obtain ⟨i, hi, ht⟩ := htrue
      obtain ⟨T, hTS, hT, ht⟩ := ih i (hlt i hi) k hk
        (fun hk2 => read_andFree C hb j i hj hi ((hfree hk2) (by omega)).2) ht
      exact ⟨T, hTS, hT, by
        rw [hw, or_value C hb T j hj ho]
        exact ⟨i, hi, ht⟩⟩

end PEqualNP.Outside.AuxSmall7971

namespace PEqualNP.Outside.AuxReach7971

-- FRAGMENT fold    DEPENDS: (none)
-- Wire list as a fold over the gate list. C.wires x = W C.gates x (rfl), C.eval x = (W C.gates x).getD C.output false.
-- Exports:
--   def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
--   def W (gs : List Gate) (w : List Bool) := gs.foldl step w
--   wires_W C x : C.wires x = W C.gates x
--   eval_W C x : C.eval x = (W C.gates x).getD C.output false
--   circuitFun_W n C x : circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false
--   W_nil, W_cons : W (g :: gs) w = W gs (step w g), W_single : W [g] w = step w g
--   W_append : W (a ++ b) w = W b (W a w),  W_snoc : W (gs ++ [g]) w = step (W gs w) g
--   W_split j : W gs w = W (gs.drop j) (W (gs.take j) w)
--   step_len : (step w g).length = w.length + 1,  W_length : (W gs w).length = w.length + gs.length
--   getD_app_lt (i < l.length) : (l ++ l2).getD i false = l.getD i false
--   getD_app_len : (l ++ [v]).getD l.length false = v
--   getD_ge (l.length <= i) : l.getD i false = false
--   step_lt (i < w.length) : (step w g).getD i false = w.getD i false
--   step_last (k = w.length) : (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false)
--   W_prefix (i < w.length) : (W gs w).getD i false = w.getD i false
--   W_ge (w.length + gs.length <= i) : (W gs w).getD i false = false
--   W_snoc_getD : (W (gs ++ [g]) w).getD t false = if t = w.length + gs.length then (eval of g on W gs w) else (W gs w).getD t false
--   W_gate (j < gs.length) : (W gs w).getD (w.length + j) false
--        = gs[j].op.eval (gs[j].inputs.map fun i => if i < w.length + j then (W gs w).getD i false else false)
--   W_gate_pre (gs = pre ++ g :: post) : (W gs w).getD (w.length + pre.length) false = g.op.eval (g.inputs.map fun i => (W pre w).getD i false)
--   ofFn_getD (u < n) : (List.ofFn x).getD u false = x u
--   ofFn_getD_ge (n <= u) : (List.ofFn x).getD u false = false
--   split_gates (j < gs.length) : exists pre post, gs = pre ++ gs[j] :: post and pre.length = j
--   split2 (gs[j]? = some g) : exists pre post, pre.length = j, gs = pre ++ g :: post, and for all g2, gs.set j g2 = pre ++ g2 :: post
--   step_congr : same gate value on P gives same step
--   gateAt_eq (j < C.gates.length) : gateAt C j = C.gates[j],  gateAt_mem : gateAt C j in C.gates
--   gateAt_ge (C.gates.length <= j) : gateAt C j = (OR of nothing)
--   getElem?_gateAt : C.gates[j]? = some g -> gateAt C j = g and j < C.gates.length
--   eval_and_iff : GateOp.and.eval (l.map f) = true iff all i in l, f i = true
--   eval_or_iff : GateOp.or.eval (l.map f) = true iff exists i in l, f i = true
--   eval_and2 / eval_or2 : GateOp.and.eval [a, b] = (a and b) / GateOp.or.eval [a, b] = (a or b);  eval_or1 / eval_and1 : one operand copies it
-- Use: rewrite C.wires/eval/circuitFun into W, split the gate list at the changed gate with split2,
-- then compare W post (step P g1) with W post (step P g2) (W_prefix for wires below, W_gate for gate wires).

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

-- FRAGMENT mono    DEPENDS: fold
-- Wire values val, gate-by-gate value equations, monotonicity of AND/OR circuits, Monotone2 / IsAO2 facts,
-- minimal true points.
-- Exports:
--   def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false     (val C x u = (W C.gates x).getD u false by rfl)
--   eval_eq_val : C.eval x = val C x C.output ;  circuitFun_val : circuitFun n C x = val C (List.ofFn x) C.output
--   val_input (hx : x.length = n) (hu : u < n) : val C x u = x.getD u false
--   val_ofFn (u : Fin n) : val C (List.ofFn x) u.val = x u ;  val_ofFn_lt (hu : u < n) : val C (List.ofFn x) u = x (u, hu)
--   val_ge (hx : x.length = n) (hu : n + C.gates.length <= u) : val C x u = false
--   val_gate (hx : x.length = n) (hj : j < C.gates.length) :
--       val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => if i < n + j then val C x i else false)
--   val_gate_rb : same, without the if, when every input i of gate j has i < n + j (ReadsBack)
--   val_or  (op = or)  : val C x (n + r) = true iff exists i in inputs, i < n + r and val C x i = true
--   val_and (op = and) : val C x (n + r) = true iff all i in inputs, i < n + r and val C x i = true
--   and_val (IsAO2, op = and) : val C x (n + j) = (val of input 0 && val of input 1)  (inputs.getD 0 0 / getD 1 0)
--   or_val  (IsAO2, op = or)  : val C x (n + j) = (val of input 0 || val of input 1)
--   def OpMono R : AND and OR are monotone for relation R on Bool ;  opMono_eq : OpMono Eq ;  opMono_imp : OpMono (a = true -> b = true)
--   andOrOnly_of_monotone2 : Monotone2 C -> AndOrOnly C ;  andOrOnly_of_isAO2 : IsAO2 n C -> AndOrOnly C
--   mono (AndOrOnly C) (x <= y pointwise) : for all w, val C (ofFn x) w = true -> val C (ofFn y) w = true
--   circuitFun_mono (AndOrOnly C) (x <= y) : circuitFun n C x = true -> circuitFun n C y = true
--   monotone2_len : Monotone2 C -> g in C.gates -> g.inputs.length <= 2 ;  isAO2_len : IsAO2 n C -> g in C.gates -> g.inputs.length = 2
--   isAO2_rb : IsAO2 n C -> j < C.gates.length -> i in (gateAt C j).inputs -> i < n + j
--   def tr y : Finset of true coordinates ;  tr_lt : z < y strictly -> (tr z).card < (tr y).card
--   exists_min F x (F x = true) : exists y <= x, F y = true and every z < y (z <= y, z ne y) has F z = false
-- Use: induction on the wire index w (Nat.strong_induction_on) with val_input / val_ge / val_gate to compare two runs.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

theorem opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

theorem opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

theorem val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

theorem val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

theorem andOrOnly_of_monotone2 {C : Circuit} (h : Monotone2 C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := by
  intro g hg
  have h1 := (h g hg).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact h1

theorem andOrOnly_of_isAO2 {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.EdgeOwnership.AndOrOnly C := h.1

theorem monotone2_len {C : Circuit} (h : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length ≤ 2 := (h g hg).2

theorem isAO2_len {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {g : Gate} (hg : g ∈ C.gates) :
    g.inputs.length = 2 := h.2.2 g hg

theorem isAO2_rb {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) {i : ℕ} (hi : i ∈ (gateAt C j).inputs) : i < n + j :=
  h.2.1 j hj i hi

theorem mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

theorem circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

theorem and_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) &&
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

theorem or_val (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) (x : List Bool)
    (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    val C x (n + j) = (val C x ((gateAt C j).inputs.getD 0 0) ||
      val C x ((gateAt C j).inputs.getD 1 0)) := by
  obtain ⟨_, hRB, h2⟩ := hC
  have hlen : (gateAt C j).inputs.length = 2 := h2 _ (gateAt_mem hj)
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [val_gate hx hj, hop]
  rw [hab] at hrb ⊢
  have ha : a < n + j := hrb a (by simp)
  have hb : b < n + j := hrb b (by simp)
  simp [GateOp.eval, ha, hb]

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem exists_min {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) (hx : F x = true) :
    ∃ y : Fin n → Bool, (∀ i, y i = true → x i = true) ∧ F y = true ∧
      ∀ z : Fin n → Bool, (∀ i, z i = true → y i = true) → z ≠ y → F z = false := by
  let S : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun y => F y = true ∧ ∀ i, y i = true → x i = true)
  have hS : S.Nonempty := ⟨x, by simp [S, hx]⟩
  obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
  refine ⟨y, hyS.2, hyS.1, ?_⟩
  intro z hzy hne
  cases hz : F z
  · rfl
  · exfalso
    have hzS : z ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, fun i hi => hyS.2 i (hzy i hi)⟩
    have h1 := hmin z hzS
    have h2 := tr_lt z y hzy hne
    omega

-- FRAGMENT orreach    DEPENDS: fold mono
-- OR closures (PEqualNP.CleanedNonEdge.orStep / orSets / OrReaches), PEqualNP.TopForm.orIn, and the
-- value facts: a true gate makes every wire OR-reaching it true.
-- Exports (CNE = PEqualNP.CleanedNonEdge, TF = PEqualNP.TopForm):
--   wireVal_eq_val : CNE.wireVal n C w x = val C (List.ofFn x) w   (rfl)
--   gateVal_eq_val : PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j)   (rfl)
--   readVal_eq : CNE.readVal n C a w x = if w < n + a then val C (List.ofFn x) w else false   (rfl)
--   orSets_len gs cs : (gs.foldl (CNE.orStep n) cs).length = cs.length + gs.length
--   orSets_length : (CNE.orSets n C).length = C.gates.length
--   orSets_char gs : i in (gs.foldl (orStep n) []).getD j [] iff j < gs.length and (i = j or
--       (gs.getD j (OR of nothing)).op = or and exists w in its inputs, n <= w, w < n + j, i in (fold).getD (w - n) [])
--   orSets_mem_iff (hk : k < C.gates.length) : x in (orSets n C).getD k [] iff x = k or
--       ((gateAt C k).op = or and exists w in (gateAt C k).inputs, n <= w and w < n + k and x in (orSets n C).getD (w - n) [])
--   orReaches_iff : CNE.OrReaches n C (n + k) g iff k < C.gates.length and (g = k or
--       ((gateAt C k).op = or and exists i in (gateAt C k).inputs, i < n + k and OrReaches n C i g))
--   orReaches_self (hj : j < C.gates.length) : OrReaches n C (n + j) j
--   orReaches_step (j an OR gate, i in its inputs, i < n + j, OrReaches n C i g) : OrReaches n C (n + j) g
--   orReaches_bound : OrReaches n C w g -> n + g <= w and w < n + C.gates.length
--   orReaches_trans : OrReaches n C w (k) -> OrReaches n C (n + k) g -> OrReaches n C w g
--   reach_up (hx : x.length = n) (val C x (n + j) = true) : for all b, OrReaches n C b j -> val C x b = true
--   reach_up_wire : CNE.wireVal n C (n + j) x = true -> OrReaches n C b j -> CNE.wireVal n C b x = true
--   orIn_mem_filter : membership in Finset.filter with an arbitrary decidability proof
--   mem_orIn : i in TF.orIn n C w iff (i = w or exists k < C.gates.length, OrReaches n C w k and
--       (gateAt C k).op = or and i in (gateAt C k).inputs)
--   orIn_self (i : Fin n) : i in TF.orIn n C i
--   orIn_up (j an OR gate, i in its inputs, i < n + j) : a in orIn n C i -> a in orIn n C (n + j)
--   orIn_reach : OrReaches n C b k -> a in orIn n C (n + k) -> a in orIn n C b
--   orIn_val (hx : x.length = n) : a in orIn n C b -> val C x a = true -> val C x b = true
-- Use: orReaches_iff to unfold one level, reach_up / orIn_val to push truth up OR chains.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem wireVal_eq_val (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.wireVal n C w x = val C (List.ofFn x) w := rfl

theorem gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

theorem readVal_eq (n : ℕ) (C : Circuit) (a w : ℕ) (x : Fin n → Bool) :
    PEqualNP.CleanedNonEdge.readVal n C a w x =
      if w < n + a then val C (List.ofFn x) w else false := rfl

theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

theorem reach_up (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (j : ℕ)
    (hv : val C x (n + j) = true) :
    ∀ b : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C b j → val C x b = true := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hr
    have hnb : n ≤ b := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, b = n + k := ⟨b - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k j).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]
      exact hv
    · exact (val_or hx hk hop).mpr ⟨i, hi, hlt, ih i hlt hri⟩


end PEqualNP.Outside.AuxReach7971

namespace Shared7971
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.Outside.AuxSmall7971
abbrev I := Fin 13
abbrev V := I ⊕ I
abbrev Board := incidences singerLines3
def generic (U : Finset V) : Prop :=
  IsFree Board U ∧ U.toRight.card ≤ 3 ∧
  (∀ l, (U.toLeft ∩ singerLines3 l).card ≤ 2) ∧
  ∀ p, (U.toRight.filter fun l => p ∈ singerLines3 l).card ≤ 2
def cross (C : Circuit) (a b : Nat) : Prop :=
  ∀ A B : Finset V, A.card ≤ 2 → B.card ≤ 2 → generic (A ∪ B) →
    (value C A a && value C B b) = false
def flat (C : Circuit) : Prop :=
  ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ EdgeOwnership.InCone 26 C i j
def flag (e : I × I) : Finset V := {Sum.inl e.1, Sum.inr e.2}

theorem smallGeneric {T : Finset V} (hc : T.card ≤ 2) (hf : IsFree Board T) : generic T := by
  have hsum : T.toLeft.card + T.toRight.card = T.card := Finset.card_toLeft_add_card_toRight
  have hl : T.toLeft.card ≤ 2 := by omega
  have hr : T.toRight.card ≤ 2 := by omega
  exact ⟨hf, by omega, fun _ => (Finset.card_le_card Finset.inter_subset_left).trans hl,
    fun _ => (Finset.card_le_card (Finset.filter_subset _ _)).trans hr⟩

theorem flag_card (e : I × I) : (flag e).card = 2 := by simp [flag]
theorem flag_sub (e : I × I) (U : Finset V) : flag e ⊆ U ↔ PairIn U e := by
  simp [flag, PairIn, Finset.insert_subset_iff]

theorem reachTrue {C : Circuit} {j w : Nat} (h : CleanedNonEdge.OrReaches 26 C w j)
    (S : Finset V) (hs : value C S (26+j) = true) : value C S w = true :=
  PEqualNP.Outside.AuxReach7971.reach_up 26 C _ (input_length S) j hs w h

theorem commonEdge {C : Circuit} {a b j : Nat}
    (hm : Monotone2 C) (hb : ReadsBack 26 C) (hn : flat C) (hx : cross C a b)
    (ha : CleanedNonEdge.OrReaches 26 C a j) (hz : CleanedNonEdge.OrReaches 26 C b j)
    (S : Finset V) :
    value C S (26+j) = true ↔
    ∃ e ∈ Board, PairIn S e ∧ value C (flag e) (26+j) = true := by
  constructor
  · intro h
    obtain ⟨T, hTS, htwo, hT⟩ := small_witness C hm hb hn S (26+j) 2 (by decide)
      (fun h => (by omega : False).elim) h
    have hbad : ¬IsFree Board T := by
      intro hfree
      have hc := hx T T htwo htwo (by simpa using smallGeneric htwo hfree)
      rw [reachTrue ha T hT, reachTrue hz T hT] at hc
      contradiction
    unfold IsFree at hbad
    push_neg at hbad
    obtain ⟨e, he, hmem⟩ := hbad
    have hsub := (flag_sub e T).mpr hmem
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [flag_card]; exact htwo)
    exact ⟨e, he, (flag_sub _ _).mp (hsub.trans hTS), by simpa only [heq] using hT⟩
  · rintro ⟨e, _, he, hval⟩
    exact value_mono C hm hb ((flag_sub _ _).mpr he) _ hval
end Shared7971
namespace Shared7971
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.Outside.AuxSmall7971

theorem frontier (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack 26 C) (S : Finset V) :
    ∀ w, value C S w = true →
      (∃ v ∈ S, value C {v} w = true) ∨
      ∃ j < C.gates.length, CleanedNonEdge.OrReaches 26 C w j ∧
        (gateAt C j).op = .and ∧ value C S (26+j) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases small : w < 26
    · exact Or.inl ⟨inputVertex w small, (value_input C S w small).mp hw,
        (value_input C _ w small).mpr (Finset.mem_singleton_self _)⟩
    by_cases out : 26+C.gates.length ≤ w
    · simp [value_oob C S w out] at hw
    let j := w-26
    have jj : j < C.gates.length := by dsimp [j]; omega
    have ew : w=26+j := by dsimp [j]; omega
    rw [ew] at hw ⊢
    rcases (gate_spec C hm j jj).1 with ha | ho
    · exact Or.inr ⟨j, jj, Outside.AuxReach7971.orReaches_self 26 C j jj, ha, hw⟩
    obtain ⟨i, hi, hiv⟩ := (or_value C hb S j jj ho).mp hw
    have hlt := hb j jj i hi
    rcases ih i (by omega) hiv with ⟨v, hvs, hv⟩ | ⟨k, hk, hreach, hand, hval⟩
    · exact Or.inl ⟨v,hvs,(or_value C hb _ j jj ho).mpr ⟨i,hi,hv⟩⟩
    · exact Or.inr ⟨k,hk,Outside.AuxReach7971.orReaches_step 26 C j i k jj ho hi hlt hreach,hand,hval⟩

def privateAt (C : Circuit) (w z : Nat) (S : Finset V) : Prop :=
  ∃ j < C.gates.length, CleanedNonEdge.OrReaches 26 C w j ∧
    ¬ CleanedNonEdge.OrReaches 26 C z j ∧ (gateAt C j).op = .and ∧ value C S (26+j) = true

theorem privateOnFree {C : Circuit} {a b : Nat}
    (hm : Monotone2 C) (hb : ReadsBack 26 C) (hn : flat C) (hx : cross C a b)
    (S : Finset V) (hf : IsFree Board S)
    (h1 : value C S a = true) (h2 : value C S b = true) :
    privateAt C a b S ∨ privateAt C b a S := by
  have absent (j : Nat) (ha : CleanedNonEdge.OrReaches 26 C a j)
      (hz : CleanedNonEdge.OrReaches 26 C b j) (v : value C S (26+j) = true) : False := by
    obtain ⟨e,he,pair,_⟩ := (commonEdge hm hb hn hx ha hz S).mp v
    exact hf e he pair
  rcases frontier C hm hb S a h1 with ⟨u,hu,hua⟩ | ⟨i,hi,hr,hand,hval⟩
  · rcases frontier C hm hb S b h2 with ⟨v,hv,hvb⟩ | ⟨j,hj,hreach,hand,hval⟩
    · let U : Finset V := {u}
      let W : Finset V := {v}
      have sub : U ∪ W ⊆ S := Finset.union_subset (Finset.singleton_subset_iff.mpr hu)
        (Finset.singleton_subset_iff.mpr hv)
      have free : IsFree Board (U ∪ W) := fun e he ht => hf e he ⟨sub ht.1,sub ht.2⟩
      have c : (U ∪ W).card ≤ 2 := (Finset.card_union_le U W).trans (by simp [U,W])
      have hh := hx U W (by simp [U]) (by simp [W]) (smallGeneric c free)
      change (value C {u} a && value C {v} b)=false at hh
      simp [hua,hvb] at hh
    · exact Or.inr ⟨j,hj,hreach,fun ha => absent j ha hreach hval,hand,hval⟩
  · exact Or.inl ⟨i,hi,hr,fun hz => absent i hr hz hval,hand,hval⟩
end Shared7971
namespace Shared7971
open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.HeptadCover PEqualNP.GenericRejection
open PEqualNP.Outside.AuxSmall7971
def P (p : I) : V := Sum.inl p
def L (l : I) : V := Sum.inr l
theorem sameShoreP (p q : I) : IsFree Board {P p,P q} := by
  intro e _ he
  simpa [PairIn,P] using he.2
theorem sameShoreL (l m : I) : IsFree Board {L l,L m} := by
  intro e _ he
  simpa [PairIn,L] using he.1
theorem missing (p m : I) (h : p ∉ singerLines3 m) : IsFree Board {P p,L m} := by
  rintro ⟨u,v⟩ hin he
  have hp : u = p := by simpa [PairIn,P,L] using he.1
  have hm : v = m := by simpa [PairIn,P,L] using he.2
  subst u; subst v
  exact h (by simpa [Board,incidences] using hin)
theorem noSq : ∀ l m : I, l=m ∨ (singerLines3 l ∩ singerLines3 m).card ≤ 1 := by decide +kernel

def Adj : V → V → Prop
  | .inl p,.inr l => p ∈ singerLines3 l
  | .inr l,.inl p => p ∈ singerLines3 l
  | _,_ => False
theorem notRectangle (p q l m : I) (a : p ∈ singerLines3 l) (b : p ∈ singerLines3 m)
    (c : q ∈ singerLines3 l) (d : q ∈ singerLines3 m) : p=q ∨ l=m := by
  rcases noSq l m with h|h
  · exact Or.inr h
  · exact Or.inl (Finset.card_le_one.mp h p (Finset.mem_inter.mpr ⟨a,b⟩) q (Finset.mem_inter.mpr ⟨c,d⟩))
theorem square (u v t s : V) (A : Adj u t) (B : Adj u s) (C : Adj v t) (D : Adj v s) :
    u=v ∨ t=s := by
  cases u <;> cases v <;> cases t <;> cases s <;>
    simp_all only [Adj,Sum.inl.injEq,Sum.inr.injEq] <;>
    first | exact notRectangle _ _ _ _ A B C D | exact (notRectangle _ _ _ _ A C B D).symm

theorem adjacentPins {C : Circuit} {a b : Nat} (hx : cross C a b) (u v : V)
    (hu : value C {u} a = true) (hv : value C {v} b = true) : Adj u v := by
  by_contra h
  have fr : IsFree Board ({u} ∪ {v}) := by
    rw [Finset.singleton_union]
    cases u with
    | inl p =>
      cases v with
      | inl q => exact sameShoreP p q
      | inr m => exact missing p m h
    | inr l =>
      cases v with
      | inl q => simpa [Finset.pair_comm] using missing q l h
      | inr m => exact sameShoreL l m
  have hsmall : (({u} : Finset V) ∪ {v}).card ≤ 2 :=
    (Finset.card_union_le _ _).trans (by simp)
  have bad := hx _ _ (by simp : ({u} : Finset V).card ≤ 2)
    (by simp : ({v} : Finset V).card ≤ 2) (smallGeneric hsmall fr)
  simp [hu,hv] at bad

theorem rawCut {C : Circuit} {a b : Nat} (hx : cross C a b) :
    ∃ w ∈ [a,b], ∃ p : V, ∀ v : V, value C {v} w = true → v=p := by
  classical
  by_cases one : ∃ p : V, ∀ v : V, value C {v} a = true → v=p
  · exact ⟨a,by simp,one⟩
  have someA : ∃ u : V, value C {u} a = true := by
    by_contra! no
    exact one ⟨Sum.inl 0,fun v hv => by have h := no v; simp [hv] at h⟩
  obtain ⟨u,hu⟩ := someA
  have ne : ¬ ∀ v : V, value C {v} a = true → v=u := fun z => one ⟨u,z⟩
  push_neg at ne
  obtain ⟨v,hv,hn⟩ := ne
  by_cases someB : ∃ t : V, value C {t} b = true
  · obtain ⟨t,ht⟩ := someB
    refine ⟨b,by simp,t,fun s hs => ?_⟩
    exact (square v u s t (adjacentPins hx v s hv hs) (adjacentPins hx v t hv ht)
      (adjacentPins hx u s hu hs) (adjacentPins hx u t hu ht)).resolve_left hn
  · refine ⟨b,by simp,Sum.inl 0,fun s hs => (someB ⟨s,hs⟩).elim⟩

theorem rawPrice {C : Circuit} {a b : Nat} (hm : Monotone2 C) (hb : ReadsBack 26 C)
    (hx : cross C a b) (flags : ∀ e ∈ Board, value C (flag e) a = true ∧ value C (flag e) b = true) :
    ∃ w ∈ [a,b], ∃ p : V, ∀ e ∈ Board, p ∉ flag e →
    ∃ j < C.gates.length, CleanedNonEdge.OrReaches 26 C w j ∧ (gateAt C j).op = .and ∧
      value C (flag e) (26+j) = true := by
  obtain ⟨w,hw,p,hp⟩ := rawCut hx
  refine ⟨w,hw,p,fun e he he0 => ?_⟩
  have hwv : value C (flag e) w = true := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact (flags e he).1
    · exact (flags e he).2
  rcases frontier C hm hb (flag e) w hwv with ⟨t,ht,htw⟩|g
  · exact (he0 ((hp t htw) ▸ ht)).elim
  · exact g
end Shared7971

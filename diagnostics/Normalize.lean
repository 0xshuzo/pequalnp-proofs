import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace Normal3722

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp


lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h



-- The value of wire w of the gate list gs at the input x.
def wv {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn x)).getD w false

lemma wv_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (h : w < n) :
    wv gs x w = x ⟨w, h⟩ := by
  unfold wv
  rw [getD_wiresFrom_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma wv_out {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) (h : n + gs.length ≤ w) :
    wv gs x w = false := by
  unfold wv
  rw [List.getD_eq_default]
  rw [length_wiresFrom]
  simpa using h

lemma wv_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) (hrb : ∀ i ∈ g.inputs, i < n + k) :
    wv gs x (n + k) = g.op.eval (g.inputs.map (wv gs x)) := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have h := getD_wiresFrom_gate gs (List.ofFn x) k hk
  simp only [List.length_ofFn] at h
  unfold wv
  rw [h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [ite_eq_left (hrb i hi)]

-- The model: AND and OR gates reading exactly two earlier wires.
def AO (n : ℕ) (gs : List Gate) : Prop :=
  ∀ k g, gs[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a < n + k ∧ b < n + k

lemma ao_of (n : ℕ) (C : Circuit) (h : IsAO2 n C) : AO n C.gates := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k g hg
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  refine ⟨h1 _ hmem, ?_⟩
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (h3 _ hmem)
  have hr := h2 k hk
  rw [gateAt_eq C k hk, hab] at hr
  exact ⟨a, b, hab, hr a (by simp), hr b (by simp)⟩

lemma ao_to (n : ℕ) (gs : List Gate) (o : ℕ) (h : AO n gs) : IsAO2 n ⟨gs, o⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    exact (h k g hk).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    rw [gateAt_eq ⟨gs, o⟩ j hj] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j gs[j] (List.getElem?_eq_getElem hj')
    change i ∈ (gs[j]).inputs at hi
    rw [hab] at hi
    simp at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hg
    obtain ⟨_, a, b, hab, _, _⟩ := h k g hk
    simp [hab]

lemma wv_and {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k a b : ℕ)
    (hg : gs[k]? = some ⟨GateOp.and, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    wv gs x (n + k) = (wv gs x a && wv gs x b) := by
  rw [wv_gate gs x k _ hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  simp [GateOp.eval]

lemma wv_or {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k a b : ℕ)
    (hg : gs[k]? = some ⟨GateOp.or, [a, b]⟩) (ha : a < n + k) (hb : b < n + k) :
    wv gs x (n + k) = (wv gs x a || wv gs x b) := by
  rw [wv_gate gs x k _ hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)]
  simp [GateOp.eval]

-- Two gate lists that differ only at gate h: wires agree below h, and everywhere else
-- as soon as every read of wire n + h sees the same value.
lemma same_off {n : ℕ} (A B : List Gate) (h : ℕ) (x : Fin n → Bool)
    (hA : AO n A) (hlen : A.length = B.length)
    (hd : ∀ k, k ≠ h → A[k]? = B[k]?) :
    ∀ w, w ≠ n + h →
      (w < n + h ∨ ∀ (k : ℕ) (g : Gate), A[k]? = some g → n + h ∈ g.inputs → wv A x (n + h) = wv B x (n + h)) →
      wv A x w = wv B x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne hor
    by_cases hw : w < n
    · rw [wv_in A x w hw, wv_in B x w hw]
    · by_cases hw2 : w < n + A.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < A.length := by omega
        have hkh : k ≠ h := by omega
        have hgA : A[k]? = some A[k] := List.getElem?_eq_getElem hk
        have hgB : B[k]? = some A[k] := by rw [← hd k hkh]; exact hgA
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k _ hgA
        have hrb : ∀ i ∈ (A[k]).inputs, i < n + k := by
          intro i hi; rw [hab] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
        rw [wv_gate A x k _ hgA hrb, wv_gate B x k _ hgB hrb]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hih : i = n + h
        · rcases hor with hlt | hall
          · have := hrb i hi; omega
          · rw [hih]; exact hall k _ hgA (hih ▸ hi)
        · apply ih i (hrb i hi) hih
          rcases hor with hlt | hall
          · left; have := hrb i hi; omega
          · right; exact hall
      · rw [wv_out A x w (by omega), wv_out B x w (by omega)]

lemma all_mono (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, p i = true → q i = true) :
    (l.map p).all id = true → (l.map q).all id = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp, id]
  intro hp i hi
  exact h i hi (hp i hi)

lemma any_mono (l : List ℕ) (p q : ℕ → Bool) (h : ∀ i ∈ l, p i = true → q i = true) :
    (l.map p).any id = true → (l.map q).any id = true := by
  simp only [List.any_map, List.any_eq_true, Function.comp, id]
  rintro ⟨i, hi, hp⟩
  exact ⟨i, hi, h i hi hp⟩

-- Raising the value of gate h raises every wire.
lemma mono_off {n : ℕ} (A B : List Gate) (h : ℕ) (x : Fin n → Bool)
    (hA : AO n A) (hlen : A.length = B.length)
    (hd : ∀ k, k ≠ h → A[k]? = B[k]?)
    (hh : wv A x (n + h) = true → wv B x (n + h) = true) :
    ∀ w, wv A x w = true → wv B x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [wv_in A x w hw, wv_in B x w hw]; exact id
    · by_cases hw2 : w < n + A.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        by_cases hkh : k = h
        · rw [hkh]; exact hh
        · have hk : k < A.length := by omega
          have hgA : A[k]? = some A[k] := List.getElem?_eq_getElem hk
          have hgB : B[k]? = some A[k] := by rw [← hd k hkh]; exact hgA
          obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k _ hgA
          have hrb : ∀ i ∈ (A[k]).inputs, i < n + k := by
            intro i hi; rw [hab] at hi; simp at hi; rcases hi with rfl | rfl <;> assumption
          rw [wv_gate A x k _ hgA hrb, wv_gate B x k _ hgB hrb]
          rcases hop with hop | hop <;> rw [hop]
          · exact all_mono _ _ _ (fun i hi => ih i (hrb i hi))
          · exact any_mono _ _ _ (fun i hi => ih i (hrb i hi))
      · rw [wv_out A x w (by omega)]; intro hc; cases hc

-- Appending gates keeps the earlier wires.
lemma wv_append {n : ℕ} (A E : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w < n + A.length) :
    wv (A ++ E) x w = wv A x w := by
  unfold wv
  rw [wiresFrom_append, getD_wiresFrom_lt]
  rw [length_wiresFrom]
  simpa using hw

-- Deleting gate h, its readers reading wire r instead.
def sg (n h r w : ℕ) : ℕ := if w < n + h then w else if w = n + h then r else w - 1

def ren (s : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map s⟩

def del (n h r : ℕ) (gs : List Gate) : List Gate := (gs.eraseIdx h).map (ren (sg n h r))

lemma del_get (n h r : ℕ) (gs : List Gate) (j : ℕ) :
    (del n h r gs)[j]? = (gs[if j < h then j else j + 1]?).map (ren (sg n h r)) := by
  unfold del
  rw [List.getElem?_map, List.getElem?_eraseIdx]
  split_ifs <;> rfl

lemma del_len (n h r : ℕ) (gs : List Gate) (hh : h < gs.length) :
    (del n h r gs).length + 1 = gs.length := by
  unfold del
  rw [List.length_map, List.length_eraseIdx]
  simp only [hh, if_true]
  omega

lemma del_ao (n h r : ℕ) (gs : List Gate) (hA : AO n gs) (hr : r < n + h) :
    AO n (del n h r gs) := by
  intro j g' hg'
  rw [del_get] at hg'
  obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.1 hg'
  obtain ⟨hop, a, b, hab, ha, hb⟩ := hA _ g hg
  refine ⟨hop, sg n h r a, sg n h r b, by simp [ren, hab], ?_, ?_⟩
  · unfold sg; split_ifs at ha ⊢ <;> omega
  · unfold sg; split_ifs at hb ⊢ <;> omega

lemma ao_rb {n : ℕ} (gs : List Gate) (hA : AO n gs) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) :
    ∀ i ∈ g.inputs, i < n + k := by
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k g hg
  intro i hi
  rw [hab] at hi
  simp at hi
  rcases hi with rfl | rfl <;> assumption

lemma set_ao {n : ℕ} (gs : List Gate) (hA : AO n gs) (h r : ℕ) (hr : r < n + h) :
    AO n (gs.set h ⟨GateOp.or, [r, r]⟩) := by
  intro k g hg
  by_cases hk : k = h
  · subst hk
    by_cases hlt : k < gs.length
    · rw [List.getElem?_set_self hlt] at hg
      cases hg
      exact ⟨Or.inr rfl, r, r, rfl, hr, hr⟩
    · rw [List.getElem?_eq_none (by simpa using hlt)] at hg
      cases hg
  · rw [List.getElem?_set_ne (Ne.symm hk)] at hg
    exact hA k g hg

lemma set_copy {n : ℕ} (gs : List Gate) (h r : ℕ) (x : Fin n → Bool)
    (hh : h < gs.length) (hr : r < n + h) :
    wv (gs.set h ⟨GateOp.or, [r, r]⟩) x (n + h) = wv (gs.set h ⟨GateOp.or, [r, r]⟩) x r := by
  rw [wv_or _ x h r r (List.getElem?_set_self hh) hr hr, Bool.or_self]

-- The deleted circuit computes, at the renamed wire, what the circuit with gate h
-- turned into a copy of wire r computes.
lemma del_val {n : ℕ} (gs : List Gate) (h r : ℕ) (x : Fin n → Bool)
    (hA : AO n gs) (hh : h < gs.length) (hr : r < n + h) :
    ∀ w, wv (del n h r gs) x (sg n h r w) = wv (gs.set h ⟨GateOp.or, [r, r]⟩) x w := by
  have hAS := set_ao gs hA h r hr
  have hAD := del_ao n h r gs hA hr
  have hlenD := del_len n h r gs hh
  have gate_case : ∀ k j, k ≠ h → k < gs.length → (if j < h then j else j + 1) = k →
      (∀ i, i < n + k → wv (del n h r gs) x (sg n h r i) = wv (gs.set h ⟨GateOp.or, [r, r]⟩) x i) →
      wv (del n h r gs) x (n + j) = wv (gs.set h ⟨GateOp.or, [r, r]⟩) x (n + k) := by
    intro k j hkh hk hjk ih
    have hgS : (gs.set h ⟨GateOp.or, [r, r]⟩)[k]? = some gs[k] := by
      rw [List.getElem?_set_ne (Ne.symm hkh)]; exact List.getElem?_eq_getElem hk
    have hgD : (del n h r gs)[j]? = some (ren (sg n h r) gs[k]) := by
      rw [del_get, hjk, List.getElem?_eq_getElem hk]; rfl
    rw [wv_gate _ x j _ hgD (ao_rb _ hAD j _ hgD), wv_gate _ x k _ hgS (ao_rb _ hAS k _ hgS)]
    show (gs[k]).op.eval (((gs[k]).inputs.map (sg n h r)).map _) = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact ih i (ao_rb _ hAS k _ hgS i hi)
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · have hs : sg n h r w = w := by unfold sg; rw [if_pos (by omega)]
      rw [hs, wv_in _ x w hw, wv_in _ x w hw]
    · by_cases hw2 : w < n + gs.length
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < gs.length := by omega
        rcases lt_trichotomy k h with hlt | heq | hgt
        · have hs : sg n h r (n + k) = n + k := by unfold sg; rw [if_pos (by omega)]
          rw [hs]
          exact gate_case k k (by omega) hk (by rw [if_pos hlt]) (fun i hi => ih i hi)
        · subst heq
          have hs : sg n k r (n + k) = r := by
            unfold sg; rw [if_neg (by omega), if_pos rfl]
          have hs2 : sg n k r r = r := by unfold sg; rw [if_pos hr]
          rw [hs, set_copy gs k r x hh hr, ← ih r hr, hs2]
        · have hs : sg n h r (n + k) = n + (k - 1) := by
            unfold sg; rw [if_neg (by omega), if_neg (by omega)]; omega
          rw [hs]
          exact gate_case k (k - 1) (by omega) hk (by rw [if_neg (by omega)]; omega)
            (fun i hi => ih i hi)
      · have hs : sg n h r w = w - 1 := by
          unfold sg; rw [if_neg (by omega), if_neg (by omega)]
        rw [hs, wv_out _ x _ (by omega), wv_out _ x _ (by rw [List.length_set]; omega)]

-- The OR gates not below f.
def bad (n : ℕ) (f : (Fin n → Bool) → Bool) (gs : List Gate) : Set ℕ :=
  {j | ∃ g, gs[j]? = some g ∧ g.op = GateOp.or ∧
    ¬ ∀ z : Fin n → Bool, wv gs z (n + j) = true → f z = true}

lemma bad_finite (n : ℕ) (f : (Fin n → Bool) → Bool) (gs : List Gate) : (bad n f gs).Finite := by
  apply (Set.finite_lt_nat gs.length).subset
  rintro j ⟨g, hg, _⟩
  exact (List.getElem?_eq_some_iff.1 hg).1

lemma set_differs (gs : List Gate) (h : ℕ) (g : Gate) :
    ∀ k, k ≠ h → gs[k]? = (gs.set h g)[k]? := by
  intro k hk
  rw [List.getElem?_set_ne (Ne.symm hk)]

def run {α : Type} (st : List α → Gate → α) (init : List α) (gs : List Gate) : List α :=
  gs.foldl (fun w g => w ++ [st w g]) init

lemma run_length {α : Type} (st : List α → Gate → α) (gs : List Gate) (init : List α) :
    (run st init gs).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp [run]
  | cons g gs ih =>
    have h := ih (init ++ [st init g])
    simp only [run, List.foldl_cons] at h ⊢
    rw [h]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma run_snoc {α : Type} (st : List α → Gate → α) (gs : List Gate) (g : Gate) (init : List α) :
    run st init (gs ++ [g]) = run st init gs ++ [st (run st init gs) g] := by
  simp [run, List.foldl_append]

lemma run_getD_snoc {α : Type} (d : α) (st : List α → Gate → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    (run st init (gs ++ [g])).getD i d =
      if i = init.length + gs.length then st (run st init gs) g
      else (run st init gs).getD i d := by
  rw [run_snoc]
  have hl := run_length st gs init
  rcases lt_trichotomy i (init.length + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- the value of wire `i` in a generic run -/
def rv {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) (i : ℕ) : α :=
  (run (fun w g => G g (g.inputs.map fun i => w.getD i d)) init gs).getD i d

lemma rv_snoc {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (g : Gate) (i : ℕ) :
    rv d G init (gs ++ [g]) i =
      if i = init.length + gs.length then G g (g.inputs.map fun j => rv d G init gs j)
      else rv d G init gs i := by
  unfold rv
  rw [run_getD_snoc]

lemma rv_ge {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : init.length + gs.length ≤ i) : rv d G init gs i = d := by
  unfold rv
  generalize (fun (w : List α) (g : Gate) => G g (g.inputs.map fun i => w.getD i d)) = st
  have hl := run_length st gs init
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

lemma rv_lt {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate)
    (i : ℕ) (hi : i < init.length) : rv d G init gs i = init.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => simp [rv, run]
  | append_singleton gs g ih =>
    rw [rv_snoc, if_neg (by omega)]
    exact ih

lemma rv_gate {α : Type} (d : α) (G : Gate → List α → α) (init : List α) (gs : List Gate) :
    ∀ (k : ℕ) (hk : k < gs.length), (∀ j ∈ gs[k].inputs, j < init.length + k) →
      rv d G init gs (init.length + k) =
        G gs[k] (gs[k].inputs.map fun j => rv d G init gs j) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro k hk
    simp at hk
  | append_singleton gs g ih =>
    intro k hk hrb
    by_cases hkl : k = gs.length
    · subst hkl
      have hgl : (gs ++ [g])[gs.length]'hk = g := by simp
      rw [hgl] at hrb ⊢
      rw [rv_snoc, if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]
    · have hk' : k < gs.length + 1 := by simpa using hk
      have hk2 : k < gs.length := by omega
      have hget : (gs ++ [g])[k]'hk = gs[k] := List.getElem_append_left hk2
      rw [hget] at hrb ⊢
      rw [rv_snoc, if_neg (by omega), ih k hk2 hrb]
      congr 1
      apply List.map_congr_left
      intro j hj
      rw [rv_snoc, if_neg (by have := hrb j hj; omega)]


def Gp (g : Gate) (ins : List (Bool × Bool)) : Bool × Bool :=
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
      (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

def pinit (isLine : ℕ → Bool) (zl : List Bool) : List (Bool × Bool) :=
  (zl.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)


lemma pinit_length (isLine : ℕ → Bool) (zl : List Bool) : (pinit isLine zl).length = zl.length := by
  simp [pinit]

lemma pinit_getD (isLine : ℕ → Bool) (zl : List Bool) (w : ℕ) (hw : w < zl.length) :
    (pinit isLine zl).getD w (false, false) =
      if isLine w then (false, zl.getD w false) else (zl.getD w false, false) := by
  simp [pinit, List.getD_eq_getElem?_getD, hw]

def zin (n p l : ℕ) : List Bool := (List.range n).map fun i => i == p || i == l

lemma zin_length (n p l : ℕ) : (zin n p l).length = n := by simp [zin]

lemma zin_getD (n p l w : ℕ) (hw : w < n) : (zin n p l).getD w false = (w == p || w == l) := by
  simp [zin, List.getD_eq_getElem?_getD, hw]

/-! read vectors -/

abbrev Bits := Bool × Bool
abbrev zeroBits : Bits := (false,false)
abbrev pv (init : List Bits) (gs : List Gate) (w : ℕ) := rv zeroBits Gp init gs w

def proj {n : ℕ} (init : List Bits) (i : Fin n) := (init.getD i.val zeroBits).1

lemma pv_gate {n : ℕ} (init : List Bits) (hn : init.length = n) (gs : List Gate)
    (ao : AO n gs) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) :
    pv init gs (n+k) = Gp g (g.inputs.map (pv init gs)) := by
  obtain ⟨hk,rfl⟩ := List.getElem?_eq_some_iff.1 hg
  have rb := ao_rb gs ao k _ (List.getElem?_eq_getElem hk)
  have h := rv_gate zeroBits Gp init gs k hk (by rw [hn]; exact rb)
  simpa only [hn] using h

lemma first_part {n : ℕ} (init : List Bits) (hn : init.length = n) (gs : List Gate)
    (ao : AO n gs) (w : ℕ) : (pv init gs w).1 = wv gs (proj init : Fin n → Bool) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases lt : w < n
    · rw [wv_in gs _ w lt]
      exact congrArg Prod.fst (rv_lt zeroBits Gp init gs w (by omega))
    by_cases out : n+gs.length ≤ w
    · rw [wv_out gs _ w out]
      exact congrArg Prod.fst (rv_ge zeroBits Gp init gs w (by omega))
    obtain ⟨k,rfl⟩ : ∃k,w=n+k := ⟨w-n,by omega⟩
    have hk : k < gs.length := by omega
    have hg := List.getElem?_eq_getElem (l:=gs) hk
    obtain ⟨hop,a,b,hab,ha,hb⟩ := ao k _ hg
    rw [pv_gate init hn gs ao k _ hg, wv_gate gs _ k _ hg (ao_rb gs ao k _ hg),hab]
    rcases hop with hand|hor
    · simp [Gp,hand,GateOp.eval,ih a ha,ih b hb]
    · simp [Gp,hor,GateOp.eval,ih a ha,ih b hb]

lemma transport {n : ℕ} (init : List Bits) (hn : init.length = n) (gs : List Gate)
    (ao : AO n gs) (h v : ℕ) (hh : h < gs.length) (hv : v < n+h) (limit : ℕ)
    (same : n+h < limit → pv init gs (n+h) = pv init gs v) :
    ∀ i, i < limit → pv init (del n h v gs) (sg n h v i) = pv init gs i := by
  have hd := del_ao n h v gs ao hv
  have hl := del_len n h v gs hh
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro lim
    by_cases lo : i<n
    · have s : sg n h v i=i := by unfold sg; rw [if_pos (by omega)]
      rw [s]
      exact (rv_lt zeroBits Gp init (del n h v gs) i (by omega)).trans
        (rv_lt zeroBits Gp init gs i (by omega)).symm
    by_cases out : n+gs.length ≤ i
    · have s : sg n h v i=i-1 := by unfold sg; rw [if_neg (by omega),if_neg (by omega)]
      rw [s]
      exact (rv_ge zeroBits Gp init (del n h v gs) (i-1) (by omega)).trans
        (rv_ge zeroBits Gp init gs i (by omega)).symm
    obtain ⟨k,rfl⟩ : ∃k,i=n+k := ⟨i-n,by omega⟩
    have hk : k<gs.length := by omega
    by_cases eq : k=h
    · subst k
      have s : sg n h v (n+h)=v := by simp [sg]
      have t : sg n h v v=v := by simp [sg,hv]
      rw [s,same lim]
      simpa only [t] using ih v hv (by omega)
    let j := if k<h then k else k-1
    have hj : (if j<h then j else j+1)=k := by dsimp [j]; split_ifs <;> omega
    have s : sg n h v (n+k)=n+j := by dsimp [sg,j]; split_ifs <;> omega
    have hg := List.getElem?_eq_getElem (l:=gs) hk
    have hg' : (del n h v gs)[j]? = some (ren (sg n h v) gs[k]) := by
      rw [del_get,hj,hg]; rfl
    rw [s,pv_gate init hn _ hd j _ hg',pv_gate init hn _ ao k _ hg]
    have hargs : ((gs[k].inputs.map (sg n h v)).map (pv init (del n h v gs))) = gs[k].inputs.map (pv init gs) := by
      rw [List.map_map]; apply List.map_congr_left
      intro z hz
      have small := ao_rb gs ao k _ hg z hz
      exact ih z small (by omega)
    change Gp (ren (sg n h v) gs[k]) ((gs[k].inputs.map (sg n h v)).map _) = _
    rw [hargs]
    rfl

/-- Every true retained linear coefficient whose degree-zero input is rejected by f. -/
def Retains {n : ℕ} (f : (Fin n → Bool) → Bool) (base : Circuit) (gs : List Gate) (o : ℕ) :=
  ∀ init : List Bits, init.length=n → f (proj init)=false → (pv init base.gates base.output).2=true →
    (pv init gs o).2=true

lemma lift_parts {n : ℕ} (f : (Fin n → Bool) → Bool) (base : Circuit) (gs : List Gate)
    (o h w v : ℕ) (ao : AO n gs) (old : Retains f base gs o)
    (hg : gs[h]? = some ⟨GateOp.or,[w,v]⟩ ∨ gs[h]? = some ⟨GateOp.or,[v,w]⟩)
    (below : ∀ z, wv gs z w = true → f z = true) :
    Retains f base ((del n h v gs) ++ [⟨GateOp.or,[sg n h v o,w]⟩]) (n+(del n h v gs).length) := by
  have hh : h<gs.length := by rcases hg with e|e <;> exact (List.getElem?_eq_some_iff.1 e).1
  have hwv : w<n+h ∧ v<n+h := by
    rcases hg with e|e <;> exact ⟨ao_rb gs ao h _ e w (by simp),ao_rb gs ao h _ e v (by simp)⟩
  obtain ⟨hw,hv⟩ := hwv
  intro init hn cold root
  have oldRoot := old init hn cold root
  have pre := transport init hn gs ao h v hh hv (n+h) (fun e => (Nat.lt_irrefl _ e).elim) w hw
  have s : sg n h v w=w := by simp [sg,hw]
  rw [s] at pre
  have z : (pv init gs w).1=false := by
    rw [first_part init hn gs ao w]
    cases e : wv gs (proj init : Fin n → Bool) w with
    | false => rfl
    | true => have bad := below _ e; rw [cold] at bad; contradiction
  have last := rv_snoc zeroBits Gp init (del n h v gs) (⟨GateOp.or,[sg n h v o,w]⟩ : Gate)
    (n+(del n h v gs).length)
  have lastValue : pv init ((del n h v gs) ++ [⟨GateOp.or,[sg n h v o,w]⟩])
      (n+(del n h v gs).length) =
      ((pv init (del n h v gs) (sg n h v o)).1 || (pv init (del n h v gs) w).1,
       (pv init (del n h v gs) (sg n h v o)).2 || (pv init (del n h v gs) w).2) := by
    simpa [hn,Gp] using last
  rw [lastValue]
  change ((pv init (del n h v gs) (sg n h v o)).2 || (pv init (del n h v gs) w).2)=true
  rw [pre]
  cases bit : (pv init gs w).2 with
  | true => simp
  | false =>
    have nul : pv init gs w = (false,false) := Prod.ext z bit
    have same : pv init gs (n+h)=pv init gs v := by
      rcases hg with e|e
      · rw [pv_gate init hn gs ao h _ e]; simp [Gp,nul]
      · rw [pv_gate init hn gs ao h _ e]; simp [Gp,nul]
    have output := transport init hn gs ao h v hh hv (o+1) (fun _=>same) o (by omega)
    rw [output,oldRoot]; rfl

-- The lift: an OR gate not below f that reads a wire w below f drops w, and w is joined
-- to the output. Same size, one OR gate not below f fewer.
lemma lift {n : ℕ} (f : (Fin n → Bool) → Bool) (gs : List Gate) (o h w v : ℕ) (base : Circuit) (old : Retains f base gs o)
    (hA : AO n gs) (hf : ∀ x, wv gs x o = f x) (ho : o < n + gs.length)
    (hg : gs[h]? = some ⟨GateOp.or, [w, v]⟩ ∨ gs[h]? = some ⟨GateOp.or, [v, w]⟩)
    (hnb : ¬ ∀ z : Fin n → Bool, wv gs z (n + h) = true → f z = true)
    (hw : ∀ z : Fin n → Bool, wv gs z w = true → f z = true) :
    ∃ gs' o', AO n gs' ∧ (∀ x, wv gs' x o' = f x) ∧ gs'.length = gs.length ∧
      (bad n f gs').ncard < (bad n f gs).ncard ∧ Retains f base gs' o' := by
  have hh : h < gs.length := by
    rcases hg with hg | hg <;> exact (List.getElem?_eq_some_iff.1 hg).1
  have hwv : w < n + h ∧ v < n + h := by
    rcases hg with hg | hg
    · exact ⟨ao_rb gs hA h _ hg w (by simp), ao_rb gs hA h _ hg v (by simp)⟩
    · exact ⟨ao_rb gs hA h _ hg w (by simp), ao_rb gs hA h _ hg v (by simp)⟩
  obtain ⟨hwlt, hvlt⟩ := hwv
  have hval : ∀ x : Fin n → Bool, wv gs x (n + h) = (wv gs x w || wv gs x v) := by
    intro x
    rcases hg with hg | hg
    · exact wv_or gs x h w v hg hwlt hvlt
    · rw [wv_or gs x h v w hg hvlt hwlt, Bool.or_comm]
  have hAS := set_ao gs hA h v hvlt
  have hAD := del_ao n h v gs hA hvlt
  have hlenD := del_len n h v gs hh
  have hlenS : (gs.set h ⟨GateOp.or, [v, v]⟩).length = gs.length := List.length_set
  have hdiff := set_differs gs h ⟨GateOp.or, [v, v]⟩
  -- wires below h agree
  have hpre : ∀ (x : Fin n → Bool) (i : ℕ), i < n + h →
      wv gs x i = wv (gs.set h ⟨GateOp.or, [v, v]⟩) x i :=
    fun x i hi => same_off gs _ h x hA hlenS.symm hdiff i (by omega) (Or.inl hi)
  have hSh : ∀ x : Fin n → Bool, wv (gs.set h ⟨GateOp.or, [v, v]⟩) x (n + h) = wv gs x v := by
    intro x; rw [set_copy gs h v x hh hvlt, hpre x v hvlt]
  have hmono : ∀ (x : Fin n → Bool) (i : ℕ),
      wv (gs.set h ⟨GateOp.or, [v, v]⟩) x i = true → wv gs x i = true := by
    intro x
    apply mono_off _ gs h x hAS hlenS (fun k hk => (hdiff k hk).symm)
    rw [hSh x, hval x]
    intro hv; rw [hv]; simp
  have hsgo : sg n h v o < n + (del n h v gs).length := by
    unfold sg; split_ifs <;> omega
  have hgN : ((del n h v gs) ++ [(⟨GateOp.or, [sg n h v o, w]⟩ : Gate)])[(del n h v gs).length]? =
      some ⟨GateOp.or, [sg n h v o, w]⟩ := by
    simp
  have hAN : AO n ((del n h v gs) ++ [(⟨GateOp.or, [sg n h v o, w]⟩ : Gate)]) := by
    intro k g hk
    by_cases hlt : k < (del n h v gs).length
    · rw [List.getElem?_append_left hlt] at hk
      exact hAD k g hk
    · have hk' : k < ((del n h v gs) ++ [(⟨GateOp.or, [sg n h v o, w]⟩ : Gate)]).length :=
        (List.getElem?_eq_some_iff.1 hk).1
      have hke : k = (del n h v gs).length := by
        rw [List.length_append] at hk'; simp at hk'; omega
      subst hke
      rw [hgN] at hk
      cases hk
      exact ⟨Or.inr rfl, _, _, rfl, hsgo, by omega⟩
  have hsw : sg n h v w = w := by unfold sg; rw [if_pos hwlt]
  have hout : ∀ x : Fin n → Bool,
      wv ((del n h v gs) ++ [(⟨GateOp.or, [sg n h v o, w]⟩ : Gate)]) x (n + (del n h v gs).length)
        = f x := by
    intro x
    rw [wv_or _ x _ _ _ hgN hsgo (by omega), wv_append _ _ x _ hsgo, wv_append _ _ x _ (by omega),
      del_val gs h v x hA hh hvlt o]
    have h2 : wv (del n h v gs) x w = wv gs x w := by
      conv_lhs => rw [← hsw]
      rw [del_val gs h v x hA hh hvlt w, ← hpre x w hwlt]
    rw [h2]
    cases hww : wv gs x w with
    | true => rw [hw x hww]; simp
    | false =>
      have heq : wv gs x (n + h) = wv (gs.set h ⟨GateOp.or, [v, v]⟩) x (n + h) := by
        rw [hSh x, hval x, hww]; simp
      have ho2 : wv gs x o = wv (gs.set h ⟨GateOp.or, [v, v]⟩) x o := by
        by_cases hoh : o = n + h
        · rw [hoh]; exact heq
        · exact same_off gs _ h x hA hlenS.symm hdiff o hoh (Or.inr (fun _ _ _ _ => heq))
      rw [← ho2, hf x]; simp
  refine ⟨_, n + (del n h v gs).length, hAN, hout, by rw [List.length_append]; simp; omega, ?_, lift_parts f base gs o h w v hA old hg hw⟩
  have hhbad : h ∈ bad n f gs := by
    rcases hg with hg | hg
    · exact ⟨_, hg, rfl, hnb⟩
    · exact ⟨_, hg, rfl, hnb⟩
  refine lt_of_le_of_lt ?_ (Set.ncard_sdiff_singleton_lt_of_mem hhbad (bad_finite n f gs))
  apply Set.ncard_le_ncard_of_injOn (fun j => if j < h then j else j + 1) ?_ ?_
    ((bad_finite n f gs).subset Set.sdiff_subset)
  · rintro j ⟨g, hgj, hop, hnbj⟩
    have hjlt : j < ((del n h v gs) ++ [(⟨GateOp.or, [sg n h v o, w]⟩ : Gate)]).length :=
      (List.getElem?_eq_some_iff.1 hgj).1
    rw [List.length_append] at hjlt
    simp at hjlt
    by_cases hjl : j < (del n h v gs).length
    · rw [List.getElem?_append_left hjl, del_get] at hgj
      obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hgj
      refine ⟨⟨g0, hg0, hop, ?_⟩, ?_⟩
      · intro hbelow
        apply hnbj
        intro z hz
        apply hbelow z
        apply hmono z
        rw [wv_append _ _ z _ (by omega)] at hz
        have hs : sg n h v (n + (if j < h then j else j + 1)) = n + j := by
          unfold sg; split_ifs <;> omega
        rw [← del_val gs h v z hA hh hvlt, hs]
        exact hz
      · simp only [Set.mem_singleton_iff]; split_ifs <;> omega
    · exfalso
      have hje : j = (del n h v gs).length := by omega
      apply hnbj
      intro z _
      rw [hje] at *
      exact (hout z).symm ▸ (by assumption)
  · intro a _ b _ hab
    simp only at hab
    split_ifs at hab <;> omega

-- An AND gate reading a wire below f can be turned into a copy of that wire, and deleted.
lemma shrink_and {n : ℕ} (f : (Fin n → Bool) → Bool) (gs : List Gate) (o k a b t : ℕ)
    (hA : AO n gs) (hf : ∀ x, wv gs x o = f x)
    (hg : gs[k]? = some ⟨GateOp.and, [a, b]⟩) (ht : t = a ∨ t = b)
    (hb : ∀ z : Fin n → Bool, wv gs z t = true → f z = true) :
    ∃ gs' o', AO n gs' ∧ (∀ x, wv gs' x o' = f x) ∧ gs'.length + 1 = gs.length := by
  have hk : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have halt := ao_rb gs hA k _ hg a (by simp)
  have hblt := ao_rb gs hA k _ hg b (by simp)
  have htlt : t < n + k := by rcases ht with rfl | rfl <;> assumption
  have hlenS : (gs.set k ⟨GateOp.or, [t, t]⟩).length = gs.length := List.length_set
  have hdiff := set_differs gs k ⟨GateOp.or, [t, t]⟩
  refine ⟨del n k t gs, sg n k t o, del_ao n k t gs hA htlt, ?_, del_len n k t gs hk⟩
  intro x
  rw [del_val gs k t x hA hk htlt o, ← hf x]
  have hSk : wv (gs.set k ⟨GateOp.or, [t, t]⟩) x (n + k) = wv gs x t := by
    rw [set_copy gs k t x hk htlt]
    exact (same_off gs _ k x hA hlenS.symm hdiff t (by omega) (Or.inl htlt)).symm
  have hgk : wv gs x (n + k) = (wv gs x a && wv gs x b) := wv_and gs x k a b hg halt hblt
  by_cases heq : wv gs x (n + k) = wv (gs.set k ⟨GateOp.or, [t, t]⟩) x (n + k)
  · by_cases hok : o = n + k
    · rw [hok]; exact heq.symm
    · exact (same_off gs _ k x hA hlenS.symm hdiff o hok (Or.inr (fun _ _ _ _ => heq))).symm
  · have htt : wv gs x t = true := by
      by_contra hne
      apply heq
      rw [hSk, hgk]
      have hft : wv gs x t = false := by simpa using hne
      rcases ht with rfl | rfl <;> simp [hft]
    have hfx : wv gs x o = true := by rw [hf x]; exact hb x htt
    rw [hfx]
    exact mono_off gs _ k x hA hlenS.symm hdiff (fun _ => by rw [hSk]; exact htt) o hfx

-- A gate that nobody reads and that is not the output can be deleted.
lemma shrink_dead {n : ℕ} (f : (Fin n → Bool) → Bool) (gs : List Gate) (o j : ℕ)
    (hA : AO n gs) (hf : ∀ x, wv gs x o = f x) (hj : j < gs.length)
    (hun : ∀ (k : ℕ) (g : Gate), gs[k]? = some g → n + j ∉ g.inputs) (ho : o ≠ n + j) :
    ∃ gs' o', AO n gs' ∧ (∀ x, wv gs' x o' = f x) ∧ gs'.length + 1 = gs.length := by
  have h0 : 0 < n + j := by
    obtain ⟨_, a, b, _, ha, _⟩ := hA j _ (List.getElem?_eq_getElem hj)
    omega
  have hlenS : (gs.set j ⟨GateOp.or, [0, 0]⟩).length = gs.length := List.length_set
  refine ⟨del n j 0 gs, sg n j 0 o, del_ao n j 0 gs hA h0, ?_, del_len n j 0 gs hj⟩
  intro x
  rw [del_val gs j 0 x hA hj h0 o, ← hf x]
  exact (same_off gs _ j x hA hlenS.symm (set_differs gs j _) o ho
    (Or.inr (fun k g hg hmem => absurd hmem (hun k g hg)))).symm

lemma inCone_lt (n : ℕ) (C : Circuit) (i m : ℕ) (h : InCone n C i m) : m < C.gates.length := by
  by_contra hm
  unfold InCone cones at h
  rw [List.getD_eq_default _ _ (by rw [coneFold_length]; simp; omega)] at h
  simp at h

lemma inCone_trans (n : ℕ) (C : Circuit) (i j : ℕ) (hij : InCone n C i j) :
    ∀ m, InCone n C j m → InCone n C i m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hjm
    have hm := inCone_lt n C j m hjm
    obtain ⟨w, hw, h1, h2, h3⟩ := (inCone_iff n C j m hm).1 hjm
    refine (inCone_iff n C i m hm).2 ⟨w, hw, h1, h2, Or.inr ?_⟩
    rcases h3 with h3 | h3
    · rw [← h3]; exact hij
    · exact ih (w - n) (by omega) h3

-- In a least circuit every gate is the output gate or lies in its cone.
lemma live_all {n : ℕ} (f : (Fin n → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hA : AO n gs) (hf : ∀ x, wv gs x o = f x)
    (hleast : ∀ gs' o', AO n gs' → (∀ x, wv gs' x o' = f x) → gs.length ≤ gs'.length) :
    PEqualNP.FactorSubst.liveSize n ⟨gs, o⟩ = gs.length := by
  classical
  have key : ∀ j, j < gs.length →
      n ≤ o ∧ (j = o - n ∨ InCone n ⟨gs, o⟩ j (o - n)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j1, hj1, hd1⟩ := hcon
    let P : ℕ → Prop := fun j => j < gs.length ∧ ¬ (n ≤ o ∧ (j = o - n ∨ InCone n ⟨gs, o⟩ j (o - n)))
    have hP1 : P j1 := by
      refine ⟨hj1, fun hc => ?_⟩
      have hd := hd1 hc.1
      rcases hc.2 with h | h
      · exact hd.1 h
      · exact hd.2 h
    have hspec := Nat.findGreatest_spec (P := P) (le_of_lt hj1) hP1
    have hgr := fun k (hk : Nat.findGreatest P gs.length < k) (hkb : k ≤ gs.length) =>
      Nat.findGreatest_is_greatest (P := P) hk hkb
    obtain ⟨hj0, hdead⟩ := hspec
    have hun : ∀ (k : ℕ) (g : Gate), gs[k]? = some g →
        n + Nat.findGreatest P gs.length ∉ g.inputs := by
      intro k g hg hmem
      have hk : k < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      have hlt := ao_rb gs hA k g hg _ hmem
      have hlive : n ≤ o ∧ (k = o - n ∨ InCone n ⟨gs, o⟩ k (o - n)) := by
        by_contra hnl
        exact hgr k (by omega) (le_of_lt hk) ⟨hk, hnl⟩
      have hga : gateAt ⟨gs, o⟩ k = g := by
        rw [gateAt_eq ⟨gs, o⟩ k hk]
        exact Option.some.inj ((List.getElem?_eq_getElem hk).symm.trans hg)
      have hcone : InCone n ⟨gs, o⟩ (Nat.findGreatest P gs.length) k :=
        (inCone_iff n ⟨gs, o⟩ _ k hk).2
          ⟨n + Nat.findGreatest P gs.length, by rw [hga]; exact hmem, by omega, hlt,
            Or.inl (by omega)⟩
      apply hdead
      refine ⟨hlive.1, Or.inr ?_⟩
      rcases hlive.2 with he | hc
      · have hc2 := hcone
        rw [he] at hc2
        exact hc2
      · exact inCone_trans n ⟨gs, o⟩ _ k hcone _ hc
    have ho : o ≠ n + Nat.findGreatest P gs.length := by
      intro he
      exact hdead ⟨by omega, Or.inl (by omega)⟩
    obtain ⟨gs', o', h1, h2, h3⟩ := shrink_dead f gs o _ hA hf hj0 hun ho
    have := hleast gs' o' h1 h2
    omega
  unfold PEqualNP.FactorSubst.liveSize PEqualNP.FactorSubst.liveGates
  rw [Finset.filter_true_of_mem (fun j hj => by
    have hj' : j < gs.length := Finset.mem_range.1 hj
    have hk := key j hj'
    exact ⟨hk.1, hk.2⟩)]
  simp

theorem preserve (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (hC : IsAO2 n C)
    (hCf : circuitFun n C = f)
    (minimal : ∀D : Circuit, IsAO2 n D → circuitFun n D=f → C.size≤D.size) :
    ∃ D : Circuit, (IsAO2 n D ∧ circuitFun n D = f ∧
        ∀ C2 : Circuit, IsAO2 n C2 → circuitFun n C2 = f → D.size ≤ C2.size) ∧
      (¬ ∃ h < D.gates.length, ∃ b : Fin 2, PEqualNP.Core.InOutputCone n D h ∧
        (gateAt D h).op = GateOp.or ∧
        ¬ (∀ z1 : Fin n → Bool, gateVal n D h z1 = true → f z1 = true) ∧
        ((∀ x1 : Fin n → Bool, PEqualNP.ReadTwo.wval D x1 (opnd D h b) = true → f x1 = true) ∧
          ∃ y1 : Fin n → Bool, PEqualNP.ReadTwo.wval D y1 (opnd D h b) = true)) ∧
      (∀ k < D.gates.length, (gateAt D k).op = GateOp.and → ∀ t ∈ (gateAt D k).inputs,
        ¬ (∀ x : Fin n → Bool, Circuit.eval ⟨D.gates, t⟩ (List.ofFn x) = true → f x = true)) ∧
      PEqualNP.FactorSubst.liveSize n D = D.size ∧ Retains f C D.gates D.output := by
  classical
  have hex : ∃ b, ∃ gs o, AO n gs ∧ (∀ x, wv gs x o = f x) ∧ gs.length = C.size ∧
      Retains f C gs o ∧ (bad n f gs).ncard = b :=
    ⟨_, C.gates, C.output, ao_of n C hC, fun x => by rw [←hCf]; rfl,
      rfl, fun _ _ _ hit => hit, rfl⟩
  obtain ⟨gs,o,hA,hf,hlen,ret,hpot⟩ := Nat.find_spec hex
  have hleast : ∀ gs' o', AO n gs' → (∀ x, wv gs' x o' = f x) → gs.length ≤ gs'.length := by
    intro gs' o' ao' fun'
    rw [hlen]
    exact minimal ⟨gs',o'⟩ (ao_to n gs' o' ao') (funext fun')
  have hpmin : ∀ gs' o', AO n gs' → (∀ x, wv gs' x o' = f x) → gs'.length = gs.length →
      Retains f C gs' o' → (bad n f gs).ncard ≤ (bad n f gs').ncard := by
    intro gs' o' a b c d
    rw [hpot]
    exact Nat.find_min' hex ⟨gs',o',a,b,c.trans hlen,d,rfl⟩
  have gate_shape : ∀ k (hk : k < gs.length), ∃ a c, a < n + k ∧ c < n + k ∧
      (gs[k]).inputs = [a, c] ∧ gs[k]? = some ⟨(gs[k]).op, [a, c]⟩ := by
    intro k hk
    obtain ⟨_, a, c, hac, ha, hc⟩ := hA k _ (List.getElem?_eq_getElem hk)
    refine ⟨a, c, ha, hc, hac, ?_⟩
    rw [List.getElem?_eq_getElem hk, ← hac]
  refine ⟨⟨gs, o⟩, ⟨ao_to n gs o hA, funext (fun x => hf x), ?_⟩, ?_, ?_, live_all f gs o hA hf hleast, ret⟩
  · intro C2 h2 hf2
    exact hleast C2.gates C2.output (ao_of n C2 h2) (fun x => by rw [← hf2]; rfl)
  · rintro ⟨h, hh, b, _, hor, hnb, hbel, y, hy⟩
    have hh' : h < gs.length := hh
    obtain ⟨a, c, ha, hc, hac, hgate⟩ := gate_shape h hh'
    have hgat : gateAt ⟨gs, o⟩ h = gs[h] := gateAt_eq ⟨gs, o⟩ h hh
    rw [hgat] at hor
    rw [hor] at hgate
    have hopnd : opnd ⟨gs, o⟩ h b = a ∨ opnd ⟨gs, o⟩ h b = c := by
      unfold opnd
      rw [hgat, hac]
      fin_cases b <;> simp
    have ho : o < n + gs.length := by
      by_contra hno
      have hfy : f y = true := hbel y hy
      rw [← hf y, wv_out gs y o (by omega)] at hfy
      cases hfy
    have hnb' : ¬ ∀ z : Fin n → Bool, wv gs z (n + h) = true → f z = true := hnb
    have hbel' : ∀ z : Fin n → Bool, wv gs z (opnd ⟨gs, o⟩ h b) = true → f z = true := hbel
    rcases hopnd with e | e
    · rw [e] at hbel'
      obtain ⟨gs', o', h1, h2, h3, h4, keep⟩ := lift f gs o h a c C ret hA hf ho (Or.inl hgate) hnb' hbel'
      have := hpmin gs' o' h1 h2 h3 keep
      omega
    · rw [e] at hbel'
      obtain ⟨gs', o', h1, h2, h3, h4, keep⟩ := lift f gs o h c a C ret hA hf ho (Or.inr hgate) hnb' hbel'
      have := hpmin gs' o' h1 h2 h3 keep
      omega
  · intro k hk hand t ht hbelow
    have hk' : k < gs.length := hk
    obtain ⟨a, c, ha, hc, hac, hgate⟩ := gate_shape k hk'
    have hgat : gateAt ⟨gs, o⟩ k = gs[k] := gateAt_eq ⟨gs, o⟩ k hk
    rw [hgat] at hand ht
    rw [hand] at hgate
    rw [hac] at ht
    have ht' : t = a ∨ t = c := by simpa using ht
    have hbelow' : ∀ z : Fin n → Bool, wv gs z t = true → f z = true := hbelow
    obtain ⟨gs', o', h1, h2, h3⟩ := shrink_and f gs o k a c t hA hf hgate ht' hbelow'
    have := hleast gs' o' h1 h2
    omega

open PEqualNP.ReadK PEqualNP.Core

lemma pair_cold {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (side : ℕ → Bool) (p l : ℕ) (opp : side p ≠ side l) :
    graphFun G ∅ (proj (pinit side (zin n p l))) = false := by
  let init := pinit side (zin n p l)
  have hw (i : Fin n) (hi : proj init i=true) : side i.val=false ∧ (i.val=p ∨ i.val=l) := by
    change ((pinit side (zin n p l)).getD i.val zeroBits).1=true at hi
    rw [pinit_getD _ _ _ (by rw [zin_length]; exact i.isLt),zin_getD _ _ _ _ i.isLt] at hi
    cases e : side i.val with
    | false => exact ⟨rfl,by simpa [e] using hi⟩
    | true => simp [e] at hi
  have independent : ¬ ∃ u v : Fin n, G.Adj u v ∧ proj init u=true ∧ proj init v=true := by
    rintro ⟨u,v,adj,hu,hv⟩
    obtain ⟨a,cu⟩ := hw u hu
    obtain ⟨b,cv⟩ := hw v hv
    have eq : u=v := by
      apply Fin.ext
      rcases cu with eu|eu <;> rcases cv with ev|ev
      · exact eu.trans ev.symm
      · rw [eu] at a; rw [ev] at b; exact (opp (a.trans b.symm)).elim
      · rw [eu] at a; rw [ev] at b; exact (opp (b.trans a.symm)).elim
      · exact eu.trans ev.symm
    subst v
    exact G.loopless.irrefl _ adj
  change graphFun G ∅ (proj init)=false
  simp [graphFun,independent]

lemma line_preserved {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (r : Retains (graphFun G ∅) C D.gates D.output)
    (side : ℕ→Bool) (p l : ℕ) (opp : side p ≠ side l) :
    lineSingle C n side p l=true → lineSingle D n side p l=true := by
  exact r (pinit side (zin n p l)) (by simp [pinit_length,zin_length]) (pair_cold G side p l opp)

/-- A single least circuit can be normalized without losing any previously single edge or orientation. -/
theorem normalizeLeast {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hc : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ IsLiftFixedPoint G D ∧
      (∀ k<D.gates.length,(gateAt D k).op=.and → ∀ t∈(gateAt D k).inputs,
          ¬(∀ x : Fin n→Bool,Circuit.eval ⟨D.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true)) ∧
      PEqualNP.FactorSubst.liveSize n D=D.size ∧
      (∀ (side : ℕ → Bool) (p l : ℕ), side p≠side l →
        lineSingle C n side p l=true → lineSingle D n side p l=true) := by
  obtain ⟨D,hD,fixed,clean,live,keep⟩ := preserve n (graphFun G ∅) C hc.1 hc.2.1 hc.2.2
  exact ⟨D,hD,fixed,clean,live,line_preserved keep⟩

/-- The other normal-form requirements add no obstruction once minimum size and single reading coincide. -/
theorem equivalence {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : ℕ→Bool) (E : List (ℕ×ℕ)) (sep : ∀ e∈E,s e.1≠s e.2) :
    (∃ D : Circuit, IsLeastAO G D ∧ IsLiftFixedPoint G D ∧
      (∀ k<D.gates.length,(gateAt D k).op=.and → ∀ t∈(gateAt D k).inputs,
          ¬(∀ x : Fin n→Bool,Circuit.eval ⟨D.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true)) ∧
      PEqualNP.FactorSubst.liveSize n D=D.size ∧ doubleReread D n s E=[]) ↔
    ∃ C : Circuit, IsLeastAO G C ∧ doubleReread C n s E=[] := by
  constructor
  · rintro ⟨D,h,_,_,_,one⟩; exact ⟨D,h,one⟩
  · rintro ⟨C,h,one⟩
    obtain ⟨D,hD,fixed,clean,live,keep⟩ := normalizeLeast G C h
    refine ⟨D,hD,fixed,clean,live,List.eq_nil_iff_forall_not_mem.mpr ?_⟩
    intro e he
    obtain ⟨em,ed⟩ := List.mem_filter.mp he
    have sd := sep e em
    have sn : (!s e.1) ≠ (!s e.2) := by cases a:s e.1 <;> cases b:s e.2 <;> simp_all
    have po := keep s e.1 e.2 sd
    have li := keep (fun i=> !s i) e.1 e.2 sn
    have old : e ∈ doubleReread C n s E := by
      apply List.mem_filter.mpr
      refine ⟨em,?_⟩
      change (!(lineSingle D n s e.1 e.2) && !(lineSingle D n (fun i=> !s i) e.1 e.2))=true at ed
      change (!(lineSingle C n s e.1 e.2) && !(lineSingle C n (fun i=> !s i) e.1 e.2))=true
      cases a:lineSingle C n s e.1 e.2 <;> cases b:lineSingle C n (fun i=> !s i) e.1 e.2 <;> simp_all
    rw [one] at old
    exact List.not_mem_nil old

end Normal3722

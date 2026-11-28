import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (C : Circuit) (z : List Bool) (w : ℕ) : Bool :=
  (C.wires z).getD w false

lemma wires_eq_foldl (C : Circuit) (z : List Bool) :
    C.wires z = C.gates.foldl step z := rfl

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by simp only [step, List.length_append]; omega
    rw [ih (step w g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [step, List.getElem_append_left hi]

lemma wv_input (C : Circuit) (z : List Bool) (i : ℕ) (hi : i < z.length) :
    wv C z i = z.getD i false := by
  unfold wv
  rw [wires_eq_foldl]
  exact foldl_step_getD_lt C.gates z i hi

lemma wv_ge (C : Circuit) (z : List Bool) (w : ℕ) (hw : z.length + C.gates.length ≤ w) :
    wv C z w = false := by
  unfold wv
  rw [wires_eq_foldl]
  have hlen : (C.gates.foldl step z).length ≤ w := by rw [foldl_step_length]; omega
  rw [List.getD_eq_default _ _ hlen]

lemma wv_gate (C : Circuit) (hRB : ReadsBack 26 C) (z : List Bool) (hz : z.length = 26)
    (j : ℕ) (hj : j < C.gates.length) :
    wv C z (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv C z i) := by
  unfold wv
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← hdrop, this]
  let pref := (C.gates.take j).foldl step z
  have hplen : pref.length = 26 + j := by
    simp only [pref, foldl_step_length, hz, List.length_take]
    omega
  have hpref_get : ∀ i < 26 + j, (C.gates.foldl step z).getD i false = pref.getD i false := by
    intro i hi
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    exact foldl_step_getD_lt _ pref i (by omega)
  have hgate_eq : gateAt C j = C.gates[j] := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
  have hval : (C.gates.foldl step z).getD (26 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlt : 26 + j < (step pref C.gates[j]).length := by
      simp only [step, List.length_append, List.length_singleton, hplen]; omega
    rw [foldl_step_getD_lt _ (step pref C.gates[j]) (26 + j) hlt, List.getD_eq_getElem _ _ hlt]
    have hidx : 26 + j = pref.length := hplen.symm
    simp only [step, hidx, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
  rw [hval, hgate_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < 26 + j := hRB j hj i (hgate_eq ▸ hi)
  exact (hpref_get i hilt).symm

lemma gate_inputs_pair {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => simp [h] at hlen
  | [_] => simp [h] at hlen
  | _ :: _ :: _ :: _ => simp [h] at hlen

lemma gate_inputs_lt {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.getD 0 0 < 26 + j ∧ (gateAt C j).inputs.getD 1 0 < 26 + j := by
  have hpair := gate_inputs_pair hAO hj
  have h0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  have h1 : (gateAt C j).inputs.getD 1 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  exact ⟨hAO.2.1 j hj _ h0, hAO.2.1 j hj _ h1⟩

lemma wv_and_eq {C : Circuit} (hAO : IsAO2 26 C) {z : List Bool} (hz : z.length = 26)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wv C z (26 + j) = (wv C z ((gateAt C j).inputs.getD 0 0) && wv C z ((gateAt C j).inputs.getD 1 0)) := by
  rw [wv_gate C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_or_eq {C : Circuit} (hAO : IsAO2 26 C) {z : List Bool} (hz : z.length = 26)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wv C z (26 + j) = (wv C z ((gateAt C j).inputs.getD 0 0) || wv C z ((gateAt C j).inputs.getD 1 0)) := by
  rw [wv_gate C hAO.2.1 z hz j hj, hop, gate_inputs_pair hAO hj]
  simp [GateOp.eval]

lemma wv_mono {C : Circuit} (hAO : IsAO2 26 C) {x y : List Bool}
    (hx : x.length = 26) (hy : y.length = 26)
    (hle : ∀ i < 26, x.getD i false = true → y.getD i false = true) :
    ∀ w : ℕ, wv C x w = true → wv C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases h1 : w < 26
    · rw [wv_input C x w (by omega)] at htrue
      rw [wv_input C y w (by omega)]
      exact hle w h1 htrue
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at htrue ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [wv_and_eq hAO hx hjlt hand, Bool.and_eq_true] at htrue
          rw [wv_and_eq hAO hy hjlt hand, Bool.and_eq_true]
          exact ⟨ih _ (by omega) htrue.1, ih _ (by omega) htrue.2⟩
        · rw [wv_or_eq hAO hx hjlt hor, Bool.or_eq_true] at htrue
          rw [wv_or_eq hAO hy hjlt hor, Bool.or_eq_true]
          rcases htrue with h | h
          · exact Or.inl (ih _ (by omega) h)
          · exact Or.inr (ih _ (by omega) h)
      · rw [wv_ge C x w (by omega)] at htrue
        cases htrue

lemma list_filter_length_eq_card_range (l : List Gate) (p : Gate → Bool) (d : Gate) :
    (l.filter p).length = ((Finset.range l.length).filter (fun j => p (l.getD j d) = true)).card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hlast : (l ++ [g]).getD l.length d = g := by
      have hlt : l.length < (l ++ [g]).length := by simp
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    have hfilt_eq : (Finset.range l.length).filter (fun j => p ((l ++ [g]).getD j d) = true) =
        (Finset.range l.length).filter (fun j => p (l.getD j d) = true) := by
      apply Finset.filter_congr
      intro j hj
      have hjlt : j < l.length := Finset.mem_range.mp hj
      have hjlt2 : j < (l ++ [g]).length := by simp; omega
      rw [List.getD_eq_getElem _ _ hjlt2, List.getD_eq_getElem _ _ hjlt, List.getElem_append_left hjlt]
    rw [hlast, hfilt_eq]
    cases hpg : p g with
    | false =>
      simp [List.filter, hpg, ih]
    | true =>
      simp [List.filter, hpg, ih]

lemma nAnd_eq_card (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.and)] :
    nAnd C = ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)).card := by
  unfold nAnd
  rw [list_filter_length_eq_card_range C.gates _ ⟨GateOp.or, []⟩]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
  rfl

lemma nOr_eq_card (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.or)] :
    nOr C = ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.or)).card := by
  unfold nOr
  rw [list_filter_length_eq_card_range C.gates _ ⟨GateOp.or, []⟩]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
  rfl

def pairInput (p l : Fin 13) : List Bool :=
  (List.ofFn fun x : Fin 13 => decide (x = p)) ++
  (List.ofFn fun x : Fin 13 => decide (x = l))

def quadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
  (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))

lemma pairInput_length (p l : Fin 13) : (pairInput p l).length = 26 := by
  simp [pairInput]

lemma quadInput_length (Q : Finset (Fin 13)) : (quadInput Q).length = 26 := by
  simp [quadInput]

lemma pairInput_getD_true (p l : Fin 13) (i : ℕ) (hi : i < 26)
    (ht : (pairInput p l).getD i false = true) : i = p.val ∨ i = 13 + l.val := by
  have hlt : i < (pairInput p l).length := by rw [pairInput_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlt] at ht
  simp only [pairInput] at ht
  by_cases h1 : i < 13
  · have hlt1 : i < (List.ofFn fun x : Fin 13 => decide (x = p)).length := by simp; omega
    rw [List.getElem_append_left hlt1, List.getElem_ofFn] at ht
    simp only [decide_eq_true_iff] at ht
    left
    have := congrArg Fin.val ht
    simpa using this
  · have hge : (List.ofFn fun x : Fin 13 => decide (x = p)).length ≤ i := by simp; omega
    rw [List.getElem_append_right hge] at ht
    simp only [List.length_ofFn, List.getElem_ofFn, decide_eq_true_iff] at ht
    right
    have := congrArg Fin.val ht
    simp only at this
    omega

lemma quadInput_getD_pt (Q : Finset (Fin 13)) (p : Fin 13) :
    (quadInput Q).getD p.val false = decide (p ∈ Q) := by
  have hlt1 : p.val < (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length := by simp
  have hlt2 : p.val < (quadInput Q).length := by rw [quadInput_length]; exact Nat.lt_trans p.isLt (by omega)
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput, List.getElem_append_left hlt1, List.getElem_ofFn, Fin.eta]

lemma quadInput_getD_ln (Q : Finset (Fin 13)) (l : Fin 13) :
    (quadInput Q).getD (13 + l.val) false = decide (l ∈ missLines singerLines3 Q) := by
  have hlt2 : 13 + l.val < (quadInput Q).length := by rw [quadInput_length]; omega
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput]
  have hge : (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length ≤ 13 + l.val := by simp
  rw [List.getElem_append_right hge]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn, Fin.eta]


def zOr (z1 z2 : List Bool) : List Bool :=
  List.ofFn fun k : Fin 26 => z1.getD k.val false || z2.getD k.val false

lemma zOr_length (z1 z2 : List Bool) : (zOr z1 z2).length = 26 := by
  simp [zOr]

lemma zOr_getD (z1 z2 : List Bool) (i : ℕ) (hi : i < 26) :
    (zOr z1 z2).getD i false = (z1.getD i false || z2.getD i false) := by
  have hlt : i < (zOr z1 z2).length := by rw [zOr_length]; exact hi
  rw [List.getD_eq_getElem _ _ hlt]
  simp only [zOr, List.getElem_ofFn]

def evSel (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ) : Bool :=
  if w < 26 then z.getD w false
  else if w - 26 < C.gates.length then
    let j := w - 26
    let g := gateAt C j
    let u := g.inputs.getD 0 0
    let v := g.inputs.getD 1 0
    if _hu : u < w then
      if _hv : v < w then
        match g.op with
        | GateOp.or => evSel C sel z u || evSel C sel z v
        | GateOp.and => if sel j then evSel C sel z v else evSel C sel z u
        | _ => false
      else false
    else false
  else false
termination_by w

lemma evSel_input (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ) (hw : w < 26) :
    evSel C sel z w = z.getD w false := by
  rw [evSel]; simp only [hw, ↓reduceIte]

lemma evSel_ge (C : Circuit) (sel : ℕ → Bool) (z : List Bool) (w : ℕ)
    (hw : 26 + C.gates.length ≤ w) :
    evSel C sel z w = false := by
  rw [evSel]
  have h1 : ¬ (w < 26) := by omega
  have h2 : ¬ (w - 26 < C.gates.length) := by omega
  simp only [h1, h2, ↓reduceIte]

lemma evSel_or (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    evSel C sel z (26 + j) =
      (evSel C sel z ((gateAt C j).inputs.getD 0 0) || evSel C sel z ((gateAt C j).inputs.getD 1 0)) := by
  rw [evSel]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma evSel_and (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z : List Bool)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    evSel C sel z (26 + j) =
      (if sel j then evSel C sel z ((gateAt C j).inputs.getD 1 0)
       else evSel C sel z ((gateAt C j).inputs.getD 0 0)) := by
  rw [evSel]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hlt.1, hlt.2, ↓reduceDIte, hop]

lemma evSel_congr (C : Circuit) (hAO : IsAO2 26 C) (sel1 sel2 : ℕ → Bool)
    (hagree : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → sel1 j = sel2 j)
    (z : List Bool) :
    ∀ w : ℕ, evSel C sel1 z w = evSel C sel2 z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C sel1 z w h1, evSel_input C sel2 z w h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO sel1 z j hjlt hand, evSel_and C hAO sel2 z j hjlt hand,
            hagree j hjlt hand, ih _ (by omega), ih _ (by omega)]
        · rw [evSel_or C hAO sel1 z j hjlt hor, evSel_or C hAO sel2 z j hjlt hor,
            ih _ (by omega), ih _ (by omega)]
      · rw [evSel_ge C sel1 z w (by omega), evSel_ge C sel2 z w (by omega)]

lemma evSel_of_wv (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool)
    (z : List Bool) (hz : z.length = 26) :
    ∀ w : ℕ, wv C z w = true → evSel C sel z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases h1 : w < 26
    · rw [wv_input C z w (by omega)] at htrue
      rw [evSel_input C sel z w h1]
      exact htrue
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj] at htrue ⊢
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [wv_and_eq hAO hz hjlt hand, Bool.and_eq_true] at htrue
          rw [evSel_and C hAO sel z j hjlt hand]
          cases sel j
          · exact ih _ (by omega) htrue.1
          · exact ih _ (by omega) htrue.2
        · rw [wv_or_eq hAO hz hjlt hor, Bool.or_eq_true] at htrue
          rw [evSel_or C hAO sel z j hjlt hor, Bool.or_eq_true]
          rcases htrue with h | h
          · exact Or.inl (ih _ (by omega) h)
          · exact Or.inr (ih _ (by omega) h)
      · rw [wv_ge C z w (by omega)] at htrue
        cases htrue

def pickOf (C : Circuit) (z : List Bool) (j : ℕ) : Bool :=
  wv C z ((gateAt C j).inputs.getD 0 0)

lemma evSel_zOr (C : Circuit) (hAO : IsAO2 26 C) (sel : ℕ → Bool) (z1 z2 : List Bool) :
    ∀ w : ℕ, evSel C sel (zOr z1 z2) w = (evSel C sel z1 w || evSel C sel z2 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C sel _ w h1, evSel_input C sel z1 w h1, evSel_input C sel z2 w h1,
        zOr_getD z1 z2 w h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO sel _ j hjlt hand, evSel_and C hAO sel z1 j hjlt hand,
            evSel_and C hAO sel z2 j hjlt hand]
          cases sel j
          · exact ih _ (by omega)
          · exact ih _ (by omega)
        · rw [evSel_or C hAO sel _ j hjlt hor, evSel_or C hAO sel z1 j hjlt hor,
            evSel_or C hAO sel z2 j hjlt hor, ih _ (by omega), ih _ (by omega)]
          cases evSel C sel z1 ((gateAt C j).inputs.getD 0 0) <;>
          cases evSel C sel z1 ((gateAt C j).inputs.getD 1 0) <;>
          cases evSel C sel z2 ((gateAt C j).inputs.getD 0 0) <;>
          cases evSel C sel z2 ((gateAt C j).inputs.getD 1 0) <;> rfl
      · rw [evSel_ge C sel _ w (by omega), evSel_ge C sel z1 w (by omega),
          evSel_ge C sel z2 w (by omega)]
        rfl

def compatible (C : Circuit) (z : List Bool) (j : Nat) (b : Bool) : Prop :=
  (if b then wv C z ((gateAt C j).inputs.getD 1 0)
   else wv C z ((gateAt C j).inputs.getD 0 0)) =
    (wv C z ((gateAt C j).inputs.getD 0 0) && wv C z ((gateAt C j).inputs.getD 1 0))

lemma compatible_pick (C : Circuit) (z : List Bool) (j : Nat) :
    compatible C z j (pickOf C z j) := by
  unfold compatible pickOf
  cases wv C z ((gateAt C j).inputs.getD 0 0) <;> rfl

lemma evSel_valid (C : Circuit) (hAO : IsAO2 26 C) (z : List Bool) (hz : z.length = 26) (sel : Nat → Bool)
    (valid : ∀ j < C.gates.length, (gateAt C j).op=.and → compatible C z j (sel j)) :
    ∀ w : ℕ, evSel C sel z w = wv C z w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [evSel_input C _ z w h1, wv_input C z w (by omega)]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        have hlt := gate_inputs_lt hAO hjlt
        rw [hwj]
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [evSel_and C hAO _ z j hjlt hand, wv_and_eq hAO hz hjlt hand,
            ih _ (by omega), ih _ (by omega)]
          exact valid j hjlt hand
        · rw [evSel_or C hAO _ z j hjlt hor, wv_or_eq hAO hz hjlt hor,
            ih _ (by omega), ih _ (by omega)]
      · rw [evSel_ge C _ z w (by omega), wv_ge C z w (by omega)]

def andSet (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.and)] : Finset Nat :=
  (Finset.range C.gates.length).filter fun j => (gateAt C j).op=.and

theorem fiberBound {T : Type} [Fintype T] (C : Circuit) (ao : IsAO2 26 C)
    (rows : T → List Bool) (lengths : ∀ i, (rows i).length=26)
    (rejected : ∀ i, wv C (rows i) C.output=false)
    (separated : ∀ i j, i≠j → wv C (zOr (rows i) (rows j)) C.output=true)
    (k : Nat) (hk : k<C.gates.length) (andK : (gateAt C k).op=.and)
    (side : Bool) (allows : ∀ i, compatible C (rows i) k side) :
    Fintype.card T ≤ 2 ^ (nAnd C - 1) := by
  classical
  let A := andSet C
  have mem : k∈A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,andK⟩
  let sel (i : T) (j : Nat) := if j=k then side else pickOf C (rows i) j
  let code (i : T) (j : {j // j∈A.erase k}) := sel i j.val
  have agrees (i j) (hj : j<C.gates.length) (op : (gateAt C j).op=.and) :
      compatible C (rows i) j (sel i j) := by
    by_cases h : j=k
    · subst j
      simpa only [sel,if_pos rfl] using allows i
    · simpa only [sel,if_neg h] using compatible_pick C (rows i) j
  have inj : Function.Injective code := by
    intro i j eq
    by_contra diff
    have same (k' : Nat) (h : k'<C.gates.length) (op : (gateAt C k').op=.and) : sel i k'=sel j k' := by
      by_cases e : k'=k
      · simp [sel,e]
      · exact congrFun eq ⟨k',Finset.mem_erase.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h,op⟩⟩⟩
    have zeroI := (evSel_valid C ao (rows i) (lengths i) (sel i) (agrees i) C.output).trans (rejected i)
    have zeroJ := (evSel_congr C ao (sel i) (sel j) same (rows j) C.output).trans
      ((evSel_valid C ao (rows j) (lengths j) (sel j) (agrees j) C.output).trans (rejected j))
    have pos := evSel_of_wv C ao (sel i) (zOr (rows i) (rows j)) (zOr_length _ _) C.output (separated i j diff)
    rw [evSel_zOr C ao,zeroI,zeroJ] at pos
    contradiction
  have cardA : A.card=nAnd C := (nAnd_eq_card C).symm
  have sz := Fintype.card_le_of_injective code inj
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_coe,Finset.card_erase_of_mem mem,cardA] using sz

end PEqualNP.Outside.L_meta_5274
namespace PEqualNP.Outside.L_meta_5274
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.ReadTwo
open scoped BigOperators

theorem rawBefore (C : Circuit) (ao : IsAO2 26 C) (k : Nat) (hk : k<C.gates.length)
    (early : ∀ j<k, (gateAt C j).op ≠ .and) (w : Nat) (hw : w<26+k) :
    ∃ A : Finset (Fin 26), ∀ x : List Bool, x.length=26 →
      (wv C x w=true ↔ ∃ i∈A, x.getD i.val false=true) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases raw : w<26
    · refine ⟨{⟨w,raw⟩},fun x hx => ?_⟩
      rw [wv_input C x w (by omega)]
      simp
    · let j := w-26
      have hlt : j<k := by dsimp [j]; omega
      have acc : j<C.gates.length := by omega
      have eq : w=26+j := by dsimp [j]; omega
      have gmem : gateAt C j ∈ C.gates := by
        simp only [gateAt,List.getD_eq_getElem _ _ acc]; exact List.getElem_mem acc
      have op := (ao.1 _ gmem).resolve_left (early j hlt)
      have lt := gate_inputs_lt ao acc
      obtain ⟨A,hA⟩ := ih _ (by omega : ((gateAt C j).inputs.getD 0 0)<w) (by omega)
      obtain ⟨B,hB⟩ := ih _ (by omega : ((gateAt C j).inputs.getD 1 0)<w) (by omega)
      refine ⟨A∪B,fun x hx => ?_⟩
      rw [eq,wv_or_eq ao hx acc op,Bool.or_eq_true,hA x hx,hB x hx]
      simp only [Finset.mem_union]
      constructor
      · rintro (⟨i,hi,hv⟩|⟨i,hi,hv⟩)
        · exact ⟨i,Or.inl hi,hv⟩
        · exact ⟨i,Or.inr hi,hv⟩
      · rintro ⟨i,hi,hv⟩
        rcases hi with hu|hu
        · exact Or.inl ⟨i,hu,hv⟩
        · exact Or.inr ⟨i,hu,hv⟩

def occurrences {T : Type} [Fintype T] (rows : T → List Bool) (A : Finset (Fin 26)) :
    Finset T := Finset.univ.filter fun t => ∃ i∈A, (rows t).getD i.val false=true

set_option maxHeartbeats 500000 in
theorem counting {T : Type} [Fintype T] [DecidableEq T] (cardT : Fintype.card T=234)
    (C : Circuit) (ao : IsAO2 26 C) (lower : 0<nAnd C)
    (rows : T → List Bool) (lengths : ∀ t, (rows t).length=26)
    (rejected : ∀ i, wv C (rows i) C.output=false)
    (separated : ∀ i j, i≠j → wv C (zOr (rows i) (rows j)) C.output=true)
    (board : ∀ A B : Finset (Fin 26),
      106 ≤ (occurrences rows A).card → 106 ≤ (occurrences rows B).card →
      24 ≤ ((occurrences rows A) ∩ (occurrences rows B)).card) : 9≤nAnd C := by
  classical
  by_contra! small
  let S := andSet C
  have sc : S.card=nAnd C := (nAnd_eq_card C).symm
  have ne : S.Nonempty := Finset.card_pos.mp (by omega)
  let k := S.min' ne
  have km := S.min'_mem ne
  have hkm : k∈S := km
  obtain ⟨h,hk⟩ := Finset.mem_filter.mp hkm
  have valid := Finset.mem_range.mp h
  have early j (hj : j<k) (bad : (gateAt C j).op=.and) : False := by
    have mem : j∈S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),bad⟩
    exact (Nat.not_le_of_lt hj) (S.min'_le j mem)
  have lt := gate_inputs_lt ao valid
  obtain ⟨A,ap⟩ := rawBefore C ao k valid early _ lt.1
  obtain ⟨B,bp⟩ := rawBefore C ao k valid early _ lt.2
  let a := occurrences rows A
  let b := occurrences rows B
  have eqA t : t∈a ↔ wv C (rows t) ((gateAt C k).inputs.getD 0 0)=true := by
    simpa only [a,occurrences,Finset.mem_filter,Finset.mem_univ,true_and] using (ap _ (lengths t)).symm
  have eqB t : t∈b ↔ wv C (rows t) ((gateAt C k).inputs.getD 1 0)=true := by
    simpa only [b,occurrences,Finset.mem_filter,Finset.mem_univ,true_and] using (bp _ (lengths t)).symm
  let side (v : Bool) := Finset.univ.filter fun t => compatible C (rows t) k v
  have cap v : (side v).card ≤128 := by
    have f := fiberBound C ao (fun t : {t // t∈side v} => rows t.val)
      (fun t => lengths t.val) (fun t => rejected t.val)
      (fun i j hne => separated i.val j.val (fun h => hne (Subtype.ext h)))
      k valid hk v (fun t => (Finset.mem_filter.mp t.property).2)
    rw [Fintype.card_coe] at f
    exact f.trans (Nat.pow_le_pow_right (by decide : 0<2) (by omega : nAnd C-1≤7))
  have member (t : T) (v : Bool) : t∈side v ↔ compatible C (rows t) k v :=
    ⟨fun h => (Finset.mem_filter.mp h).2,fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  have lor : ∀ x y : Bool, x=(x&&y) ∨ y=(x&&y) := by decide
  have lf : ∀ x y : Bool, x=false → x=(x&&y) := by decide
  have rf : ∀ x y : Bool, y=false → y=(x&&y) := by decide
  have eqt : ∀ x y : Bool, x=true → y=true → x=(x&&y) ∧ y=(x&&y) := by decide
  have all : (side false ∪ side true) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro t
    apply Finset.mem_union.mpr
    rw [member,member]
    exact lor _ _
  have ha : Finset.univ ⊆ side false ∪ a := by
    intro t _
    by_cases h : t∈a
    · exact Finset.mem_union_right _ h
    · have hz := Bool.eq_false_iff.mpr (fun e => h ((eqA t).2 e))
      exact Finset.mem_union_left _ ((member t false).2 (lf _ _ hz))
  have hb : Finset.univ ⊆ side true ∪ b := by
    intro t _
    by_cases h : t∈b
    · exact Finset.mem_union_right _ h
    · have hz := Bool.eq_false_iff.mpr (fun e => h ((eqB t).2 e))
      exact Finset.mem_union_left _ ((member t true).2 (rf _ _ hz))
  have ac := (Finset.card_le_card ha).trans (Finset.card_union_le _ _)
  have bc := (Finset.card_le_card hb).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ,cardT] at ac bc
  have c0:=cap false
  have c1:=cap true
  have sizeA : 106≤a.card := by omega
  have sizeB : 106≤b.card := by omega
  have overlap : 24 ≤ (a∩b).card := board A B sizeA sizeB
  have sub : a∩b ⊆ side false ∩ side true := by
    intro t ht
    obtain ⟨u,v⟩ := Finset.mem_inter.mp ht
    have g := (eqA t).mp u
    have h := (eqB t).mp v
    have both := eqt _ _ g h
    exact Finset.mem_inter.mpr ⟨(member t false).2 both.1,(member t true).2 both.2⟩
  have lowerAB := overlap.trans (Finset.card_le_card sub)
  have total := Finset.card_union_add_card_inter (side false) (side true)
  rw [all,Finset.card_univ,cardT] at total
  omega
end PEqualNP.Outside.L_meta_5274

namespace Board5278
open PEqualNP.HeptadCover
abbrev V := Fin 13
abbrev Row := Fin 18 × V
def pTab : Array Nat := #[29, 39, 71, 77, 83, 85, 101, 105, 135, 141, 195, 201, 275, 281, 297, 329, 337, 549]
def lTab : Array Nat := #[2592, 392, 896, 2816, 644, 2688, 2432, 2306, 776, 800, 772, 770, 580, 2624, 2114, 2562, 2564, 2184]
def pt (r : Row) (p : V) : Bool := (pTab[r.1.val]!).testBit (p-r.2).val
def ln (r : Row) (l : V) : Bool := (lTab[r.1.val]!).testBit (l-r.2).val
def P (p : V) : Finset Row := Finset.univ.filter fun r => pt r p
def L (p : V) : Finset Row := Finset.univ.filter fun r => ln r p
def points (r : Row) : Finset V := Finset.univ.filter fun p => pt r p
def move (s : V) (r : Row) : Row := (r.1,r.2+s)
lemma ptMove (r : Row) (s i : V) : pt (move s r) (i+s) = pt r i := by
  simp [pt,move]
lemma lnMove (r : Row) (s i : V) : ln (move s r) (i+s) = ln r i := by
  simp [ln,move]
theorem allQuads : ∀ r : Row, IsQuadrangle singerLines3 (points r) := by decide +kernel
theorem miss : ∀ (r : Row) (l : V), (ln r l=true) ↔ l∈missLines singerLines3 (points r) := by decide +kernel
theorem outside : ∀ (r : Row) (p : V), pt r p=false →
    ∃ l : V, ln r l=true ∧ p∈singerLines3 l := by decide +kernel
theorem apartBase : ∀ (i j : Fin 18) (s : V), (i,(0:V)) ≠ (j,s) →
    ∃ p : V, pt (i,0) p=true ∧ pt (j,s) p=false := by decide +kernel
theorem apart (a b : Row) (hne : a ≠ b) : ∃ p : V, pt a p=true ∧ pt b p=false := by
  obtain ⟨i,t⟩ := a
  obtain ⟨j,u⟩ := b
  have diff : (i,(0:V)) ≠ (j,u-t) := by
    intro h
    have f := congrArg (move t) h
    exact hne (by simpa only [move,zero_add,sub_add_cancel] using f)
  obtain ⟨p,hp,hn⟩ := apartBase i j (u-t) diff
  refine ⟨p+t,?_,?_⟩
  · simpa only [move,zero_add] using (ptMove (i,0) t p).trans hp
  · simpa only [move,sub_add_cancel] using (ptMove (j,u-t) t p).trans hn

def shifted (s : V) (X : Finset Row) : Finset Row := X.image (move s)
lemma injMove (s : V) : Function.Injective (move s) := by
  rintro ⟨i,t⟩ ⟨j,u⟩ h
  have eq := congrArg (move (-s)) h
  simpa [move] using eq
lemma shiftP (s i : V) : shifted s (P i) = P (i+s) := by
  ext r
  constructor
  · intro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,ptMove] at ht ⊢
    exact ht
  · intro h
    refine Finset.mem_image.mpr ⟨move (-s) r,?_,by rcases r with ⟨a,b⟩; simp [move]⟩
    have e := ptMove r (-s) (i+s)
    simpa [P] using (e.trans (Finset.mem_filter.mp h).2)
lemma shiftL (s i : V) : shifted s (L i) = L (i+s) := by
  ext r
  constructor
  · intro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    simp only [L,Finset.mem_filter,Finset.mem_univ,true_and,lnMove] at ht ⊢
    exact ht
  · intro h
    refine Finset.mem_image.mpr ⟨move (-s) r,?_,by rcases r with ⟨a,b⟩; simp [move]⟩
    have e := lnMove r (-s) (i+s)
    simpa [L] using (e.trans (Finset.mem_filter.mp h).2)
lemma shiftUnion (s : V) (X Y : Finset Row) : shifted s (X∪Y)=shifted s X∪shifted s Y :=
  by simp [shifted,Finset.image_union]
lemma shiftInter (s : V) (X Y : Finset Row) : shifted s (X∩Y)=shifted s X∩shifted s Y := by
  exact Finset.image_inter _ _ (injMove s)
lemma shiftCard (s : V) (X : Finset Row) : (shifted s X).card=X.card :=
  Finset.card_image_of_injective _ (injMove s)

theorem point0 : (P 0).card ≤ 99 := by decide +kernel
theorem lines0 : ∀ l : V, (L 0 ∪ L l).card ≤ 99 := by decide +kernel
theorem pp0 : ∀ p : V, 18 ≤ (P 0 ∩ P p).card := by decide +kernel
theorem ll0 : ∀ l : V, 9 ≤ (L 0 ∩ L l).card := by decide +kernel
theorem mixed0 : ∀ l : V, (0 : V) ∉ singerLines3 l → 24 ≤ (P 0 ∩ L l).card := by decide +kernel
theorem incident0 : ∀ l : V, (0 : V) ∈ singerLines3 l → P 0 ∩ L l = ∅ := by decide +kernel
theorem twoPts0 : ∀ a b : V, a≠b → 24 ≤ (P 0 ∩ (P a ∪ P b)).card := by decide +kernel
theorem thin : ∀ a b i j : V, a≠b → i≠j → a∈singerLines3 i → a∈singerLines3 j →
    b∈singerLines3 i → b∉singerLines3 j := by decide +kernel

theorem card0 : (L 0).card=54 := by decide +kernel
theorem pairs0 : ∀ a : V, a≠0 → (L 0∩L a).card=9 := by decide +kernel
theorem triple0 : ∀ a b : V, a≠0 → b≠0 → a≠b → ((L 0 ∩ L a) ∩ L b).card≤1 := by decide +kernel

theorem threeLs0 (a b c : V) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    24 ≤ (L 0 ∩ ((L a∪L b)∪L c)).card := by
  let U := L 0 ∩ L a
  let Vv := L 0 ∩ L b
  let W := L 0 ∩ L c
  have distribute : L 0 ∩ ((L a∪L b)∪L c)=(U∪Vv)∪W := by
    ext t
    simp only [U,Vv,W,Finset.mem_inter,Finset.mem_union]
    tauto
  rw [distribute]
  have u (r s : Board5278.V) (hr : r≠0) (hs : s≠0) (hrs : r≠s) :
      ((L 0∩L r)∩(L 0∩L s)).card ≤ 1 := by
    exact (Finset.card_le_card (show (L 0∩L r)∩(L 0∩L s) ⊆ (L 0∩L r)∩L s from
      Finset.inter_subset_inter_left _ Finset.inter_subset_right)).trans (triple0 r s hr hs hrs)
  have big (X : Finset Row) (h : L 0 ⊆ X) : 24 ≤ X.card := by
    have := Finset.card_le_card h
    rw [card0] at this
    omega
  by_cases ha : a=0
  · apply big
    intro t ht
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ht,ha.symm ▸ ht⟩))
  by_cases hb : b=0
  · apply big
    intro t ht
    exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ht,hb.symm ▸ ht⟩))
  by_cases hc : c=0
  · apply big
    intro t ht
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ht,hc.symm ▸ ht⟩)
  have cu : U.card=9 := pairs0 a ha
  have cv : Vv.card=9 := pairs0 b hb
  have cw : W.card=9 := pairs0 c hc
  have uv : (U∩Vv).card≤1 := u a b ha hb hab
  have uw : (U∩W).card≤1 := u a c ha hc hac
  have vw : (Vv∩W).card≤1 := u b c hb hc hbc
  have split : (U∪Vv)∩W ⊆ (U∩W)∪(Vv∩W) := by
    intro t ht
    obtain ⟨h,w⟩ := Finset.mem_inter.mp ht
    rcases Finset.mem_union.mp h with l|r
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨l,w⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨r,w⟩)
  have pair := (Finset.card_le_card split).trans (Finset.card_union_le _ _)
  have first := Finset.card_union_add_card_inter U Vv
  have last := Finset.card_union_add_card_inter (U∪Vv) W
  omega

end Board5278

namespace Board5278
open PEqualNP.HeptadCover

lemma pointCard (p : V) : (P p).card ≤99 := by
  have h := point0
  rw [←shiftCard p _] at h
  simpa only [shiftP,zero_add] using h
lemma lineUnionCard (a b : V) : (L a ∪ L b).card ≤99 := by
  have h := lines0 (b-a)
  rw [←shiftCard a _] at h
  simpa only [shiftUnion,shiftL,zero_add,sub_add_cancel] using h
lemma shiftNe (r a b : V) (h : a≠b) : a-r≠b-r := by
  intro eq
  exact h (by simpa only [sub_add_cancel] using congrArg (fun v : V => v+r) eq)
lemma twoPoints (r a b : V) (ha : a≠b) : 24 ≤ (P r ∩ (P a ∪ P b)).card := by
  have h := twoPts0 (a-r) (b-r) (shiftNe r a b ha)
  rw [←shiftCard r _] at h
  simpa only [shiftInter,shiftUnion,shiftP,zero_add,sub_add_cancel] using h
lemma threeLines (r a b c : V) (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    24 ≤ (L r ∩ ((L a ∪ L b) ∪ L c)).card := by
  have h := threeLs0 (a-r) (b-r) (c-r) (shiftNe r a b ab)
    (shiftNe r a c ac) (shiftNe r b c bc)
  rw [←shiftCard r _] at h
  simpa only [shiftInter,shiftUnion,shiftL,zero_add,sub_add_cancel] using h
lemma pointPair (p q : V) : 18 ≤ (P p ∩ P q).card := by
  have h := pp0 (q-p)
  rw [←shiftCard p _] at h
  simpa only [shiftInter,shiftP,zero_add,sub_add_cancel] using h
lemma linePair (l m : V) : 9 ≤ (L l ∩ L m).card := by
  have h := ll0 (m-l)
  rw [←shiftCard l _] at h
  simpa only [shiftInter,shiftL,zero_add,sub_add_cancel] using h
lemma incidenceShift : ∀ (p l : V), p ∈ singerLines3 l ↔ 0 ∈ singerLines3 (l-p) := by decide +kernel
lemma offFlag (p l : V) (hn : p∉singerLines3 l) : 24 ≤ (P p ∩ L l).card := by
  have h := mixed0 (l-p) ((incidenceShift p l).not.mp hn)
  rw [←shiftCard p _] at h
  simpa only [shiftInter,shiftP,shiftL,zero_add,sub_add_cancel] using h
lemma onFlag (p l : V) (hy : p∈singerLines3 l) : Disjoint (P p) (L l) := by
  have h := congrArg (shifted p) (incident0 (l-p) ((incidenceShift p l).mp hy))
  rw [shiftInter,shiftP,shiftL,zero_add,sub_add_cancel] at h
  exact Finset.disjoint_iff_inter_eq_empty.mpr (by simpa [shifted] using h)

inductive Rich (S : Finset Row) : Prop
  | pp (a b : V) (ne : a≠b) (ha : P a⊆S) (hb : P b⊆S)
  | pl (p l : V) (hp : P p⊆S) (hl : L l⊆S)
  | lll (a b c : V) (ab : a≠b) (ac : a≠c) (bc : b≠c)
       (ha : L a⊆S) (hb : L b⊆S) (hc : L c⊆S)

def generated (X : Finset Row) : Prop := ∀ r∈X,
  (∃ p, r∈P p ∧ P p⊆X) ∨ (∃ l, r∈L l ∧ L l⊆X)

lemma richOf {X : Finset Row} (gen : generated X) (big : 106≤X.card) : Rich X := by
  classical
  have outsideOf (Y : Finset Row) (dim : Y.card≤99) : ∃ r∈X,r∉Y := by
    by_contra! hall
    have inc : X⊆Y := hall
    have := Finset.card_le_card inc
    omega
  by_cases havePoint : ∃ p, P p⊆X
  · obtain ⟨p,hp⟩ := havePoint
    obtain ⟨r,hr,hn⟩ := outsideOf (P p) (pointCard p)
    rcases gen r hr with ⟨q,hq,sub⟩ | ⟨l,_,sub⟩
    · exact .pp p q (fun e => hn (e.symm ▸ hq)) hp sub
    · exact .pl p l hp sub
  · have line (r) (h : r∈X) : ∃ l, r∈L l ∧ L l⊆X := (gen r h).resolve_left
        (fun ⟨p,_,hp⟩ => havePoint ⟨p,hp⟩)
    obtain ⟨r,hr,_⟩ := outsideOf ∅ (by simp)
    obtain ⟨a,_,ha⟩ := line r hr
    obtain ⟨s,hs,hsa⟩ := outsideOf (L a) (by simpa using lineUnionCard a a)
    obtain ⟨b,hsb,hb⟩ := line s hs
    obtain ⟨t,ht,htab⟩ := outsideOf (L a∪L b) (lineUnionCard a b)
    obtain ⟨c,htc,hc⟩ := line t ht
    refine .lll a b c (fun e => hsa (e.symm ▸ hsb)) ?_ ?_ ha hb hc
    · intro e; subst c; exact htab (Finset.mem_union_left _ htc)
    · intro e; subst c; exact htab (Finset.mem_union_right _ htc)

lemma charge {F G X Y : Finset Row} (floor : 24≤(F∩G).card) (f : F⊆X) (g : G⊆Y) :
    24≤(X∩Y).card := floor.trans (Finset.card_le_card (Finset.inter_subset_inter f g))

lemma PPvs {X Y : Finset Row} (a b : V) (ne : a≠b) (ha : P a⊆X) (hb : P b⊆X)
    (rich : Rich Y) : 24 ≤ (X∩Y).card := by
  have pin p (hp : P p⊆Y) : 24 ≤ (X∩Y).card := by
    rw [Finset.inter_comm X Y]
    exact charge (twoPoints p a b ne) hp (Finset.union_subset ha hb)
  cases rich with
  | pp p q _ h _ => exact pin p h
  | pl p l h _ => exact pin p h
  | lll l m t lm _ _ hl hm _ =>
    by_cases al : a∈singerLines3 l
    · by_cases am : a∈singerLines3 m
      · by_cases bl : b∈singerLines3 l
        · exact charge (offFlag b m (thin a b l m ne lm al am bl)) hb hm
        · exact charge (offFlag b l bl) hb hl
      · exact charge (offFlag a m am) ha hm
    · exact charge (offFlag a l al) ha hl

lemma mixedVs {X Y : Finset Row} (p l q m : V) (hp : P p⊆X) (hl : L l⊆X)
    (hq : P q⊆Y) (hm : L m⊆Y) : 24≤(X∩Y).card := by
  by_cases inc : p∈singerLines3 m
  · let A := P p∩P q
    let B := L l∩L m
    have dis : Disjoint A B := (onFlag p m inc).mono Finset.inter_subset_left Finset.inter_subset_right
    have sub : A∪B ⊆ X∩Y := Finset.union_subset (Finset.inter_subset_inter hp hq)
      (Finset.inter_subset_inter hl hm)
    have dim := Finset.card_le_card sub
    rw [Finset.card_union_of_disjoint dis] at dim
    have d : 18≤A.card := pointPair p q
    have e : 9≤B.card := linePair l m
    omega
  · exact charge (offFlag p m inc) hp hm

lemma intersection {X Y : Finset Row} (a : Rich X) (b : Rich Y) : 24≤(X∩Y).card := by
  cases a with
  | pp p q ne hp hq => exact PPvs p q ne hp hq b
  | pl p l hp hl =>
    cases b with
    | pp u v ne hu hv => simpa only [Finset.inter_comm Y X] using PPvs u v ne hu hv (.pl p l hp hl)
    | pl u v hu hv => exact mixedVs p l u v hp hl hu hv
    | lll i j k ij ik jk hi hj hk =>
      exact charge (threeLines l i j k ij ik jk) hl (Finset.union_subset (Finset.union_subset hi hj) hk)
  | lll i j k ij ik jk hi hj hk =>
    rw [Finset.inter_comm X Y]
    have use l (hl : L l⊆Y) := charge (threeLines l i j k ij ik jk) hl
      (Finset.union_subset (Finset.union_subset hi hj) hk)
    cases b with
    | pp u v ne hu hv => exact PPvs u v ne hu hv (.lll i j k ij ik jk hi hj hk)
    | pl _ l _ hl => exact use l hl
    | lll l _ _ _ _ _ hl _ _ => exact use l hl

end Board5278

namespace PEqualNP.Outside.L_meta_5274
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover PEqualNP.ReadTwo
open Board5278

def actual (r : Row) := quadInput (points r)
lemma pointRead (r : Row) (p : V) : (actual r).getD p.val false=true ↔ r∈P p := by
  simp [actual,quadInput_getD_pt,points,P]
lemma lineRead (r : Row) (l : V) : (actual r).getD (13+l.val) false=true ↔ r∈L l := by
  simp only [actual,quadInput_getD_ln,decide_eq_true_eq,L,Finset.mem_filter,Finset.mem_univ,true_and]
  exact (miss r l).symm
lemma generatedActual (A : Finset (Fin 26)) : generated (occurrences actual A) := by
  intro r hr
  obtain ⟨i,hi,hit⟩ := (Finset.mem_filter.mp hr).2
  by_cases low : i.val<13
  · let p : V := ⟨i.val,low⟩
    refine Or.inl ⟨p,(pointRead r p).1 hit,?_⟩
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,(pointRead t p).2 ht⟩
  · let l : V := ⟨i.val-13,by have := i.isLt; omega⟩
    have back : 13+l.val=i.val := by dsimp [l]; omega
    refine Or.inr ⟨l,(lineRead r l).1 (by simpa only [back] using hit),?_⟩
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,by simpa only [back] using (lineRead t l).2 ht⟩

lemma actualSeparation (C : Circuit) (ao : IsAO2 26 C)
    (positive : ∀ p l : V,p∈singerLines3 l → C.eval (pairInput p l)=true)
    (a b : Row) (hne : a≠b) : wv C (zOr (actual a) (actual b)) C.output=true := by
  obtain ⟨p,hp,abs⟩ := apart a b hne
  obtain ⟨l,hl,inc⟩ := outside b p abs
  apply wv_mono ao (pairInput_length p l) (zOr_length _ _) _ C.output (positive p l inc)
  intro i hi h
  rw [zOr_getD _ _ i hi,Bool.or_eq_true]
  rcases pairInput_getD_true p l i hi h with rfl | rfl
  · exact Or.inl ((pointRead a p).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩))
  · exact Or.inr ((lineRead b l).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩))

theorem atLeastNine (C : Circuit) (ao : IsAO2 26 C) (nonempty : 0<nAnd C)
    (positive : ∀ p l : V,p∈singerLines3 l → C.eval (pairInput p l)=true)
    (negative : ∀ Q∈quadrangles singerLines3,C.eval (quadInput Q)=false) : 9≤nAnd C := by
  classical
  refine counting (T:=Row) (by decide) C ao nonempty actual (fun r => quadInput_length _) ?_
    (actualSeparation C ao positive) ?_
  · intro r
    apply negative
    apply Finset.mem_filter.mpr
    have h := allQuads r
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,h.1⟩,h.2⟩
  · intro A B ha hb
    exact intersection (richOf (generatedActual A) ha) (richOf (generatedActual B) hb)

theorem coverAtLeastNine (C : Circuit) (J : Finset Nat) (ao : IsAO2 26 C)
    (prev : 8≤nAnd C)
    (cover : ∀ x : List Bool,x.length=26 →
      (C.eval x=true ↔ ∃ j∈J, PEqualNP.LowMerge.wireVal C x (26+j)=true))
    (flags : ∀ p l : V, p∈singerLines3 l →
      ∃ j∈J, PEqualNP.LowMerge.wireVal C (pairInput p l) (26+j)=true)
    (quiet : ∀ j∈J, ∀ Q∈quadrangles singerLines3, PEqualNP.LowMerge.wireVal C (quadInput Q) (26+j)=false) :
    9≤nAnd C := by
  apply atLeastNine C ao (by omega)
  · exact fun p l h => (cover _ (pairInput_length p l)).2 (flags p l h)
  · intro Q hQ
    apply Bool.eq_false_iff.mpr
    intro bad
    obtain ⟨j,hj,fire⟩ := (cover _ (quadInput_length Q)).1 bad
    exact Bool.noConfusion ((quiet j hj Q hQ).symm.trans fire)
end PEqualNP.Outside.L_meta_5274

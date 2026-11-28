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
      aesop

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
  have all : (side false ∪ side true) = Finset.univ := by
    ext t
    simp only [side,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true,compatible]
    cases wv C (rows t) ((gateAt C k).inputs.getD 0 0) <;>
      cases wv C (rows t) ((gateAt C k).inputs.getD 1 0) <;> decide
  have ha : Finset.univ ⊆ side false ∪ a := by
    intro t _
    by_cases h : t∈a
    · exact Finset.mem_union_right _ h
    · have hz := Bool.eq_false_iff.mpr (fun e => h ((eqA t).2 e))
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [compatible,hz]⟩)
  have hb : Finset.univ ⊆ side true ∪ b := by
    intro t _
    by_cases h : t∈b
    · exact Finset.mem_union_right _ h
    · have hz := Bool.eq_false_iff.mpr (fun e => h ((eqB t).2 e))
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [compatible,hz]⟩)
  have ac := (Finset.card_le_card ha).trans (Finset.card_union_le _ _)
  have bc := (Finset.card_le_card hb).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ,cardT] at ac bc
  have c0:=cap false
  have c1:=cap true
  have overlap : 24 ≤ (a∩b).card := board A B (by omega) (by omega)
  have sub : a∩b ⊆ side false ∩ side true := by
    intro t ht
    obtain ⟨u,v⟩ := Finset.mem_inter.mp ht
    have g := (eqA t).mp u
    have h := (eqB t).mp v
    simp [side,compatible,g,h]
  have lowerAB := overlap.trans (Finset.card_le_card sub)
  have total := Finset.card_union_add_card_inter (side false) (side true)
  rw [all,Finset.card_univ,cardT] at total
  omega
end PEqualNP.Outside.L_meta_5274

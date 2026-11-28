import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18593.Donor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
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

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
theorem junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
theorem binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
theorem opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
theorem opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
theorem andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
theorem andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
theorem operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
theorem operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
theorem operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
theorem inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hr, hjv⟩

lemma residualConnection (hL : IsLeastAO G C) (hT : TopForm G C)
    (he : (Ustar G C).Nonempty) :
    (centreless G C).Nonempty ∨ (orN G C \ lam G C).Nonempty := by
  obtain ⟨e, he⟩ := he
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, hr, _⟩ := residualTrace hL hT he
    rcases lastOrBefore (orReaches_reach j _ hr).1 with heq | ⟨m, hl, ho, hi, hb, _⟩
    · have hz : side (n := n) C a b = ∅ := by
        change orIn n C (opnd C a b) = ∅
        rw [heq]
        exact andRawEmpty (junkData hj).2.1
      left
      refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
      fin_cases b
      · exact .inl hz
      · exact .inr hz
    · exact .inr ⟨m, lastOrOutside hL.1 hj hl ho hi hb⟩

lemma firstResidualGate (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ j ∈ junk G C, gateVal n C j (pairInput u v) = true ∧
      (∀ k ∈ junk G C, k < j → gateVal n C k (pairInput u v) = false) ∧
      ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b := by
  obtain ⟨_, _, _, j, hj, _, hjv⟩ := residualTrace hL hT he
  let fires (k : ℕ) := k ∈ junk G C ∧ gateVal n C k (pairInput u v) = true
  have hex : ∃ k, fires k := ⟨j, hj, hjv⟩
  let k := Nat.find hex
  have hk : fires k := Nat.find_spec hex
  have hfirst (i : ℕ) (hi : i ∈ junk G C) (hik : i < k) :
      gateVal n C i (pairInput u v) = false := by
    apply Bool.eq_false_iff.mpr
    intro hon
    exact (Nat.not_le_of_lt hik) (Nat.find_min' hex ⟨hi, hon⟩)
  refine ⟨k, hk.1, hk.2, hfirst, ?_⟩
  obtain ⟨hlen, hop, _⟩ := junkData hk.1
  intro b
  have hval := (andValOperands hL.1 hlen hop _).mp hk.2 b
  rcases operandSupport hL.1 hT hlen hop hval with ⟨t, ht, rfl | rfl⟩ | ⟨i, hi, hr, hv⟩
  · exact .inl ht
  · exact .inr ht
  · exact (Bool.false_ne_true ((hfirst i hi (operandReachLt hL.1 hlen hr)).symm.trans hv)).elim

end PEqualNP.Outside.L_meta_18593.Donor

theorem PEqualNP.Outside.L_meta_18593.Donor :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ((PEqualNP.TopForm.Ustar x2 x4).Nonempty → (0 : ℕ) < (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) ∧ ∀ (x7 x8 : Fin x1), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x2 x4 → ∃ x10 ∈ PEqualNP.TopForm.junk x2 x4, ∀ (x11 : Fin (2 : ℕ)), x7 ∈ PEqualNP.TopForm.side x4 x10 x11 ∨ x8 ∈ PEqualNP.TopForm.side x4 x10 x11 := by
  intro n G _ C least top
  constructor
  · intro nonempty
    rcases PEqualNP.Outside.L_meta_18593.Donor.residualConnection least top nonempty with h | h
    · have hpos := Finset.card_pos.mpr h
      omega
    · have hpos := Finset.card_pos.mpr h
      omega
  · intro u v he
    obtain ⟨j, hj, _, _, hits⟩ :=
      PEqualNP.Outside.L_meta_18593.Donor.firstResidualGate least top he
    exact ⟨j, hj, hits⟩

namespace PEqualNP.Outside.L_meta_18593.Cut
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem cuts {n k : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (ao : IsAO2 n C) (tf : TopForm G C) (X : Fin k → Fin n → Bool)
    (fails : ∀ i, ∃ j∈junk G C,gateVal n C j (X i)=false)
    (joins : ∀ i t,i≠t → ∃ u v : Fin n, (X i u=true ∨ X t u=true) ∧
      (X i v=true ∨ X t v=true) ∧ ∀ j∈junk G C,gateVal n C j (pairInput u v)=true) :
    k ≤ (junk G C).card*2 := by
  classical
  let pick (i : Fin k) := Nat.find (fails i)
  have mem (i : Fin k) : pick i ∈ junk G C := (Nat.find_spec (fails i)).1
  have failat (i : Fin k) : gateVal n C (pick i) (X i)=false := (Nat.find_spec (fails i)).2
  have earlier (i : Fin k) (g : Nat) (hg : g∈junk G C) (lt : g<pick i) : gateVal n C g (X i)=true := by
    cases hv : gateVal n C g (X i) with
    | false => exact False.elim ((Nat.find_min (fails i) lt) ⟨hg,hv⟩)
    | true => rfl
  have free (i : Fin k) : ∃ b : Fin 2,Donor.val C (List.ofFn (X i)) (opnd C (pick i) b)=false := by
    obtain ⟨bound,op,_⟩ := Donor.junkData (mem i)
    by_contra h
    have all : ∀ b : Fin 2,Donor.val C (List.ofFn (X i)) (opnd C (pick i) b)=true := by
      intro b
      cases hb : Donor.val C (List.ofFn (X i)) (opnd C (pick i) b) with
      | false => exact False.elim (h ⟨b,hb⟩)
      | true => rfl
    have h := (Donor.andValOperands ao bound op (X i)).mpr all
    rw [failat] at h
    cases h
  choose side off using free
  let tag (i : Fin k) : (junk G C) × Fin 2 := (⟨pick i,mem i⟩,side i)
  have inj : Function.Injective tag := by
    intro i t eq
    by_contra ne
    have same : pick t=pick i := (congrArg (fun z : (junk G C) × Fin 2 => z.1.val) eq).symm
    have sb : side t=side i := (congrArg (fun z : (junk G C) × Fin 2 => z.2) eq).symm
    have ti := off t
    rw [same,sb] at ti
    obtain ⟨u,v,hu,hv,on⟩ := joins i t ne
    obtain ⟨bound,op,_⟩ := Donor.junkData (mem i)
    have arm := (Donor.andValOperands ao bound op _).mp (on _ (mem i)) (side i)
    rcases Donor.operandSupport ao tf bound op arm with ⟨p,hp,ep⟩|⟨g,hg,reach,_⟩
    · have xp : X i p=true ∨ X t p=true := ep.elim (fun e => e ▸ hu) (fun e => e ▸ hv)
      rcases xp with xp|xp
      · have z := Donor.sideVal hp xp
        rw [off i] at z
        cases z
      · have z := Donor.sideVal hp xp
        rw [ti] at z
        cases z
    · have active := earlier i g hg (Donor.operandReachLt ao bound reach)
      have z := Donor.orStep_up (n:=n) (C:=C) (by simp : (List.ofFn (X i)).length=n)
        (Donor.orReaches_reach g _ reach).1 (show Donor.val C (List.ofFn (X i)) (n+g)=true from active)
      rw [off i] at z
      cases z
  have bound := Fintype.card_le_of_injective tag inj
  simpa only [Fintype.card_fin,Fintype.card_prod,Fintype.card_coe] using bound

end PEqualNP.Outside.L_meta_18593.Cut



namespace PEqualNP.Outside.L_meta_18593.Probes
def board (a b c d e f : Bool) (i j : Fin 3) : Bool :=
  match i.val,j.val with
  | 0,1 => a
  | 0,2 => b
  | 1,0 => c
  | 1,2 => d
  | 2,0 => e
  | 2,1 => f
  | _,_ => true
def rows (a b c d e f : Bool) (h : Fin 5) : Nat :=
  let code : Nat := (if a then 1 else 0)+(if b then 2 else 0)+(if c then 4 else 0)+(if d then 8 else 0)+(if e then 16 else 0)+(if f then 32 else 0)
  match code with
  | 0 => [7,14,21,28,35].getD h.val 0
  | 1 => [7,14,28,35,42].getD h.val 0
  | 2 => [7,14,21,28,42].getD h.val 0
  | 3 => [7,14,28,42,56].getD h.val 0
  | 4 => [7,21,28,35,49].getD h.val 0
  | 6 => [7,21,28,34,56].getD h.val 0
  | 8 => [7,14,21,28,49].getD h.val 0
  | 9 => [7,14,28,33,56].getD h.val 0
  | 10 => [7,14,21,28,56].getD h.val 0
  | 12 => [7,21,28,49,56].getD h.val 0
  | 16 => [7,21,35,42,49].getD h.val 0
  | 17 => [7,20,35,42,56].getD h.val 0
  | 20 => [7,21,35,49,56].getD h.val 0
  | 24 => [7,10,21,49,56].getD h.val 0
  | 25 => [7,10,20,33,56].getD h.val 0
  | 32 => [7,14,35,42,49].getD h.val 0
  | 33 => [7,14,35,42,56].getD h.val 0
  | 34 => [7,14,17,42,56].getD h.val 0
  | 36 => [7,12,35,49,56].getD h.val 0
  | 38 => [7,12,17,34,56].getD h.val 0
  | 48 => [7,35,42,49,56].getD h.val 0
  | _ => 0

def L (r : Nat) (i : Fin 3) := r.testBit i.val
def R (r : Nat) (i : Fin 3) := r.testBit (3+i.val)
def SquareFree (B : Fin 3 → Fin 3 → Bool) : Prop := ∀ i j k l, i≠j → k≠l →
  B i k=true → B j k=true → B i l=true → B j l=false
def Good (B : Fin 3 → Fin 3 → Bool) (r : Fin 5 → Nat) : Prop :=
  (∀ h i j,L (r h) i=true → R (r h) j=true → B i j=false) ∧
  ∀ h t,h≠t → ∃ i,(L (r h) i=true ∨ L (r t) i=true) ∧ (R (r h) i=true ∨ R (r t) i=true)
instance (B : Fin 3 → Fin 3 → Bool) : Decidable (SquareFree B) := by unfold SquareFree; infer_instance
instance (B : Fin 3 → Fin 3 → Bool) (r : Fin 5 → Nat) : Decidable (Good B r) := by unfold Good; infer_instance
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem certificate : ∀ a b c d e f : Bool, SquareFree (board a b c d e f) →
    Good (board a b c d e f) (rows a b c d e f) := by decide +kernel

theorem existence (B : Fin 3 → Fin 3 → Bool) (diag : ∀ i,B i i=true) (sf : SquareFree B) :
    ∃ r : Fin 5 → Nat,Good B r := by
  let T := board (B 0 1) (B 0 2) (B 1 0) (B 1 2) (B 2 0) (B 2 1)
  have eq : B=T := by
    funext i j
    fin_cases i <;> fin_cases j <;> first | rfl | apply diag
  rw [eq] at sf ⊢
  exact ⟨_,certificate _ _ _ _ _ _ sf⟩

end PEqualNP.Outside.L_meta_18593.Probes

namespace PEqualNP.Outside.L_meta_18593
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
theorem five_rows {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (four : NoFourCycle G)
    (a b : Fin 3 → Fin n) (ai : Function.Injective a) (bi : Function.Injective b)
    (aa : ∀ i j,¬G.Adj (a i) (a j)) (bb : ∀ i j,¬G.Adj (b i) (b j))
    (diag : ∀ i,G.Adj (a i) (b i)) :
    ∃ X : Fin 5 → Fin n → Bool,(∀ h,graphFun G ∅ (X h)=false) ∧
      ∀ h t,h≠t → ∃ i,(X h (a i)=true ∨ X t (a i)=true) ∧ (X h (b i)=true ∨ X t (b i)=true) := by
  classical
  let B (i j : Fin 3) := decide (G.Adj (a i) (b j))
  have sf : Probes.SquareFree B := by
    intro i j k l ij kl hik hjk hil
    change decide (G.Adj (a j) (b l))=false
    apply decide_eq_false
    intro jl
    apply kl
    apply bi
    exact Finset.card_le_one.mp (four _ _ (fun e => ij (ai e))) _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true hik,of_decide_eq_true hjk⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true hil,jl⟩)
  obtain ⟨r,good,joint⟩ := Probes.existence B (fun i => decide_eq_true (diag i)) sf
  let X (h : Fin 5) (v : Fin n) := decide ((∃ i,a i=v ∧ Probes.L (r h) i=true) ∨
    (∃ j,b j=v ∧ Probes.R (r h) j=true))
  refine ⟨X,?_,?_⟩
  · intro h
    apply Bool.eq_false_iff.mpr
    intro on
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
      decide_eq_true_eq] at on
    obtain ⟨u,v,uv,hu,hv⟩ := on
    have ax {u : Fin n} (z : X h u=true) := of_decide_eq_true z
    rcases ax hu with ⟨i,rfl,li⟩|⟨i,rfl,ri⟩ <;> rcases ax hv with ⟨j,rfl,lj⟩|⟨j,rfl,rj⟩
    · exact aa i j uv
    · have no := good h i j li rj
      exact (of_decide_eq_false no) uv
    · have no := good h j i lj ri
      exact (of_decide_eq_false no) uv.symm
    · exact bb i j uv
  · intro h t ht
    obtain ⟨i,left,right⟩ := joint h t ht
    have la (s : Fin 5) (v : Probes.L (r s) i=true) : X s (a i)=true :=
      decide_eq_true (Or.inl ⟨i,rfl,v⟩)
    have rb (s : Fin 5) (v : Probes.R (r s) i=true) : X s (b i)=true :=
      decide_eq_true (Or.inr ⟨i,rfl,v⟩)
    exact ⟨i,left.imp (la h) (la t),right.imp (rb h) (rb t)⟩

theorem no_joint_three {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (four : NoFourCycle G) (least : IsLeastAO G C) (form : TopForm G C) (count : (junk G C).card≤2)
    (a b : Fin 3 → Fin n) (ai : Function.Injective a) (bi : Function.Injective b)
    (aa : ∀ i j,¬G.Adj (a i) (a j)) (bb : ∀ i j,¬G.Adj (b i) (b j))
    (diag : ∀ i,G.Adj (a i) (b i))
    (allOn : ∀ i,∀ g∈junk G C,gateVal n C g (pairInput (a i) (b i))=true) :
    ∃ x : Fin n → Bool, graphFun G ∅ x=false ∧ ∀ g∈junk G C,gateVal n C g x=true := by
  classical
  obtain ⟨X,off,joins⟩ := five_rows G four a b ai bi aa bb diag
  by_contra none
  have fails (i : Fin 5) : ∃ j∈junk G C,gateVal n C j (X i)=false := by
    by_contra fail
    apply none
    refine ⟨X i,off i,?_⟩
    intro j hj
    cases z : gateVal n C j (X i) with
    | false => exact False.elim (fail ⟨j,hj,z⟩)
    | true => rfl
  have bound := Cut.cuts G C least.1 form X fails (by
    intro i t it
    obtain ⟨k,ak,bk⟩ := joins i t it
    exact ⟨a k,b k,ak,bk,allOn k⟩)
  omega
end PEqualNP.Outside.L_meta_18593

namespace PEqualNP.Outside.L_meta_18593
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge Finset

variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def DoubleRoute (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (u v : Fin n) : Prop :=
  ∃ a ∈ tops G C,∃ g ∈ junk G C,∃ h ∈ junk G C,g≠h ∧
    OrReaches n C (opnd C a 0) g ∧ OrReaches n C (opnd C a 1) h ∧
    gateVal n C g (pairInput u v)=true ∧ gateVal n C h (pairInput u v)=true

theorem double_sound {u v : Fin n} (ao : IsAO2 n C) (d : DoubleRoute G C u v)
    (x : Fin n → Bool) (on : ∀ g∈junk G C,gateVal n C g x=true) : graphFun G ∅ x=true := by
  obtain ⟨a,atop,g,hg,h,hh,_,rg,rh,_,_⟩ := d
  obtain ⟨bound,op,below⟩ := Donor.topData atop
  apply below x
  apply (Donor.andValBoth ao bound op x).mpr
  refine ⟨?_,?_⟩
  · exact Donor.orStep_up (n:=n) (C:=C) (by simp : (List.ofFn x).length=n)
      (Donor.orReaches_reach g _ rg).1 (on _ hg)
  · exact Donor.orStep_up (n:=n) (C:=C) (by simp : (List.ofFn x).length=n)
      (Donor.orReaches_reach h _ rh).1 (on _ hh)

theorem double_hits {u v : Fin n} (cnt : (junk G C).card≤2) (d : DoubleRoute G C u v) :
    ∀ z∈junk G C,gateVal n C z (pairInput u v)=true := by
  classical
  obtain ⟨a,_,g,hg,h,hh,ne,_,_,ag,ah⟩ := d
  have subset : ({g,h} : Finset Nat) ⊆ junk G C := by
    intro w hw
    rcases mem_insert.mp hw with eq|other
    · exact eq ▸ hg
    · exact (mem_singleton.mp other) ▸ hh
  have size : ({g,h} : Finset Nat).card=2 := by simp [ne]
  have exhaust : ({g,h} : Finset Nat)=junk G C :=
    eq_of_subset_of_card_le subset (by omega)
  intro z hz
  rw [←exhaust] at hz
  rcases mem_insert.mp hz with rfl | hmem
  · exact ag
  · exact (mem_singleton.mp hmem) ▸ ah

theorem missing_double (four : NoFourCycle G) (least : IsLeastAO G C) (form : TopForm G C)
    (count : (junk G C).card≤2) (a b : Fin 3 → Fin n) (ai : Function.Injective a) (bi : Function.Injective b)
    (aa : ∀ i j,¬G.Adj (a i) (a j)) (bb : ∀ i j,¬G.Adj (b i) (b j)) (diag : ∀ i,G.Adj (a i) (b i)) :
    ∃ i,¬DoubleRoute G C (a i) (b i) := by
  classical
  by_contra! every
  obtain ⟨x,off,on⟩ := no_joint_three G C four least form count a b ai bi aa bb diag
    (fun i => double_hits count (every i))
  have yes := double_sound least.1 (every 0) x on
  rw [off] at yes
  cases yes
end PEqualNP.Outside.L_meta_18593

namespace PEqualNP.Outside.L_meta_18593.Trace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
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

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma pairInput_comm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp only [pairInput, or_comm]

lemma sub_zero2 : (1 : Fin 2) - 0 = 1 := by decide

lemma sub_one2 : (1 : Fin 2) - 1 = 0 := by decide

end PEqualNP.Outside.L_meta_18593.Trace

theorem PEqualNP.Outside.L_meta_18593.Trace : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.Ustar x2 x4, (∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x12 : Fin (2 : ℕ)), ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x9 ∈ PEqualNP.TopForm.side x4 x11 x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x12 ≠ x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
  intro n G _ C hL hT e
  induction e using Sym2.ind with
  | _ u v =>
  intro huv
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
      (PEqualNP.EdgeOwnership.pairInput u v) = true → G.Adj u v :=
    fun u v h => (PEqualNP.Outside.L_meta_18593.Trace.graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, PEqualNP.Outside.L_meta_18593.Trace.val C (List.ofFn x) C.output =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    PEqualNP.Outside.L_meta_18593.Trace.edge_trace G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
      hF hout u v ((PEqualNP.Outside.L_meta_18593.Trace.graphFun_pair G u v).mpr hadj)
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op =
      PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases hAO _ (PEqualNP.Outside.L_meta_18593.Trace.gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : PEqualNP.TopForm.BelowF G C a := fun x hx =>
    PEqualNP.Outside.L_meta_18593.Trace.below_of_reach
      (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ PEqualNP.TopForm.tops G C := by
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (PEqualNP.Outside.L_meta_18593.Trace.gateAt_mem halen))
  have e0 : PEqualNP.TopForm.opnd C a 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C a 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  have hpq := (PEqualNP.Outside.L_meta_18593.Trace.val_and (n := n) (by simp) halen hop).mp hval
  have hpin : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hqin : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hp := hpq p hpin
  have hq := hpq q hqin
  have junk_of : ∀ (w : ℕ), w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs →
      w < n + a → ∀ h, h < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
      Relation.ReflTransGen (PEqualNP.Outside.L_meta_18593.Trace.OrStep n C) w (n + h) →
      h ∈ PEqualNP.TopForm.junk G C ∧ ¬ PEqualNP.TopForm.BelowF G C h ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w h := by
    intro w hwin hwlt h hh hhor hr
    have hhand : (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hAO _ (PEqualNP.Outside.L_meta_18593.Trace.gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : PEqualNP.EdgeOwnership.InCone n C h a :=
      PEqualNP.Outside.L_meta_18593.Trace.operand_cone halen hwin hwlt hr
    have hnb : ¬ PEqualNP.TopForm.BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C h := by
      unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ PEqualNP.TopForm.junk G C := by
      unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    exact ⟨hjunk, hnb, PEqualNP.Outside.L_meta_18593.Trace.reach_orReaches hr h rfl hh⟩
  rcases PEqualNP.Outside.L_meta_18593.Trace.operand_trace (C := C) u v p hp.2 with
    ⟨t1, ht1, hr1⟩ | ⟨h1, hh1, hhor1, hr1, hv1⟩
  · rcases PEqualNP.Outside.L_meta_18593.Trace.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        PEqualNP.Outside.L_meta_18593.Trace.side_adj G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
          hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
        Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [PEqualNP.TopForm.side, e0]
        exact PEqualNP.Outside.L_meta_18593.Trace.reach_mem_orIn t1 hr1
      · simp only [PEqualNP.TopForm.side, e1]
        exact PEqualNP.Outside.L_meta_18593.Trace.reach_mem_orIn t2 hr2
    · obtain ⟨hj, _, hor⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      left
      have hside : t1 ∈ PEqualNP.TopForm.side C a 0 := by
        simp only [PEqualNP.TopForm.side, e0]
        exact PEqualNP.Outside.L_meta_18593.Trace.reach_mem_orIn t1 hr1
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 0)) h2' := by
        rw [PEqualNP.Outside.L_meta_18593.Trace.sub_zero2, e1]; exact hor
      rcases ht1 with rfl | rfl
      · exact ⟨t1, v, rfl, a, hatop, 0, h2', hj, hside, hor', hv2⟩
      · refine ⟨t1, u, Sym2.eq_swap, a, hatop, 0, h2', hj, hside, hor', ?_⟩
        rw [PEqualNP.Outside.L_meta_18593.Trace.pairInput_comm]; exact hv2
  · obtain ⟨hj1, hnb1, hor1⟩ := junk_of p hpin hp.1 h1 hh1 hhor1 hr1
    rcases PEqualNP.Outside.L_meta_18593.Trace.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · left
      have hside : t2 ∈ PEqualNP.TopForm.side C a 1 := by
        simp only [PEqualNP.TopForm.side, e1]
        exact PEqualNP.Outside.L_meta_18593.Trace.reach_mem_orIn t2 hr2
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 1)) h1 := by
        rw [PEqualNP.Outside.L_meta_18593.Trace.sub_one2, e0]; exact hor1
      rcases ht2 with rfl | rfl
      · exact ⟨t2, v, rfl, a, hatop, 1, h1, hj1, hside, hor', hv1⟩
      · refine ⟨t2, u, Sym2.eq_swap, a, hatop, 1, h1, hj1, hside, hor', ?_⟩
        rw [PEqualNP.Outside.L_meta_18593.Trace.pairInput_comm]; exact hv1
    · obtain ⟨hj2, _, hor2⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      right
      refine ⟨u, v, rfl, a, hatop, h1, hj1, h2', hj2, ?_, ?_, ?_, hv1, hv2⟩
      · intro heq
        subst heq
        apply hnb1
        intro x hx
        apply hbel
        show PEqualNP.Outside.L_meta_18593.Trace.val C (List.ofFn x) (n + a) = true
        rw [PEqualNP.Outside.L_meta_18593.Trace.val_and (n := n) (by simp) halen hop, hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hp.1, PEqualNP.Outside.L_meta_18593.Trace.orStep_up (n := n) (by simp) hr1 hx⟩
        · exact ⟨hq.1, PEqualNP.Outside.L_meta_18593.Trace.orStep_up (n := n) (by simp) hr2 hx⟩
      · rw [e0]; exact hor1
      · rw [e1]; exact hor2

namespace PEqualNP.Outside.L_meta_18593
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge Finset
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem filter_at_top (ao : IsAO2 n C) {t j : Nat} {w : Fin n} {b : Fin 2} (top : t∈tops G C)
    (raw : w∈side C t b) (reach : OrReaches n C (opnd C t (1-b)) j) : w∈wmax G C j := by
  classical
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  intro x jon won
  obtain ⟨bound,op,below⟩ := Donor.topData top
  apply below x
  apply (Donor.andValOperands ao bound op x).mpr
  intro i
  have r := Donor.sideVal raw won
  have s := Donor.orStep_up (n:=n) (C:=C) (by simp : (List.ofFn x).length=n)
    (Donor.orReaches_reach j _ reach).1 jon
  have pair : i=b ∨ i=1-b := by fin_cases b <;> fin_cases i <;> decide
  rcases pair with rfl|rfl
  · exact r
  · exact s

theorem matched_filter (four : NoFourCycle G) (least : IsLeastAO G C) (form : TopForm G C)
    (count : (junk G C).card≤2) (a b : Fin 3 → Fin n) (ai : Function.Injective a) (bi : Function.Injective b)
    (aa : ∀ i j,¬G.Adj (a i) (a j)) (bb : ∀ i j,¬G.Adj (b i) (b j)) (diag : ∀ i,G.Adj (a i) (b i))
    (res : ∀ i,s(a i,b i)∈Ustar G C) :
    ∃ i,∃ g∈junk G C,gateVal n C g (pairInput (a i) (b i))=true ∧ (a i∈wmax G C g ∨ b i∈wmax G C g) := by
  classical
  obtain ⟨i,miss⟩ := missing_double four least form count a b ai bi aa bb diag
  rcases Trace n G C least form _ (res i) with
    ⟨u,v,eq,t,ht,d,g,hg,raw,reach,on⟩ | ⟨u,v,eq,t,ht,g,hg,h,hh,ne,rg,rh,og,oh⟩
  · have safe := filter_at_top least.1 ht raw reach
    rcases Sym2.eq_iff.mp eq with ⟨ha,hb⟩|⟨ha,hb⟩
    · subst u; subst v
      exact ⟨i,g,hg,on,Or.inl safe⟩
    · subst u; subst v
      rw [Trace.pairInput_comm] at on
      exact ⟨i,g,hg,on,Or.inr safe⟩
  · apply False.elim
    apply miss
    rcases Sym2.eq_iff.mp eq with ⟨ha,hb⟩|⟨ha,hb⟩
    · subst u; subst v
      exact ⟨t,ht,g,hg,h,hh,ne,rg,rh,og,oh⟩
    · subst u; subst v
      rw [Trace.pairInput_comm] at og oh
      exact ⟨t,ht,g,hg,h,hh,ne,rg,rh,og,oh⟩
end PEqualNP.Outside.L_meta_18593

namespace PEqualNP.Outside.L_meta_18593.Ledger
open Finset
variable {n : Nat}

def Meets (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop := ∃ v ∈ A,v∈e

open Classical in
noncomputable def hit (U : Finset (Sym2 (Fin n))) (A : Finset (Fin n)) :=
  U.filter (Meets A)

theorem hit_mem {U : Finset (Sym2 (Fin n))} {A : Finset (Fin n)} {e} :
    e∈hit U A ↔ e∈U ∧ Meets A e := by classical simp [hit]

theorem budget (U : Finset (Sym2 (Fin n))) (d : Nat)
    (res : ∀ A : Finset (Fin n), (∀ e∈U,Meets A e) → d < A.card+U.card)
    (A : Finset (Fin n)) : d + (hit U A).card < 2*U.card + A.card := by
  classical
  have existsEnd (e : Sym2 (Fin n)) : ∃ v,v∈e := by
    induction e using Sym2.ind with
    | h a b => exact ⟨a,by simp⟩
  let f (e : Sym2 (Fin n)) := (existsEnd e).choose
  let R := U \ hit U A
  have bound := res (A ∪ R.image f) (by
    intro e he
    by_cases h : e∈hit U A
    · obtain ⟨v,hv,ev⟩ := (hit_mem.mp h).2
      exact ⟨v,mem_union_left _ hv,ev⟩
    · exact ⟨f e,mem_union_right _ (mem_image_of_mem _ (mem_sdiff.mpr ⟨he,h⟩)),(existsEnd e).choose_spec⟩)
  have su : hit U A ⊆ U := fun _ h => (hit_mem.mp h).1
  have add : R.card + (hit U A).card=U.card := card_sdiff_add_card_eq_card su
  have uni := card_union_le A (R.image f)
  have im : (R.image f).card ≤ R.card := card_image_le
  omega

theorem boundary (U : Finset (Sym2 (Fin n))) (d : Nat)
    (res : ∀ A : Finset (Fin n), (∀ e∈U,Meets A e) → d < A.card+U.card)
    (tight : 2*U.card ≤ d+1) :
    ∀ e∈U,∀ f∈U,e≠f → ¬∃ v : Fin n,v∈e ∧ v∈f := by
  classical
  rintro e he f hf ne ⟨v,ve,vf⟩
  have a := budget U d res {v}
  simp only [card_singleton] at a
  have two : 1 < (hit U {v}).card := one_lt_card.mpr
    ⟨e,hit_mem.mpr ⟨he,v,mem_singleton_self _,ve⟩,f,hit_mem.mpr ⟨hf,v,mem_singleton_self _,vf⟩,ne⟩
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
theorem three (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j2 : 2≤(junk G C).card) (o1 : 1≤(orN G C \ lam G C).card)
    (k3 : 3≤(centreless G C).card+(orN G C \ lam G C).card)
    (d5 : 5≤2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card)
    (u3 : (Ustar G C).card=3)
    (res : ∀ A : Finset (Fin n), (∀ e∈Ustar G C,Meets A e) →
      2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card < A.card+(Ustar G C).card) :
    (junk G C).card=2 ∧ (centreless G C).card=0 ∧ (orN G C \ lam G C).card=3 ∧
    ∀ e∈Ustar G C,∀ f∈Ustar G C,e≠f → ¬∃ v : Fin n,v∈e ∧ v∈f := by
  have h := budget _ _ res ∅
  simp only [card_empty,Nat.add_zero,u3] at h
  refine ⟨by omega,by omega,by omega,boundary _ _ res (by omega)⟩
end PEqualNP.Outside.L_meta_18593.Ledger

namespace PEqualNP.Outside.L_meta_18593
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership Finset
variable {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem boundary_filter (bip : G.IsBipartite) (four : NoFourCycle G) (least : IsLeastAO G C) (form : TopForm G C)
    (j2 : 2≤(junk G C).card) (o1 : 1≤(orN G C \ lam G C).card)
    (k3 : 3≤(centreless G C).card+(orN G C \ lam G C).card)
    (d5 : 5≤2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card)
    (u3 : (Ustar G C).card=3)
    (res : ∀ A : Finset (Fin n), (∀ e∈Ustar G C,∃ v∈A,v∈e) →
      2*(centreless G C).card+(junk G C).card+(orN G C \ lam G C).card < A.card+(Ustar G C).card) :
    ∃ u v : Fin n,s(u,v)∈Ustar G C ∧ ∃ j∈junk G C,gateVal n C j (pairInput u v)=true ∧
      (u∈wmax G C j ∨ v∈wmax G C j) := by
  classical
  obtain ⟨cnt,_,_,apart⟩ := Ledger.three G C j2 o1 k3 d5 u3 res
  obtain ⟨f⟩ := bip
  let q : Fin 3 ≃ ↥(Ustar G C) := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using u3)).symm
  have orient (e : Sym2 (Fin n)) (he : e∈Ustar G C) :
      ∃ a b, e=s(a,b) ∧ f a=0 ∧ f b=1 ∧ G.Adj a b := by
    have he' : e∈G.edgeFinset := (mem_sdiff.mp he).1
    induction e using Sym2.ind with
    | h a b =>
      have edge := SimpleGraph.mem_edgeFinset.mp he'
      have neq := f.valid edge
      by_cases ha : (f a).val=0
      · have hb : (f b).val≠0 := fun z => neq (Fin.ext (ha.trans z.symm))
        exact ⟨a,b,rfl,Fin.ext ha,Fin.ext (by have := (f b).isLt; change (f b).val=1; omega),edge⟩
      · have ha1 : (f a).val=1 := by have := (f a).isLt; omega
        have hb : (f b).val=0 := by
          have bl := (f b).isLt
          by_contra nz
          exact neq (Fin.ext (by omega))
        exact ⟨b,a,Sym2.eq_swap,Fin.ext hb,Fin.ext ha1,edge.symm⟩
  have orients (i : Fin 3) := orient (q i).val (q i).property
  choose a b eq ca cb diag using orients
  have disj (i k : Fin 3) (ne : i≠k) : ¬∃ v : Fin n,v∈s(a i,b i) ∧ v∈s(a k,b k) := by
    rw [←eq i,←eq k]
    exact apart _ (q i).property _ (q k).property (fun h => ne (q.injective (Subtype.ext h)))
  have hi : Function.Injective a := by
    intro i k eq
    by_contra ne
    exact disj i k ne ⟨a i,by simp,by rw [eq]; simp⟩
  have hj : Function.Injective b := by
    intro i k eq
    by_contra ne
    exact disj i k ne ⟨b i,by simp,by rw [eq]; simp⟩
  have hres (i : Fin 3) : s(a i,b i)∈Ustar G C := eq i ▸ (q i).property
  obtain ⟨i,j,hj,on,safe⟩ := matched_filter four least form (by omega) a b hi hj
    (fun i k adj => f.valid adj ((ca i).trans (ca k).symm))
    (fun i k adj => f.valid adj ((cb i).trans (cb k).symm)) diag hres
  exact ⟨a i,b i,hres i,j,hj,on,safe⟩
end PEqualNP.Outside.L_meta_18593

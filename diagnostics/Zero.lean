import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1491

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


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
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
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
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
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

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

end S90
end PEqualNP.Outside.L_meta_1491
namespace EdgeBank4081

abbrev E := Sym2 (Fin 11)
abbrev Label := Finset (Fin 11) × Finset E
def allowed : List Label := [
  ({0},∅),
  ({1},∅),
  ({2},∅),
  ({3},∅),
  ({4},∅),
  ({5},∅),
  ({6},∅),
  ({7},∅),
  ({8},∅),
  ({9},∅),
  ({10},∅),
  ({9,10},{s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11))}),
  ({4,8},{s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11))}),
  ({5,10},{s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))}),
  ({6,7},{s((3 : Fin 11),(6 : Fin 11)),s((3 : Fin 11),(7 : Fin 11))}),
  ({1,8},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))}),
  ({1,10},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({8,10},{s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({1,8,10},{s((1 : Fin 11),(4 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({2,8},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({2,9},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({8,9},{s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({2,8,9},{s((2 : Fin 11),(5 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({3,7},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))}),
  ({3,10},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({7,10},{s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({3,7,10},{s((3 : Fin 11),(6 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({3,6},{s((3 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(7 : Fin 11))}),
  ({3,9},{s((3 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({6,9},{s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({3,6,9},{s((3 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({1,4},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11))}),
  ({1,5},{s((1 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({1,9},{s((1 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({4,5},{s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({4,9},{s((4 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,9},{s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,4,5},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11))}),
  ({1,4,9},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,5,9},{s((1 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({4,5,9},{s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({1,4,5,9},{s((1 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11))}),
  ({0,7},{s((0 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({0,8},{s((0 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,7},{s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({5,8},{s((5 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({7,8},{s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5,7},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11))}),
  ({0,5,8},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,7,8},{s((0 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({5,7,8},{s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,5,7,8},{s((0 : Fin 11),(9 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}),
  ({0,2},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11))}),
  ({0,4},{s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({0,6},{s((0 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({2,4},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({2,6},{s((2 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({4,6},{s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,2,4},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11))}),
  ({0,2,6},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,4,6},{s((0 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({2,4,6},{s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))}),
  ({0,2,4,6},{s((0 : Fin 11),(10 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((6 : Fin 11),(10 : Fin 11))})]
def allEdges : Finset E := {s((0 : Fin 11),(9 : Fin 11)),s((0 : Fin 11),(10 : Fin 11)),s((1 : Fin 11),(4 : Fin 11)),s((1 : Fin 11),(8 : Fin 11)),s((2 : Fin 11),(5 : Fin 11)),s((2 : Fin 11),(10 : Fin 11)),s((3 : Fin 11),(6 : Fin 11)),s((3 : Fin 11),(7 : Fin 11)),s((4 : Fin 11),(8 : Fin 11)),s((4 : Fin 11),(10 : Fin 11)),s((5 : Fin 11),(8 : Fin 11)),s((5 : Fin 11),(9 : Fin 11)),s((6 : Fin 11),(7 : Fin 11)),s((6 : Fin 11),(10 : Fin 11)),s((7 : Fin 11),(9 : Fin 11)),s((8 : Fin 11),(9 : Fin 11))}

def hits (A : Finset (Fin 11)) (e : E) : Prop := ∃ v∈A, v∈e
instance (A : Finset (Fin 11)) (e : E) : Decidable (hits A e) := by unfold hits;infer_instance
end EdgeBank4081
namespace EdgeBank4081

def anchored (U : Finset E) (A : Finset (Fin 11)) : Prop :=
  A.card ≤ 1 ∨ ∃ c : Fin 11, ∀ x ∈ A, s(c,x)∈allEdges ∧ s(c,x)∉U

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem supported : ∀ c : Fin 11, ∀ A∈(Finset.univ.filter (fun x : Fin 11 => s(c,x)∈allEdges)).powerset,
    2 ≤ A.card → (A,A.image (fun x => s(c,x)))∈allowed := by decide +kernel

theorem choose_label (U : Finset E) (A : Finset (Fin 11)) (ne : A.Nonempty) (sat : anchored U A) :
    ∃ a∈allowed, a.1=A ∧ Disjoint a.2 U := by
  classical
  by_cases low : A.card ≤ 1
  · obtain ⟨x,hx⟩ := Finset.card_eq_one.mp (by have := Finset.card_pos.mpr ne;omega : A.card=1)
    subst A
    have raw : ∀ x : Fin 11, (({x} : Finset (Fin 11)),(∅ : Finset E))∈allowed := by decide +kernel
    exact ⟨_,raw x,rfl,by simp⟩
  · obtain ⟨c,cn⟩ := sat.resolve_left low
    have coverage : A⊆Finset.univ.filter (fun x : Fin 11 => s(c,x)∈allEdges) := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(cn x hx).1⟩
    refine ⟨_,supported c A (Finset.mem_powerset.mpr coverage) (by omega),rfl,?_⟩
    apply Finset.disjoint_left.mpr
    rintro e he hU
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    exact (cn x hx).2 hU

end EdgeBank4081
namespace Good4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership EdgeBank4081

abbrev graph := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
end Good4081
namespace Paid4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1491
lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)



theorem cross {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) (free : NoFourCycle G) (a : ℕ) (ha : a∈tops G C)
    (u v : Fin n) (hu : u∈side (n:=n) C a 0) (hv : v∈side (n:=n) C a 1) :
    s(u,v)∈G.edgeFinset ∧ s(u,v)∉Ustar G C := by
  have adj := (S90.top_facts G C free least a ha).2.1 u hu v hv
  have inside : s(u,v)∈starEdges G C := Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨(u,v),Finset.mem_product.mpr ⟨hu,hv⟩,rfl⟩⟩
  exact ⟨SimpleGraph.mem_edgeFinset.mpr adj,fun h => (Finset.mem_sdiff.mp h).2 inside⟩

theorem lambda_anchor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (least : IsLeastAO G C) (free : NoFourCycle G) (h : ℕ) (lamh : h∈lam G C) :
    ∃ c : Fin n, ∀ x∈orIn n C (n+h), s(c,x)∈G.edgeFinset ∧ s(c,x)∉Ustar G C := by
  obtain ⟨_,_,_,a,ha,b,sing,reach⟩ := Finset.mem_filter.mp lamh
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp sing
  have base : c∈side (n:=n) C a (1-b) := by rw [hc];simp
  refine ⟨c,?_⟩
  intro x hx
  have inleaf : x∈side (n:=n) C a b :=
    S90.reach_mem_orIn x ((S90.orReaches_reach h _ reach).1.trans (S90.mem_orIn_reach x hx))
  fin_cases b
  · change c∈side (n:=n) C a 1 at base
    have swap : s(c,x)=s(x,c) := Sym2.eq_swap
    rw [swap]
    exact cross G C least free a ha x c inleaf base
  · change c∈side (n:=n) C a 0 at base
    exact cross G C least free a ha c x base inleaf

end Paid4081
namespace Pure4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1491.S90

theorem dirty_or {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (j : ℕ) (ne : (orIn n C (n+j)).Nonempty) : j∈orN G C := by
  obtain ⟨x,hx⟩ := ne
  obtain ⟨jl,op,_⟩ := (Paid4081.orIn_gate C j x).mp hx
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr jl,op,?_⟩
  intro below
  have on := reach_var_val (pairInput x x) (n+j) x (mem_orIn_reach x hx) ((pairInput_true x x x).mpr (Or.inl rfl))
  exact G.loopless x ((graphFun_pair G x x).mp (below _ on))

theorem pure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (no : orN G C \ lam G C = ∅) (x : Fin n → Bool) (w : ℕ) (ne : (orIn n C w).Nonempty)
    (on : val C (List.ofFn x) w=true) : ∃ u∈orIn n C w, x u=true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases low : w < n
    · let u : Fin n := ⟨w,low⟩
      exact ⟨u,reach_mem_orIn u .refl,(val_ofFn C x u).symm.trans on⟩
    · obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
      have member := dirty_or G C j ne
      have inL : j∈lam G C := by
        by_contra bad
        have inside := Finset.mem_sdiff.mpr ⟨member,bad⟩
        rw [no] at inside
        exact Finset.notMem_empty _ inside
      obtain ⟨_,pre0,pre1,_⟩ := Finset.mem_filter.mp inL
      obtain ⟨jl,op,_⟩ := Finset.mem_filter.mp member
      have real := Finset.mem_range.mp jl
      obtain ⟨t,mem,before,value⟩ := (val_or (n:=n) (by simp) real op).mp on
      obtain ⟨a,b,ins⟩ := List.length_eq_two.mp (ao.2.2 _ (gateAt_mem real))
      have proper : (orIn n C t).Nonempty := by
        rw [ins] at mem
        simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
        rcases mem with rfl|rfl
        · simpa [opnd,ins] using pre0
        · simpa [opnd,ins] using pre1
      obtain ⟨u,hu,tru⟩ := ih t before proper value
      exact ⟨u,(Paid4081.orIn_gate C j u).mpr ⟨real,op,t,mem,before,hu⟩,tru⟩

theorem live_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (ao : IsAO2 n C)
    (top : TopForm G C) (a j : ℕ) (al : a < C.gates.length) (opa : (gateAt C a).op=.and)
    (input : n+j∈(gateAt C a).inputs) (u v : Fin n) (on : gateVal n C j (pairInput u v)=true) : ¬BelowF G C j := by
  intro below
  rcases operand_trace (C:=C) u v (n+j) on with ⟨t,_,path⟩|⟨h,hl,notOr,path,_⟩
  · have val := reach_var_val (pairInput t t) _ t path ((pairInput_true t t t).mpr (Or.inl rfl))
    exact G.loopless t ((graphFun_pair G t t).mp (below _ val))
  · have op := (ao.1 _ (gateAt_mem hl)).resolve_right notOr
    have safe : BelowF G C h := by
      intro x hv;apply below x
      exact orStep_up (n:=n) (by simp) path hv
    exact top h hl a al op safe opa (operand_cone al input (ao.2.1 a al _ input) path)

end Pure4081
namespace Triple4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership EdgeBank4081

def independent (Z : Finset (Fin 11)) := ∀ u∈Z, ∀ v∈Z, s(u,v)∉allEdges
instance (Z : Finset (Fin 11)) : Decidable (independent Z) := by unfold independent;infer_instance

def tests : List (Finset (Fin 11)) := [{0,1,2,3},{0,2,3,4},{0,1,3,5},{0,3,4,5},{0,1,2,6},{0,2,4,6},{0,1,5,6},{0,4,5,6},{0,1,2,7},{0,2,4,7},{0,1,5,7},{0,4,5,7},{0,2,3,8},{0,2,6,8},{0,2,7,8},{1,2,3,9},{2,3,4,9},{1,2,6,9},{2,4,6,9},{1,3,5,10},{1,5,7,10},{3,8,10},{7,8,10},{1,3,9,10}]
end Triple4081
namespace Pair5184
open EdgeBank4081 Triple4081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def distinguished : Finset E := {s(9,0),s(8,1),s(2,5),s(3,7),s(10,6)}
def pairs : Finset (Finset E) := {{s((0 : Fin 11),10),s((5 : Fin 11),8)},{s((1 : Fin 11),4),s((5 : Fin 11),9)},{s((2 : Fin 11),10),s((8 : Fin 11),9)},{s((4 : Fin 11),10),s((5 : Fin 11),9)}}
def z0 : Finset (Fin 11) := {7,8,10}
def cls0 : Finset (Finset E) := {{s((0 : Fin 11),9),s((1 : Fin 11),8)},{s((0 : Fin 11),9),s((3 : Fin 11),7)},{s((0 : Fin 11),9),s((5 : Fin 11),8)},{s((0 : Fin 11),10),s((1 : Fin 11),4)},{s((0 : Fin 11),10),s((1 : Fin 11),8)},{s((0 : Fin 11),10),s((2 : Fin 11),10)},{s((0 : Fin 11),10),s((3 : Fin 11),6)},{s((0 : Fin 11),10),s((3 : Fin 11),7)},{s((0 : Fin 11),10),s((4 : Fin 11),8)},{s((0 : Fin 11),10),s((4 : Fin 11),10)},{s((0 : Fin 11),10),s((5 : Fin 11),9)},{s((0 : Fin 11),10),s((6 : Fin 11),7)},{s((0 : Fin 11),10),s((6 : Fin 11),10)},{s((0 : Fin 11),10),s((7 : Fin 11),9)},{s((0 : Fin 11),10),s((8 : Fin 11),9)},{s((1 : Fin 11),4),s((2 : Fin 11),10)},{s((1 : Fin 11),4),s((3 : Fin 11),7)},{s((1 : Fin 11),4),s((5 : Fin 11),8)},{s((1 : Fin 11),4),s((6 : Fin 11),10)},{s((1 : Fin 11),4),s((8 : Fin 11),9)},{s((1 : Fin 11),8),s((2 : Fin 11),5)},{s((1 : Fin 11),8),s((2 : Fin 11),10)},{s((1 : Fin 11),8),s((3 : Fin 11),6)},{s((1 : Fin 11),8),s((3 : Fin 11),7)},{s((1 : Fin 11),8),s((4 : Fin 11),8)},{s((1 : Fin 11),8),s((4 : Fin 11),10)},{s((1 : Fin 11),8),s((5 : Fin 11),8)},{s((1 : Fin 11),8),s((5 : Fin 11),9)},{s((1 : Fin 11),8),s((6 : Fin 11),7)},{s((1 : Fin 11),8),s((6 : Fin 11),10)},{s((1 : Fin 11),8),s((7 : Fin 11),9)},{s((1 : Fin 11),8),s((8 : Fin 11),9)},{s((2 : Fin 11),5),s((3 : Fin 11),7)},{s((2 : Fin 11),5),s((6 : Fin 11),10)},{s((2 : Fin 11),5),s((8 : Fin 11),9)},{s((2 : Fin 11),10),s((3 : Fin 11),6)},{s((2 : Fin 11),10),s((3 : Fin 11),7)},{s((2 : Fin 11),10),s((4 : Fin 11),8)},{s((2 : Fin 11),10),s((4 : Fin 11),10)},{s((2 : Fin 11),10),s((5 : Fin 11),8)},{s((2 : Fin 11),10),s((5 : Fin 11),9)},{s((2 : Fin 11),10),s((6 : Fin 11),7)},{s((2 : Fin 11),10),s((6 : Fin 11),10)},{s((3 : Fin 11),6),s((4 : Fin 11),10)},{s((3 : Fin 11),6),s((5 : Fin 11),8)},{s((3 : Fin 11),6),s((7 : Fin 11),9)},{s((3 : Fin 11),7),s((4 : Fin 11),8)},{s((3 : Fin 11),7),s((4 : Fin 11),10)},{s((3 : Fin 11),7),s((5 : Fin 11),8)},{s((3 : Fin 11),7),s((5 : Fin 11),9)},{s((3 : Fin 11),7),s((6 : Fin 11),7)},{s((3 : Fin 11),7),s((6 : Fin 11),10)},{s((3 : Fin 11),7),s((7 : Fin 11),9)},{s((3 : Fin 11),7),s((8 : Fin 11),9)},{s((4 : Fin 11),8),s((5 : Fin 11),8)},{s((4 : Fin 11),8),s((5 : Fin 11),9)},{s((4 : Fin 11),8),s((6 : Fin 11),10)},{s((4 : Fin 11),8),s((7 : Fin 11),9)},{s((4 : Fin 11),8),s((8 : Fin 11),9)},{s((4 : Fin 11),10),s((5 : Fin 11),8)},{s((4 : Fin 11),10),s((6 : Fin 11),7)},{s((4 : Fin 11),10),s((6 : Fin 11),10)},{s((4 : Fin 11),10),s((8 : Fin 11),9)},{s((5 : Fin 11),8),s((6 : Fin 11),7)},{s((5 : Fin 11),8),s((6 : Fin 11),10)},{s((5 : Fin 11),8),s((7 : Fin 11),9)},{s((5 : Fin 11),8),s((8 : Fin 11),9)},{s((5 : Fin 11),9),s((6 : Fin 11),7)},{s((6 : Fin 11),7),s((7 : Fin 11),9)},{s((6 : Fin 11),7),s((8 : Fin 11),9)},{s((6 : Fin 11),10),s((7 : Fin 11),9)}}
def z1 : Finset (Fin 11) := {2,4,6,9}
def cls1 : Finset (Finset E) := {{s((0 : Fin 11),9),s((1 : Fin 11),4)},{s((0 : Fin 11),9),s((2 : Fin 11),5)},{s((0 : Fin 11),9),s((2 : Fin 11),10)},{s((0 : Fin 11),9),s((3 : Fin 11),6)},{s((0 : Fin 11),9),s((4 : Fin 11),8)},{s((0 : Fin 11),9),s((4 : Fin 11),10)},{s((0 : Fin 11),9),s((5 : Fin 11),9)},{s((0 : Fin 11),9),s((6 : Fin 11),7)},{s((0 : Fin 11),9),s((6 : Fin 11),10)},{s((0 : Fin 11),9),s((7 : Fin 11),9)},{s((0 : Fin 11),9),s((8 : Fin 11),9)},{s((1 : Fin 11),4),s((3 : Fin 11),6)},{s((1 : Fin 11),4),s((4 : Fin 11),8)},{s((1 : Fin 11),4),s((4 : Fin 11),10)},{s((1 : Fin 11),4),s((6 : Fin 11),7)},{s((1 : Fin 11),4),s((7 : Fin 11),9)},{s((2 : Fin 11),5),s((2 : Fin 11),10)},{s((2 : Fin 11),5),s((3 : Fin 11),6)},{s((2 : Fin 11),5),s((4 : Fin 11),10)},{s((2 : Fin 11),5),s((7 : Fin 11),9)},{s((3 : Fin 11),6),s((4 : Fin 11),8)},{s((3 : Fin 11),6),s((5 : Fin 11),9)},{s((3 : Fin 11),6),s((6 : Fin 11),7)},{s((3 : Fin 11),6),s((6 : Fin 11),10)},{s((3 : Fin 11),6),s((8 : Fin 11),9)},{s((4 : Fin 11),8),s((4 : Fin 11),10)},{s((5 : Fin 11),9),s((7 : Fin 11),9)},{s((5 : Fin 11),9),s((8 : Fin 11),9)},{s((6 : Fin 11),7),s((6 : Fin 11),10)},{s((7 : Fin 11),9),s((8 : Fin 11),9)}}
def z2 : Finset (Fin 11) := {0,4,5,7}
def cls2 : Finset (Finset E) := {{s((0 : Fin 11),9),s((0 : Fin 11),10)},{s((0 : Fin 11),10),s((2 : Fin 11),5)},{s((1 : Fin 11),4),s((2 : Fin 11),5)},{s((2 : Fin 11),5),s((4 : Fin 11),8)},{s((2 : Fin 11),5),s((5 : Fin 11),8)},{s((2 : Fin 11),5),s((5 : Fin 11),9)},{s((4 : Fin 11),8),s((6 : Fin 11),7)},{s((5 : Fin 11),8),s((5 : Fin 11),9)}}
def z3 : Finset (Fin 11) := {1,3,9,10}
def cls3 : Finset (Finset E) := {{s((1 : Fin 11),4),s((1 : Fin 11),8)},{s((2 : Fin 11),10),s((7 : Fin 11),9)},{s((3 : Fin 11),6),s((3 : Fin 11),7)},{s((4 : Fin 11),10),s((7 : Fin 11),9)},{s((5 : Fin 11),9),s((6 : Fin 11),10)},{s((6 : Fin 11),10),s((8 : Fin 11),9)}}
def z4 : Finset (Fin 11) := {0,2,7,8}
def cls4 : Finset (Finset E) := {{s((2 : Fin 11),5),s((6 : Fin 11),7)}}
abbrev Row := Finset (Fin 11) × Finset (Finset E)
def good (g : Row) : Prop := independent g.1 ∧ ∀ F∈g.2, ∀ t∈allowed, Disjoint t.2 F → (∀e∈F, hits t.1 e) → ¬Disjoint t.1 g.1
instance (g : Row) : Decidable (good g) := by unfold good; infer_instance
theorem good0 : good (z0,cls0) := by decide +kernel
theorem good1 : good (z1,cls1) := by decide +kernel
theorem good2 : good (z2,cls2) := by decide +kernel
theorem good3 : good (z3,cls3) := by decide +kernel
theorem good4 : good (z4,cls4) := by decide +kernel
def rows : List Row := [(z0,cls0),(z1,cls1),(z2,cls2),(z3,cls3),(z4,cls4)]
theorem good_rows (g : Row) (h : g∈rows) : good g := by
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl
  · exact good0
  · exact good1
  · exact good2
  · exact good3
  · exact good4
theorem classify : ∀ d∈allEdges, ∀ e∈allEdges, d≠e → ({d,e} : Finset E)∈pairs ∨ ∃ g∈rows, ({d,e} : Finset E)∈g.2 := by decide +kernel
theorem separated : ∀ d∈allEdges, ∀ e∈allEdges, ({d,e} : Finset E)∈pairs → d∉distinguished ∧ e∉distinguished := by decide +kernel
theorem triangle : ∀ d∈allEdges, ∀ e∈allEdges, ∀ f∈allEdges, ({d,e} : Finset E)∈pairs → ({e,f} : Finset E)∈pairs → ({d,f} : Finset E)∉pairs := by decide +kernel
end Pair5184
namespace Zero4081
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_1491.S90
open EdgeBank4081 Good4081

def hot (C : Circuit) (W : Finset E) (w : ℕ) :=
  ∀ u v : Fin 11, s(u,v)∈W → val C (List.ofFn (pairInput u v)) w=true

theorem clause (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    (no : orN graph C \ lam graph C=∅) (T : Finset E) (nonempty : T.Nonempty)
    (Z : Finset (Fin 11)) (a : ℕ) (al : a < C.gates.length) (andA : (gateAt C a).op=.and)
    (high : hot C T (11+a)) (low : gateVal 11 C a (fun i => decide (i∈Z))=false) :
    ∃ tag∈allowed, Disjoint tag.2 (Ustar graph C) ∧ (∀ e∈T, hits tag.1 e) ∧ Disjoint tag.1 Z := by
  classical
  let x : Fin 11 → Bool := fun i => decide (i∈Z)
  have free : NoFourCycle graph := by decide +kernel
  have table : graph.edgeFinset=allEdges := by decide +kernel
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have child : ∃ w∈(gateAt C a).inputs, val C (List.ofFn x) w=false := by
      by_contra! wrong
      have tt := (val_and (n:=11) (x:=List.ofFn x) (by simp) al andA).mpr (fun w hw =>
        ⟨least.1.2.1 a al w hw,Bool.eq_true_of_not_eq_false (wrong w hw)⟩)
      exact Bool.noConfusion (low.symm.trans tt)
    obtain ⟨w,hw,zw⟩ := child
    have before := least.1.2.1 a al w hw
    have hotw : hot C T w := fun p l e => ((val_and (n:=11) (by simp) al andA).mp (high p l e) w hw).2
    have raw (ne : (orIn 11 C w).Nonempty) (sat : anchored (Ustar graph C) (orIn 11 C w)) :
        ∃ tag∈allowed, Disjoint tag.2 (Ustar graph C) ∧ (∀ e∈T, hits tag.1 e) ∧ Disjoint tag.1 Z := by
      obtain ⟨tag,can,eq,openU⟩ := choose_label _ _ ne sat
      refine ⟨tag,can,openU,?_,?_⟩
      · intro e he
        obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
        obtain ⟨s,ss,atPair⟩ := Pure4081.pure graph C least.1 no (pairInput u v) w ne (hotw u v he)
        exact ⟨s,eq.symm ▸ ss,Sym2.mem_iff.mpr ((pairInput_true u v s).mp atPair)⟩
      · rw [eq]
        apply Finset.disjoint_left.mpr
        intro t inS inZ
        have all := reach_var_val x w t (mem_orIn_reach t inS) (decide_eq_true inZ)
        exact Bool.noConfusion (zw.symm.trans all)
    by_cases small : w < 11
    · exact raw ⟨⟨w,small⟩,reach_mem_orIn ⟨w,small⟩ .refl⟩ (Or.inl (Paid4081.orIn_input C w small))
    · obtain ⟨j,rfl⟩ : ∃ j, w=11+j := ⟨w-11,by omega⟩
      have jl : j < C.gates.length := by omega
      rcases least.1.1 _ (gateAt_mem jl) with isAnd|isOr
      · exact ih j (by omega) jl isAnd hotw zw
      · obtain ⟨e,he⟩ := nonempty
        obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
        have junk := Pure4081.live_input graph C least.1 top a j al andA hw u v (hotw u v he)
        have mem : j∈orN graph C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr jl,isOr,junk⟩
        have inL : j∈lam graph C := by
          by_contra noL
          have m := Finset.mem_sdiff.mpr ⟨mem,noL⟩
          rw [no] at m
          exact Finset.notMem_empty _ m
        obtain ⟨_,has,_,_⟩ := Finset.mem_filter.mp inL
        obtain ⟨t,ht⟩ := has
        obtain ⟨i,k,eq⟩ := List.length_eq_two.mp (least.1.2.2 _ (gateAt_mem jl))
        have memi : opnd C j 0∈(gateAt C j).inputs := by simp [opnd,eq]
        have ne : (orIn 11 C (11+j)).Nonempty := ⟨t,(Paid4081.orIn_gate C j t).mpr ⟨jl,isOr,_,memi,least.1.2.1 j jl _ memi,ht⟩⟩
        obtain ⟨c,H⟩ := Paid4081.lambda_anchor graph C least free j inL
        exact raw ne (Or.inr ⟨c,fun r hr => ⟨table ▸ (H r hr).1,(H r hr).2⟩⟩)

def won (C : Circuit) (j : ℕ) : Finset E := Ustar graph C ∩ gammaE graph C j
theorem price (F : Finset E) (sub : F⊆allEdges)
    (separate : ∀ Z : Finset (Fin 11), Triple4081.independent Z → F.Nonempty →
      ∃ t∈allowed, Disjoint t.2 F ∧ (∀ e∈F,hits t.1 e) ∧ Disjoint t.1 Z) :
    F.card + (F∩Pair5184.distinguished).card ≤ 2 := by
  classical
  have share (d e : E) (hd : d∈F) (he : e∈F) (ne : d≠e) :
      ({d,e} : Finset E)∈Pair5184.pairs := by
    rcases Pair5184.classify d (sub hd) e (sub he) ne with ok|⟨g,gr,hm⟩
    · exact ok
    obtain ⟨neg,block⟩ := Pair5184.good_rows g gr
    obtain ⟨t,ht,dis,hot,sep⟩ := separate g.1 neg ⟨d,hd⟩
    have incl : ({d,e} : Finset E) ⊆ F := by simp [hd,he]
    exact False.elim (block _ hm t ht (Finset.disjoint_left.mpr (fun x hx h => Finset.disjoint_left.mp dis hx (incl h))) (fun x hx => hot x (incl hx)) sep)
  by_cases small : F.card ≤ 1
  · have le := Finset.card_le_card (Finset.inter_subset_left (s₁:=F) (s₂:=Pair5184.distinguished))
    omega
  obtain ⟨d,hd,e,he,ne⟩ := Finset.one_lt_card.mp (by omega : 1 < F.card)
  have pair := share d e hd he ne
  have eqF : F = {d,e} := by
    apply Finset.Subset.antisymm
    · intro f hf
      by_contra h
      have neq : f≠d ∧ f≠e := by simpa using h
      exact Pair5184.triangle d (sub hd) e (sub he) f (sub hf) pair
        (share e f he hf neq.2.symm) (share d f hd hf neq.1.symm)
    · simp [hd,he]
  obtain ⟨dm,em⟩ := Pair5184.separated d (sub hd) e (sub he) pair
  have disj : F∩Pair5184.distinguished=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨hF,hM⟩ := Finset.mem_inter.mp hf
    rw [eqF,Finset.mem_insert,Finset.mem_singleton] at hF
    rcases hF with rfl|rfl
    · exact dm hM
    · exact em hM
  rw [disj,eqF,Finset.card_pair ne]
  decide
theorem top_bound (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    (no : orN graph C \ lam graph C=∅) (j : ℕ) (hj : j∈tops graph C) : (won C j).card + (won C j ∩ Pair5184.distinguished).card ≤ 2 := by
  classical
  have table : graph.edgeFinset=allEdges := by decide +kernel
  have sub : won C j⊆Ustar graph C := Finset.inter_subset_left
  apply price _ (fun e he => table ▸ (Finset.mem_sdiff.mp (sub he)).1)
  intro Z ind nonempty
  have zero : graphFun graph ∅ (fun r => decide (r∈Z))=false := by
    cases h : graphFun graph ∅ (fun r => decide (r∈Z)) with
    | false => rfl
    | true =>
      have z : ∃ u v, graph.Adj u v ∧ u∈Z ∧ v∈Z := by simpa [graphFun] using h
      obtain ⟨u,v,edge,hu,hv⟩ := z
      exact False.elim (ind u hu v hv (table ▸ SimpleGraph.mem_edgeFinset.mpr edge))
  obtain ⟨jl,op,clean⟩ := Finset.mem_filter.mp hj
  have off : gateVal 11 C j (fun r => decide (r∈Z))=false := by
    cases h : gateVal 11 C j (fun r => decide (r∈Z)) with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (zero.symm.trans (clean _ h)))
  have hotj : hot C (won C j) (11+j) := by
    intro u v mem
    obtain ⟨_,p,l,eq,fire⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp mem).2
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact fire
    · have swap : pairInput u v=pairInput v u := by funext i; simp [pairInput,or_comm]
      simpa only [swap] using fire
  obtain ⟨a,valid,base,active,blocked⟩ := clause C least top no _ nonempty Z j (Finset.mem_range.mp jl) op hotj off
  exact ⟨a,valid,Finset.disjoint_left.mpr (fun e ha hw => Finset.disjoint_left.mp base ha (sub hw)),active,blocked⟩
theorem all (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C)
    (no : orN graph C \ lam graph C=∅) : (Ustar graph C).card + (Ustar graph C ∩ Pair5184.distinguished).card ≤ 2*(centreless graph C).card := by
  classical
  have free : NoFourCycle graph := by decide +kernel
  have covered : Ustar graph C⊆(centreless graph C).biUnion (won C) := by
    intro e he
    obtain ⟨⟨u,v⟩,rfl⟩ := e.exists_rep
    obtain ⟨a,ha,b,j,junk,fire,_,_⟩ := off_star graph C least top u v he
    have member : s(u,v)∈won C a :=
      Finset.mem_inter.mpr ⟨he,Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp he).1,u,v,rfl,fire⟩⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,member⟩
    by_contra! full
    obtain ⟨idx,op,_⟩ := Finset.mem_filter.mp ha
    have len := Finset.mem_range.mp idx
    obtain ⟨w,z,eq⟩ := List.length_eq_two.mp (least.1.2.2 _ (gateAt_mem len))
    have meet (k : Fin 2) (notempty : side (n:=11) C a k ≠ ∅) :
        u∈side (n:=11) C a k ∨ v∈side (n:=11) C a k := by
      have mem : opnd C a k∈(gateAt C a).inputs := by fin_cases k <;> simp [opnd,eq]
      have hot := ((val_and (n:=11) (by simp) len op).mp fire _ mem).2
      obtain ⟨x,back,valx⟩ := Pure4081.pure graph C least.1 no _ _ (Finset.nonempty_iff_ne_empty.mpr notempty) hot
      rcases (pairInput_true u v x).mp valx with rfl|rfl
      · exact Or.inl back
      · exact Or.inr back
    have dis := (top_facts graph C free least a ha).1
    have add (x y : Fin 11) (xx : x∈side (n:=11) C a 0) (yy : y∈side (n:=11) C a 1) :
        s(x,y)∈starEdges graph C := Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨xx,yy⟩,rfl⟩⟩
    have miss := (Finset.mem_sdiff.mp he).2
    rcases meet 0 full.1 with u0|v0 <;> rcases meet 1 full.2 with u1|v1
    · exact Finset.disjoint_left.mp dis u0 u1
    · exact miss (add _ _ u0 v1)
    · exact miss (by rw [Sym2.eq_swap];exact add _ _ v0 u1)
    · exact Finset.disjoint_left.mp dis v0 v1
  have coveredM : Ustar graph C∩Pair5184.distinguished ⊆
      (centreless graph C).biUnion (fun j => won C j∩Pair5184.distinguished) := by
    intro e he
    obtain ⟨hu,hm⟩ := Finset.mem_inter.mp he
    obtain ⟨j,hj,hw⟩ := Finset.mem_biUnion.mp (covered hu)
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨hw,hm⟩⟩
  have h1 := (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have h2 := (Finset.card_le_card coveredM).trans Finset.card_biUnion_le
  calc
    _ ≤ (∑ j∈centreless graph C,(won C j).card) + ∑ j∈centreless graph C,(won C j∩Pair5184.distinguished).card := Nat.add_le_add h1 h2
    _ = ∑ j∈centreless graph C,((won C j).card + (won C j∩Pair5184.distinguished).card) := Finset.sum_add_distrib.symm
    _ ≤ ∑ _j∈centreless graph C,2 := Finset.sum_le_sum (fun j hj => top_bound C least top no j (Finset.mem_filter.mp hj).1)
    _ = _ := by simp [Nat.mul_comm]

end Zero4081

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
theorem zero5184 : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 (([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).map (fun z => (z/11,z % 11))) →
      IsLeastAO G C → TopForm G C →
      orN G C \ lam G C = ∅ →
      let M : Finset (Sym2 (Fin 11)) := {s(9,0),s(8,1),s(2,5),s(3,7),s(10,6)}
      (Ustar G C).card + (Ustar G C ∩ M).card ≤ 2 * (centreless G C).card := by
  intro G inst C hg hmin ht hzero
  have eqG : G = Good4081.graph := hg
  subst G
  exact Zero4081.all C hmin ht hzero

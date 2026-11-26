import PEqualNP.Defs

-- The top-gate traces, operand semantics and forcing lemmas follow L_meta_5242,
-- including its proof from L_meta_1766. The support proof follows L_meta_2074
-- by willakone. The short walk excluding two common neighbors follows R_meta_1882_1.
namespace Junk1735.Base

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

theorem edge_witness : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∀ x7 ∈ PEqualNP.TopForm.Ustar x2 x4, (∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ (x12 : Fin (2 : ℕ)), ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x9 ∈ PEqualNP.TopForm.side x4 x11 x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 ((1 : Fin (2 : ℕ)) - x12)) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) ∨ ∃ (x9 : Fin x1) (x10 : Fin x1), x7 = s(x9, x10) ∧ ∃ x11 ∈ PEqualNP.TopForm.tops x2 x4, ∃ x12 ∈ PEqualNP.TopForm.junk x2 x4, ∃ x13 ∈ PEqualNP.TopForm.junk x2 x4, x12 ≠ x13 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (0 : Fin (2 : ℕ))) x12 ∧ PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x11 (1 : Fin (2 : ℕ))) x13 ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x12 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x13 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true := by
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
    fun u v h => (Junk1735.Base.graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, Junk1735.Base.val C (List.ofFn x) C.output =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    Junk1735.Base.edge_trace G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
      hF hout u v ((Junk1735.Base.graphFun_pair G u v).mpr hadj)
  have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op =
      PEqualNP.CircuitLowerBounds.GateOp.and := by
    rcases hAO _ (Junk1735.Base.gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : PEqualNP.TopForm.BelowF G C a := fun x hx =>
    Junk1735.Base.below_of_reach
      (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ PEqualNP.TopForm.tops G C := by
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (Junk1735.Base.gateAt_mem halen))
  have e0 : PEqualNP.TopForm.opnd C a 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C a 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  have hpq := (Junk1735.Base.val_and (n := n) (by simp) halen hop).mp hval
  have hpin : p ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hqin : q ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs := by rw [hin]; simp
  have hp := hpq p hpin
  have hq := hpq q hqin
  have junk_of : ∀ (w : ℕ), w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C a).inputs →
      w < n + a → ∀ h, h < C.gates.length →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
      Relation.ReflTransGen (Junk1735.Base.OrStep n C) w (n + h) →
      h ∈ PEqualNP.TopForm.junk G C ∧ ¬ PEqualNP.TopForm.BelowF G C h ∧
        PEqualNP.CleanedNonEdge.OrReaches n C w h := by
    intro w hwin hwlt h hh hhor hr
    have hhand : (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := by
      rcases hAO _ (Junk1735.Base.gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : PEqualNP.EdgeOwnership.InCone n C h a :=
      Junk1735.Base.operand_cone halen hwin hwlt hr
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
    exact ⟨hjunk, hnb, Junk1735.Base.reach_orReaches hr h rfl hh⟩
  rcases Junk1735.Base.operand_trace (C := C) u v p hp.2 with
    ⟨t1, ht1, hr1⟩ | ⟨h1, hh1, hhor1, hr1, hv1⟩
  · rcases Junk1735.Base.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        Junk1735.Base.side_adj G (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
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
        exact Junk1735.Base.reach_mem_orIn t1 hr1
      · simp only [PEqualNP.TopForm.side, e1]
        exact Junk1735.Base.reach_mem_orIn t2 hr2
    · obtain ⟨hj, _, hor⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      left
      have hside : t1 ∈ PEqualNP.TopForm.side C a 0 := by
        simp only [PEqualNP.TopForm.side, e0]
        exact Junk1735.Base.reach_mem_orIn t1 hr1
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 0)) h2' := by
        rw [Junk1735.Base.sub_zero2, e1]; exact hor
      rcases ht1 with rfl | rfl
      · exact ⟨t1, v, rfl, a, hatop, 0, h2', hj, hside, hor', hv2⟩
      · refine ⟨t1, u, Sym2.eq_swap, a, hatop, 0, h2', hj, hside, hor', ?_⟩
        rw [Junk1735.Base.pairInput_comm]; exact hv2
  · obtain ⟨hj1, hnb1, hor1⟩ := junk_of p hpin hp.1 h1 hh1 hhor1 hr1
    rcases Junk1735.Base.operand_trace (C := C) u v q hq.2 with
      ⟨t2, ht2, hr2⟩ | ⟨h2', hh2, hhor2, hr2, hv2⟩
    · left
      have hside : t2 ∈ PEqualNP.TopForm.side C a 1 := by
        simp only [PEqualNP.TopForm.side, e1]
        exact Junk1735.Base.reach_mem_orIn t2 hr2
      have hor' : PEqualNP.CleanedNonEdge.OrReaches n C
          (PEqualNP.TopForm.opnd C a ((1 : Fin 2) - 1)) h1 := by
        rw [Junk1735.Base.sub_one2, e0]; exact hor1
      rcases ht2 with rfl | rfl
      · exact ⟨t2, v, rfl, a, hatop, 1, h1, hj1, hside, hor', hv1⟩
      · refine ⟨t2, u, Sym2.eq_swap, a, hatop, 1, h1, hj1, hside, hor', ?_⟩
        rw [Junk1735.Base.pairInput_comm]; exact hv1
    · obtain ⟨hj2, _, hor2⟩ := junk_of q hqin hq.1 h2' hh2 hhor2 hr2
      right
      refine ⟨u, v, rfl, a, hatop, h1, hj1, h2', hj2, ?_, ?_, ?_, hv1, hv2⟩
      · intro heq
        subst heq
        apply hnb1
        intro x hx
        apply hbel
        show Junk1735.Base.val C (List.ofFn x) (n + a) = true
        rw [Junk1735.Base.val_and (n := n) (by simp) halen hop, hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨hp.1, Junk1735.Base.orStep_up (n := n) (by simp) hr1 hx⟩
        · exact ⟨hq.1, Junk1735.Base.orStep_up (n := n) (by simp) hr2 hx⟩
      · rw [e0]; exact hor1
      · rw [e1]; exact hor2

end Junk1735.Base

namespace Junk1735.Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  Junk1735.Base

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma inCone_lt {i j : ℕ} (hc : InCone n C i j) : i < j := by
  have go : ∀ j i, InCone n C i j → i < j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i hc
      obtain ⟨_, k, hkj, _, hi⟩ := (inCone_iff n C i j).mp hc
      rcases hi with rfl | hi
      · exact hkj
      · exact (ih k hkj i hi).trans hkj
  exact go j i hc

lemma inCone_trans {i j k : ℕ} (hij : InCone n C i j) (hjk : InCone n C j k) :
    InCone n C i k := by
  have go : ∀ k j, InCone n C j k → InCone n C i j → InCone n C i k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j hjk hij
      obtain ⟨hk, t, htk, htin, hjt⟩ := (inCone_iff n C j k).mp hjk
      apply (inCone_iff n C i k).mpr
      refine ⟨hk, t, htk, htin, Or.inr ?_⟩
      rcases hjt with rfl | hjt
      · exact hij
      · exact ih t htk j hjt hij
  exact go k j hjk hij

lemma junk_spec {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2.2⟩

lemma and_ancestor_junk (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma opnd_mem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma and_true_iff (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  change val C (List.ofFn x) (n + a) = true ↔ _
  rw [val_and (n := n) (by simp) ha hand]
  constructor
  · intro hv b
    exact (hv _ (opnd_mem hAO ha b)).2
  · intro hv w hw
    obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ha w).mp hw
    exact ⟨opnd_lt hAO ha b, hv b⟩

lemma wire_mono (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have hx : x ⟨w, hw⟩ = true := (val_ofFn C x ⟨w, hw⟩).symm.trans hv
      exact (val_ofFn C y ⟨w, hw⟩).trans (hxy _ hx)
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rcases hAO.1 _ (gateAt_mem hk) with hop | hop
        · apply (val_and (n := n) (by simp) hk hop).mpr
          intro i hi
          obtain ⟨hlt, hvi⟩ := (val_and (n := n) (by simp) hk hop).mp hv i hi
          exact ⟨hlt, ih i hlt hvi⟩
        · obtain ⟨i, hi, hlt, hvi⟩ := (val_or (n := n) (by simp) hk hop).mp hv
          exact (val_or (n := n) (by simp) hk hop).mpr ⟨i, hi, hlt, ih i hlt hvi⟩

lemma gate_mono (hAO : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ u, x u = true → y u = true) (a : ℕ)
    (hx : gateVal n C a x = true) : gateVal n C a y = true :=
  wire_mono hAO x y hxy (n + a) hx

lemma and_operand_iff (hAO : IsAO2 n C) (hTop : TopForm G C) {a p : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hp : p ∈ (gateAt C a).inputs) (x : Fin n → Bool) :
    val C (List.ofFn x) p = true ↔
      (∃ u ∈ orIn n C p, x u = true) ∨
      ∃ k ∈ junk G C, InCone n C k a ∧ OrReaches n C p k ∧ gateVal n C k x = true := by
  constructor
  · intro hv
    obtain ⟨w, hr, hvw, hw⟩ := or_trace (n := n) (C := C) (x := List.ofFn x) (by simp) p hv
    rcases hw with hw | ⟨k, hk, rfl, hnor⟩
    · exact Or.inl ⟨⟨w, hw⟩, reach_mem_orIn ⟨w, hw⟩ hr,
        (val_ofFn C x ⟨w, hw⟩).symm.trans hvw⟩
    · have hkand : (gateAt C k).op = GateOp.and := by
        rcases hAO.1 _ (gateAt_mem hk) with hand | hor
        · exact hand
        · exact (hnor hor).elim
      have hc := operand_cone ha hp (hAO.2.1 a ha p hp) hr
      exact Or.inr ⟨k, and_ancestor_junk hTop ha hand hk hkand hc,
        hc, reach_orReaches hr k rfl hk, hvw⟩
  · rintro (⟨u, hu, hxu⟩ | ⟨k, _, _, hr, hv⟩)
    · exact reach_var_val x p u (mem_orIn_reach u hu) hxu
    · exact orStep_up (n := n) (by simp) (orReaches_reach k p hr).1 hv

end Junk1735.Structural

namespace Junk1735.Final

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Junk1735

lemma two_cases : ∀ b c : Fin 2, c = b ∨ c = 1 - b := by decide

lemma forall_two {P : Fin 2 → Prop} : (∀ b, P b) ↔ P 0 ∧ P 1 := by
  constructor
  · intro h; exact ⟨h 0, h 1⟩
  · rintro ⟨h0,h1⟩ b
    rcases two_cases 0 b with rfl | hb
    · exact h0
    · have hb1 : b = 1 := by simpa using hb
      simpa only [hb1] using h1

lemma reach_up {n : ℕ} {C : Circuit} {w k : ℕ} (x : Fin n → Bool)
    (hr : OrReaches n C w k) (hv : gateVal n C k x = true) :
    Base.val C (List.ofFn x) w = true :=
  Base.orStep_up (n := n) (by simp) (Base.orReaches_reach k w hr).1 hv

lemma raw_up {n : ℕ} {C : Circuit} {w : ℕ} (x : Fin n → Bool) (u : Fin n)
    (hu : u ∈ orIn n C w) (hx : x u = true) :
    Base.val C (List.ofFn x) w = true :=
  Base.reach_var_val x w u (Base.mem_orIn_reach u hu) hx

lemma top_force {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {t : ℕ} (ht : t ∈ tops G C)
    (x : Fin n → Bool)
    (hv : ∀ b : Fin 2, Base.val C (List.ofFn x) (opnd C t b) = true) :
    graphFun G ∅ x = true := by
  have hs : t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ BelowF G C t := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ht
  exact hs.2.2 x ((Structural.and_true_iff hAO hs.1 hs.2.1 x).2 hv)

lemma top_pair_force {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {t g h : ℕ} (ht : t ∈ tops G C)
    (r0 : OrReaches n C (opnd C t 0) g)
    (r1 : OrReaches n C (opnd C t 1) h)
    (x : Fin n → Bool) (vg : gateVal n C g x = true) (vh : gateVal n C h x = true) :
    graphFun G ∅ x = true := by
  apply top_force hAO ht x
  exact forall_two.mpr ⟨reach_up x r0 vg, reach_up x r1 vh⟩

end Junk1735.Final

namespace Junk1735.Support


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

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)).le)
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hF : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) :
    G.support.ncard ≤ C.size + 1 := by
  obtain ⟨T, hT, hdep⟩ : ∃ T : Finset (Fin n), T.card ≤ C.gates.length + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        val C (List.ofFn x) C.output = val C (List.ofFn y) C.output := by
    by_cases ho : C.output < n + C.gates.length
    · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
        {C.output} (by simpa using ho)
      exact ⟨T, by simpa using hT, fun x y h => hdep x y h _ (by simp)⟩
    · exact ⟨∅, by simp, fun x y _ => by
        rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩
  have hsub : G.support ⊆ (T : Set (Fin n)) := by
    intro v hv
    obtain ⟨u, huv⟩ := (SimpleGraph.mem_support G).1 hv
    by_contra hvT
    have e := hdep (fun w => decide (w = u ∨ w = v)) (fun w => decide (w = u)) (by
      intro i hi
      have hne : i ≠ v := fun h => hvT (h ▸ hi)
      simp [hne])
    have fx : val C (List.ofFn (fun w => decide (w = u ∨ w = v))) C.output =
        graphFun G ∅ (fun w => decide (w = u ∨ w = v)) :=
      congrFun hF (fun w => decide (w = u ∨ w = v))
    have fy : val C (List.ofFn (fun w => decide (w = u))) C.output =
        graphFun G ∅ (fun w => decide (w = u)) :=
      congrFun hF (fun w => decide (w = u))
    have t1 : graphFun G ∅ (fun w => decide (w = u ∨ w = v)) = true := by
      unfold graphFun
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff]
      exact ⟨v, u, huv, by simp, by simp⟩
    have t2 : graphFun G ∅ (fun w => decide (w = u)) = false := by
      unfold graphFun
      rw [Bool.or_eq_false_iff]
      refine ⟨by simp, ?_⟩
      rw [decide_eq_false_iff_not]
      rintro ⟨a, b, hab, ha, hb⟩
      have ha' : a = u := by simpa using ha
      have hb' : b = u := by simpa using hb
      exact hab.ne (ha'.trans hb'.symm)
    rw [fx, fy, t1, t2] at e
    cases e
  calc G.support.ncard ≤ (T : Set (Fin n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet T)
    _ = T.card := Set.ncard_coe_finset T
    _ ≤ C.size + 1 := hT

end Junk1735.Support

namespace Junk1735
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def sigG {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v : Fin n) :
    {j // j ∈ junk G C} → Fin 2 → Bool :=
  fun j b => decide (v ∈ side (n := n) C j.val b)

def uniqueG {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  Finset.univ.filter fun v : Fin n => ∀ w : Fin n, sigG G C w = sigG G C v → w = v

def singleEdges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (Ustar G C).filter fun e => ∃ v ∈ uniqueG G C, v ∈ e

theorem replace_junk {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C) (u v w : Fin n)
    (same : sigG G C v = sigG G C w) : ∀ a, a ∈ junk G C →
    gateVal n C a (pairInput u v) = true → gateVal n C a (pairInput u w) = true := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha hval
    obtain ⟨alen, aand, _⟩ := Structural.junk_spec ha
    apply (Structural.and_true_iff ao alen aand (pairInput u w)).mpr
    intro b
    have ab := Structural.opnd_mem ao alen b
    have hfirst := (Structural.and_true_iff ao alen aand (pairInput u v)).mp hval b
    apply (Structural.and_operand_iff ao top alen aand ab (pairInput u w)).mpr
    rcases (Structural.and_operand_iff ao top alen aand ab (pairInput u v)).mp hfirst with
      ⟨r, hr, hv⟩ | ⟨k, hk, cone, reach, val⟩
    · rcases (Base.pairInput_true u v r).mp hv with eq | eq
      · exact Or.inl ⟨u, eq ▸ hr, Base.pairInput_left u w⟩
      · have hside : v ∈ side (n := n) C a b := eq ▸ hr
        have hb : decide (v ∈ side (n := n) C a b) = decide (w ∈ side (n := n) C a b) :=
          congrFun (congrFun same ⟨a,ha⟩) b
        exact Or.inl ⟨w, of_decide_eq_true (hb.symm.trans (decide_eq_true hside)), Base.pairInput_right u w⟩
    · exact Or.inr ⟨k, hk, cone, reach, ih k (Structural.inCone_lt cone) hk val⟩

theorem replacements {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C)
    (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :
    ∃ u v : Fin n, e = s(u,v) ∧ ∀ w, sigG G C v = sigG G C w → G.Adj u w := by
  rcases Base.edge_witness n G C least top e he with
    ⟨u,v,edge,t,ht,b,j,hj,raw,reach,hval⟩ | ⟨u,v,edge,t,ht,j,hj,k,hk,_,r0,r1,vj,vk⟩
  · refine ⟨u,v,edge,?_⟩
    intro w same
    apply (Base.graphFun_pair G u w).mp
    apply Final.top_force least.1 ht (pairInput u w)
    intro c
    rcases Final.two_cases b c with rfl | rfl
    · exact Final.raw_up (pairInput u w) u raw (Base.pairInput_left u w)
    · exact Final.reach_up (pairInput u w) reach (replace_junk least.1 top u v w same j hj hval)
  · refine ⟨u,v,edge,?_⟩
    intro w same
    apply (Base.graphFun_pair G u w).mp
    exact Final.top_pair_force least.1 ht r0 r1 (pairInput u w)
      (replace_junk least.1 top u v w same j hj vj) (replace_junk least.1 top u v w same k hk vk)

theorem common {n : Nat} (G : SimpleGraph (Fin n))
    (hg : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length)
    (p z a b : Fin n) (hpz : p ≠ z)
    (hpa : G.Adj p a) (hza : G.Adj z a) (hpb : G.Adj p b) (hzb : G.Adj z b) : a = b := by
  by_contra hab
  let w : G.Walk p p := .cons hpa (.cons hza.symm (.cons hzb (.cons hpb.symm .nil)))
  have hc : w.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · rw [SimpleGraph.Walk.isPath_def]
      simp [w, hpz.symm, hab, hza.ne.symm, hpa.ne.symm, hzb.ne, hpb.ne.symm]
    · simp [w]
  have h := hg p w hc
  simp [w] at h

theorem counts {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (girth : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length)
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C) :
    (Ustar G C).card ≤ (singleEdges G C).card + (C.size+1) ∧
    (singleEdges G C).card ≤ (uniqueG G C).card * (C.size+1) ∧
    (uniqueG G C).card ≤ 4^(junk G C).card := by
  classical
  let Q := uniqueG G C
  let H := singleEdges G C
  let E := Ustar G C
  let R := E \ H
  let S := Finset.univ.filter fun v : Fin n => v ∈ G.support
  have sSet : (S : Set (Fin n)) = G.support := by ext p; simp [S]
  have sCard : S.card = G.support.ncard := by rw [← sSet, Set.ncard_coe_finset]
  have slim : S.card ≤ C.size+1 := sCard.trans_le (Support.main n G C least.1.2.2 least.2.1)
  have sub : H ⊆ E := Finset.filter_subset _ _
  have os (e : R) : ∃ u v : Fin n, e.val = s(u,v) ∧ ∀ w, sigG G C v = sigG G C w → G.Adj u w :=
    replacements least top e.val (Finset.mem_sdiff.mp e.property).1
  choose u v edge good using os
  have vs (e : R) : v e ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u e, (good e (v e) rfl).symm⟩⟩
  let load (e : R) : S := ⟨v e, vs e⟩
  have inj : Function.Injective load := by
    intro e f eq
    have sameV : v e = v f := congrArg Subtype.val eq
    have ns : v e ∉ Q := by
      intro hv
      apply (Finset.mem_sdiff.mp e.property).2
      refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp e.property).1,v e,hv,?_⟩
      rw [edge e]
      exact Sym2.mem_iff.mpr (Or.inr rfl)
    obtain ⟨w, same, diff⟩ : ∃ w : Fin n, sigG G C w = sigG G C (v e) ∧ w ≠ v e := by
      by_contra! no
      exact ns (Finset.mem_filter.mpr ⟨Finset.mem_univ _, no⟩)
    have sameWF : sigG G C (v f) = sigG G C w := (congrArg (sigG G C) sameV).symm.trans same.symm
    have gf : G.Adj (u f) (v e) := sameV.symm ▸ good f (v f) rfl
    have sameU : u e = u f := common G girth (v e) w (u e) (u f) diff.symm
      (good e (v e) rfl).symm (good e w same.symm).symm gf.symm (good f w sameWF).symm
    apply Subtype.ext
    rw [edge e, edge f, sameV, sameU]
  have taken : R.card ≤ S.card := by simpa using Fintype.card_le_of_injective load inj
  have total : R.card + H.card = E.card := Finset.card_sdiff_add_card_eq_card sub
  have cover : H ⊆ Q.biUnion (fun a => S.image (fun b => s(a,b))) := by
    intro e he
    obtain ⟨hE, a, ha, hae⟩ := Finset.mem_filter.mp he
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hae
    have heq : e = s(a,b) := by first | exact hb | exact hb.symm
    have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp hE).1
    rw [heq] at hedge
    have adj : G.Adj a b := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp hedge)
    have bs : b ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, adj.symm⟩⟩
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_image.mpr ⟨b,bs,heq.symm⟩⟩
  have high : H.card ≤ Q.card * S.card := (Finset.card_le_card cover).trans
    (Finset.card_biUnion_le_card_mul Q _ _ (fun _ _ => Finset.card_image_le))
  have numbered : Function.Injective (fun x : Q => sigG G C x.val) := by
    intro a b eq
    exact Subtype.ext ((Finset.mem_filter.mp b.property).2 a.val eq)
  refine ⟨?_, high.trans (Nat.mul_le_mul_left Q.card slim), ?_⟩
  · change E.card ≤ H.card + (C.size + 1)
    omega
  · calc Q.card = Fintype.card Q := (Fintype.card_coe Q).symm
         _ ≤ Fintype.card ({j // j ∈ junk G C} → Fin 2 → Bool) := Fintype.card_le_of_injective _ numbered
         _ = 4^(junk G C).card := by norm_num [Fintype.card_fun]

def Dominates {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v w : Fin n) : Prop :=
  ∀ j∈junk G C, ∀b : Fin 2, v∈side (n:=n) C j b → w∈side (n:=n) C j b

instance {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (v w : Fin n) :
    Decidable (Dominates G C v w) := by unfold Dominates; infer_instance

def maximalG {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  Finset.univ.filter fun v : Fin n => ∀w : Fin n, Dominates G C v w → w=v

def maximalEdges {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :=
  (Ustar G C).filter fun e => ∃v∈maximalG G C,v∈e

theorem replace_dominated {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (top : PEqualNP.TopForm.TopForm G C) (u v w : Fin n)
    (same : Dominates G C v w) : ∀ a, a ∈ junk G C →
    gateVal n C a (pairInput u v) = true → gateVal n C a (pairInput u w) = true := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro ha hval
    obtain ⟨alen, aand, _⟩ := Structural.junk_spec ha
    apply (Structural.and_true_iff ao alen aand (pairInput u w)).mpr
    intro b
    have ab := Structural.opnd_mem ao alen b
    have hfirst := (Structural.and_true_iff ao alen aand (pairInput u v)).mp hval b
    apply (Structural.and_operand_iff ao top alen aand ab (pairInput u w)).mpr
    rcases (Structural.and_operand_iff ao top alen aand ab (pairInput u v)).mp hfirst with
      ⟨r, hr, hv⟩ | ⟨k, hk, cone, reach, val⟩
    · rcases (Base.pairInput_true u v r).mp hv with eq | eq
      · exact Or.inl ⟨u, eq ▸ hr, Base.pairInput_left u w⟩
      · have hside : v ∈ side (n := n) C a b := eq ▸ hr
        exact Or.inl ⟨w,same a ha b hside,Base.pairInput_right u w⟩
    · exact Or.inr ⟨k, hk, cone, reach, ih k (Structural.inCone_lt cone) hk val⟩

theorem orient_dominated {n : Nat} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C)
    (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :
    ∃ u v : Fin n, e = s(u,v) ∧ ∀ w, Dominates G C v w → G.Adj u w := by
  rcases Base.edge_witness n G C least top e he with
    ⟨u,v,edge,t,ht,b,j,hj,raw,reach,hval⟩ | ⟨u,v,edge,t,ht,j,hj,k,hk,_,r0,r1,vj,vk⟩
  · refine ⟨u,v,edge,?_⟩
    intro w same
    apply (Base.graphFun_pair G u w).mp
    apply Final.top_force least.1 ht (pairInput u w)
    intro c
    rcases Final.two_cases b c with rfl | rfl
    · exact Final.raw_up (pairInput u w) u raw (Base.pairInput_left u w)
    · exact Final.reach_up (pairInput u w) reach (replace_dominated least.1 top u v w same j hj hval)
  · refine ⟨u,v,edge,?_⟩
    intro w same
    apply (Base.graphFun_pair G u w).mp
    exact Final.top_pair_force least.1 ht r0 r1 (pairInput u w)
      (replace_dominated least.1 top u v w same j hj vj) (replace_dominated least.1 top u v w same k hk vk)

theorem maximal_rest {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (girth : ∀ p (w : G.Walk p p), w.IsCycle → 5 ≤ w.length)
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C) :
    (Ustar G C).card ≤ (maximalEdges G C).card + (C.size+1) := by
  classical
  let Q := maximalG G C
  let H := maximalEdges G C
  let E := Ustar G C
  let R := E \ H
  let S := Finset.univ.filter fun v : Fin n => v ∈ G.support
  have sSet : (S : Set (Fin n)) = G.support := by ext p; simp [S]
  have sCard : S.card = G.support.ncard := by rw [← sSet, Set.ncard_coe_finset]
  have slim : S.card ≤ C.size+1 := sCard.trans_le (Support.main n G C least.1.2.2 least.2.1)
  have sub : H ⊆ E := Finset.filter_subset _ _
  have os (e : R) : ∃ u v : Fin n, e.val = s(u,v) ∧ ∀ w, Dominates G C v w → G.Adj u w :=
    orient_dominated least top e.val (Finset.mem_sdiff.mp e.property).1
  choose u v edge good using os
  have vs (e : R) : v e ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨u e, (good e (v e) (fun _ _ _ h=>h)).symm⟩⟩
  let load (e : R) : S := ⟨v e, vs e⟩
  have inj : Function.Injective load := by
    intro e f eq
    have sameV : v e = v f := congrArg Subtype.val eq
    have ns : v e ∉ Q := by
      intro hv
      apply (Finset.mem_sdiff.mp e.property).2
      refine Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp e.property).1,v e,hv,?_⟩
      rw [edge e]
      exact Sym2.mem_iff.mpr (Or.inr rfl)
    obtain ⟨w, same, diff⟩ : ∃ w : Fin n, Dominates G C (v e) w ∧ w ≠ v e := by
      by_contra! no
      exact ns (Finset.mem_filter.mpr ⟨Finset.mem_univ _, no⟩)
    have sameWF : Dominates G C (v f) w := sameV ▸ same
    have gf : G.Adj (u f) (v e) := sameV.symm ▸ good f (v f) (fun _ _ _ h=>h)
    have sameU : u e = u f := common G girth (v e) w (u e) (u f) diff.symm
      (good e (v e) (fun _ _ _ h=>h)).symm (good e w same).symm gf.symm (good f w sameWF).symm
    apply Subtype.ext
    rw [edge e, edge f, sameV, sameU]
  have taken : R.card ≤ S.card := by simpa using Fintype.card_le_of_injective load inj
  have total : R.card + H.card = E.card := Finset.card_sdiff_add_card_eq_card sub
  change E.card ≤ H.card+(C.size+1)
  omega

theorem anchor_bound {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (girth : ∀p (w : G.Walk p p),w.IsCycle → 5≤w.length)
    (Q : Finset (Fin n)) (H : Finset (Sym2 (Fin n))) (hedges : H⊆G.edgeFinset)
    (cover : ∀e∈H,∃a∈Q,a∈e) : H.card ≤ G.support.ncard+Q.card.choose 2 := by
  classical
  let S := Finset.univ.filter fun i : Fin n => i∈G.support
  have support : S.card = G.support.ncard := by
    have setEq : (S : Set (Fin n))=G.support := by ext i; simp [S]
    rw [←setEq,Set.ncard_coe_finset]
  by_cases empty : H=∅
  · simp [empty]
  obtain ⟨e0,he0⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  obtain ⟨q0,q0Q,_⟩ := cover e0 he0
  have orient (e : H) : ∃ u v : Fin n,e.val=s(u,v) ∧ v∈Q ∧ G.Adj u v := by
    obtain ⟨v,hv,ve⟩ := cover e.val e.property
    obtain ⟨u,hu⟩ := Sym2.mem_iff_exists.mp ve
    have eq : e.val=s(v,u) := by first | exact hu | exact hu.symm
    have mem := hedges e.property
    rw [eq] at mem
    exact ⟨u,v,eq.trans Sym2.eq_swap,hv,(G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp mem)).symm⟩
  choose u v edge vQ adj using orient
  let anchor (x : Fin n) := if h : ∃a∈Q,G.Adj x a then h.choose else q0
  have anch (e : H) : anchor (u e)∈Q ∧ G.Adj (u e) (anchor (u e)) := by
    have h : ∃a∈Q,G.Adj (u e) a := ⟨v e,vQ e,adj e⟩
    simpa only [anchor,dif_pos h] using h.choose_spec
  let key (e : H) : Finset (Fin n) := {anchor (u e),v e}
  have valid (e : H) (different : anchor (u e)≠v e) : key e∈Q.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro x hx
      rcases (show x=anchor (u e) ∨ x=v e by simpa [key] using hx) with rfl|rfl
      · exact (anch e).1
      · exact vQ e
    · simp [key,different]
  let F := Q.powersetCard 2
  let send (e : H) : S ⊕ F := if h : anchor (u e)=v e then
    Sum.inl ⟨u e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨v e,adj e⟩⟩⟩
    else Sum.inr ⟨key e,valid e h⟩
  have inj : Function.Injective send := by
    intro e f eq
    by_cases he : anchor (u e)=v e <;> by_cases hf : anchor (u f)=v f
    · have sameU : u e=u f := congrArg Subtype.val (Sum.inl.inj (by simpa only [send,dif_pos he,dif_pos hf] using eq))
      have sameV := he.symm.trans ((congrArg anchor sameU).trans hf)
      exact Subtype.ext ((edge e).trans ((congrArg₂ (fun x y : Fin n=>s(x,y)) sameU sameV).trans (edge f).symm))
    · simp [send,he,hf] at eq
    · simp [send,he,hf] at eq
    · have sameKey : key e=key f := congrArg Subtype.val (Sum.inr.inj (by simpa only [send,dif_neg he,dif_neg hf] using eq))
      have both (z : H) (a) (mem : a∈key z) : G.Adj (u z) a := by
        rcases (show a=anchor (u z) ∨ a=v z by simpa [key] using mem) with rfl|rfl
        · exact (anch z).2
        · exact adj z
      have a : anchor (u e)∈key f := sameKey ▸ (by simp [key] : anchor (u e)∈key e)
      have b : v e∈key f := sameKey ▸ (by simp [key] : v e∈key e)
      have sameU : u e=u f := common G girth (anchor (u e)) (v e) (u e) (u f) he
        (anch e).2.symm (adj e).symm (both f _ a).symm (both f _ b).symm
      have val : v e=anchor (u f) ∨ v e=v f := by simpa [key] using b
      have sameV : v e=v f := val.resolve_left (fun bad=>he ((congrArg anchor sameU).trans bad.symm))
      exact Subtype.ext ((edge e).trans ((congrArg₂ (fun x y : Fin n=>s(x,y)) sameU sameV).trans (edge f).symm))
  have size := Fintype.card_le_of_injective send inj
  simpa only [Fintype.card_coe,Fintype.card_sum,F,Finset.card_powersetCard,support] using size

theorem maximal_profile {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (girth : ∀p (w : G.Walk p p),w.IsCycle→5≤w.length)
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C) :
    (Ustar G C).card ≤ 2*(C.size+1)+(maximalG G C).card.choose 2 := by
  let Q := maximalG G C
  let H := maximalEdges G C
  have sub : H⊆G.edgeFinset := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have cv (e) (he : e∈H) : ∃a∈Q,a∈e := (Finset.mem_filter.mp he).2
  have anchor := anchor_bound G girth Q H sub cv
  have rest := maximal_rest G C girth least top
  have cap := Support.main n G C least.1.2.2 least.2.1
  change (Ustar G C).card≤H.card+(C.size+1) at rest
  change (Ustar G C).card≤2*(C.size+1)+Q.card.choose 2
  omega

theorem exceptional_types {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    (maximalG G C).card ≤ 4^(junk G C).card := by
  classical
  let Q := maximalG G C
  have inj : Function.Injective (fun v : Q=>sigG G C v.val) := by
    intro a b eq
    apply Subtype.ext
    apply (Finset.mem_filter.mp b.property).2
    intro j hj k mem
    have same := congrFun (congrFun eq ⟨j,hj⟩) k
    exact of_decide_eq_true (same.trans (decide_eq_true mem))
  calc (maximalG G C).card = Fintype.card Q := (Fintype.card_coe Q).symm
       _ ≤ Fintype.card ({j // j∈junk G C} → Fin 2 → Bool) := Fintype.card_le_of_injective _ inj
       _ = _ := by norm_num [Fintype.card_fun]

theorem slowly_growing {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (girth : ∀p (w : G.Walk p p),w.IsCycle→5≤w.length)
    (least : IsLeastAO G C) (top : PEqualNP.TopForm.TopForm G C)
    (small : (4^(junk G C).card).choose 2 ≤ C.size+1) :
    (Ustar G C).card ≤ 3*(C.size+1) := by
  have h := maximal_profile G C girth least top
  have bound := Nat.choose_le_choose 2 (exceptional_types G C)
  omega

end Junk1735

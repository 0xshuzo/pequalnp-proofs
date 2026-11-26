import PEqualNP.Defs

-- The evaluation preliminaries through val_ofFn_lt are from L_meta_3545 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_3568


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

open PEqualNP.TopForm

theorem first_reader {n : Nat} (C : Circuit) (rb : ReadsBack n C) (z : Fin n)
    (X Y : Fin n → Bool) (off : ∀ v : Fin n, v ≠ z → X v = Y v)
    (zero : X z = false) (out : C.output ≠ z.val)
    (diff : circuitFun n C X ≠ circuitFun n C Y)
    (andOnly : ∀ j < C.gates.length, z.val ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.and) :
    ∃ j < C.gates.length, z.val ∈ (gateAt C j).inputs ∧
      ∀ i ∈ (gateAt C j).inputs, i ≠ z.val → val C (List.ofFn X) i = true := by
  classical
  let old := val C (List.ofFn X)
  let new := val C (List.ofFn Y)
  have ex : ∃ w : Nat, w ≠ z.val ∧ old w ≠ new w := ⟨C.output,out,diff⟩
  let w := Nat.find ex
  obtain ⟨wz,wc⟩ : w ≠ z.val ∧ old w ≠ new w := Nat.find_spec ex
  have earlier (i : Nat) (hi : i < w) (iz : i ≠ z.val) : old i = new i := by
    by_contra h
    exact Nat.find_min ex hi ⟨iz,h⟩
  have lo : n ≤ w := by
    by_contra! small
    apply wc
    change val C (List.ofFn X) w = val C (List.ofFn Y) w
    rw [val_ofFn_lt _ _ _ small,val_ofFn_lt _ _ _ small]
    exact off _ (fun e => wz (congrArg Fin.val e))
  have hi : w < n+C.gates.length := by
    by_contra! big
    apply wc
    change val C (List.ofFn X) w = val C (List.ofFn Y) w
    rw [val_ge (by simp) (n:=n) big,val_ge (by simp) (n:=n) big]
  let j := w-n
  have wj : n+j=w := by dsimp only [j]; omega
  have valid : j<C.gates.length := by omega
  have leval : old w = (gateAt C j).op.eval ((gateAt C j).inputs.map old) := by
    rw [←wj]
    exact val_gate_rb (by simp) valid (rb j valid)
  have reval : new w = (gateAt C j).op.eval ((gateAt C j).inputs.map new) := by
    rw [←wj]
    exact val_gate_rb (by simp) valid (rb j valid)
  have before (i) (e : i ∈ (gateAt C j).inputs) : i < w := wj ▸ rb j valid i e
  have reads : z.val ∈ (gateAt C j).inputs := by
    by_contra h
    apply wc
    rw [leval,reval]
    congr 1
    apply List.map_congr_left
    intro i e
    exact earlier i (before i e) (fun eq => h (eq ▸ e))
  have hop := andOnly j valid reads
  have z0 : old z.val = false := (val_ofFn C X z).trans zero
  have low : old w ≠ true := by
    intro yes
    rw [leval,hop,eval_and_iff] at yes
    have h := yes z.val reads
    rw [z0] at h
    contradiction
  have high : new w = true := by
    cases l : old w <;> cases r : new w <;> simp_all
  rw [reval,hop,eval_and_iff] at high
  refine ⟨j,valid,reads,?_⟩
  intro i e iz
  exact (earlier i (before i e) iz).trans (high i e)

end PEqualNP.Outside.L_meta_3568

-- Wire bypass lemmas from the published L_meta_1485.
namespace PEqualNP.Outside.L_meta_3568.Bypass

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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_eval_eq {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : val C x (n + r) = val C x i) :
    (bypass n C r i).eval x = C.eval x :=
  (bypass_eval_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi hR).symm

lemma bypass_eval_unread {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hout : C.output ≠ n + r)
    (hno : ∀ k < C.gates.length, n + r ∉ (gateAt C k).inputs) :
    (bypass n C r i).eval x = C.eval x := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  exact (bypass_rel (R := Eq) (fun _ => rfl) opMono_eq hx hAO hr hi
    (fun ⟨k, hk, hm⟩ => absurd hm (hno k hk)) _ hout).symm

lemma bypass_AO {n : ℕ} {C : Circuit} {r i : ℕ} (hr : r < C.gates.length)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ k < (bypass n C r i).gates.length,
      (gateAt (bypass n C r i) k).op = GateOp.and ∨
        (gateAt (bypass n C r i) k).op = GateOp.or := by
  intro k hk
  rw [bypass_length] at hk
  rw [gateAt_bypass hk]
  split_ifs with h
  · exact hAO k (by omega)
  · exact hAO (k + 1) (by omega)

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma aliasWire_lt {w i u m : ℕ} (hi : i < w) (hwm : w ≤ m) (hu : u < m + 1) :
    aliasWire w i u < m := by
  unfold aliasWire; split_ifs <;> omega

lemma bypass_readsBack {n : ℕ} {C : Circuit} {r i : ℕ} (hi : i < n + r)
    (hRB : ∀ k < C.gates.length, ∀ u ∈ (gateAt C k).inputs, u < n + k) :
    ∀ k < (bypass n C r i).gates.length,
      ∀ u ∈ (gateAt (bypass n C r i) k).inputs, u < n + k := by
  intro k hk u hu
  rw [bypass_length] at hk
  rw [gateAt_bypass hk] at hu
  split_ifs at hu with h
  · exact hRB k (by omega) u hu
  · simp only [aliasGate, List.mem_map] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have := hRB (k + 1) (by omega) u' hu'
    exact aliasWire_lt hi (by omega) (by omega)

lemma isAO2_bypass {n : ℕ} {D : Circuit} {r i : ℕ} (hD : PEqualNP.TopForm.IsAO2 n D)
    (hi : i < n + r) : PEqualNP.TopForm.IsAO2 n (bypass n D r i) := by
  refine ⟨?_, bypass_readsBack hi hD.2.1, ?_⟩
  · intro g hg
    obtain ⟨g', hg', hop, _⟩ := bypass_mem g hg
    rw [hop]; exact hD.1 g' hg'
  · intro g hg
    obtain ⟨g', hg', _, hl⟩ := bypass_mem g hg
    rw [hl]; exact hD.2.2 g' hg'

end PEqualNP.Outside.L_meta_3568.Bypass

-- Slice compiler from the published L_meta_18145.
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

private abbrev W (n : ℕ) (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  scan boolStep gs (List.ofFn x)

private theorem inputAt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (W n gs x).getD i false = x ⟨i,hi⟩ := by
  rw [scan_prefix boolStep _ _ _ _ (by simpa using hi),List.getD_eq_getElem _ _ (by simpa using hi),List.getElem_ofFn]

private theorem wireAtGate {n : ℕ} (C : Circuit) (h : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    (W n C.gates x).getD (n+j) false = boolStep (W n C.gates x) C.gates[j] := by
  simpa only [List.length_ofFn] using
    (scan_gate boolStep C.gates (List.ofFn x) false j hj (fun r s he => by
      unfold boolStep
      congr 1
      apply List.map_congr_left
      intro i hi
      apply he
      have := h.2.1 j hj i (by rwa [gateAt_eq_getElem hj])
      simpa using this))

private def readOpt (w : List Bool) (ref : Option ℕ) : Bool :=
  (ref.map fun i => w.getD i false).getD false

private def validRef (lim : ℕ) (ref : Option ℕ) : Prop :=
  ∀ i, ref = some i → i < lim

private theorem optPrefix (w : List Bool) (v : Bool) (ref : Option ℕ) (ok : validRef w.length ref) :
    readOpt (w ++ [v]) ref = readOpt w ref := by
  cases ref with
  | none => rfl
  | some i => exact List.getD_append _ _ _ _ (ok i rfl)

private inductive Action where
  | reuse (ref : Option ℕ)
  | add (g : Gate)

private def Action.ref (lim : ℕ) : Action → Option ℕ
  | .reuse r => r
  | .add _ => some lim

private def Action.newGates : Action → List Gate
  | .reuse _ => []
  | .add g => [g]

private def Action.eval (w : List Bool) : Action → Bool
  | .reuse r => readOpt w r
  | .add g => boolStep w g

private def Action.Well (limit : ℕ) : Action → Prop
  | .reuse r => validRef limit r
  | .add g => (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < limit

private theorem newGatesSmall (act : Action) : act.newGates.length ≤ 1 := by cases act <;> simp [Action.newGates]

private def pick (op : GateOp) (a b : Option ℕ) : Action :=
  match a, b with
  | some i, some j => .add ⟨op,[i,j]⟩
  | none, v | v, none => .reuse (if op.eval [false,true] then v else none)

private theorem pickSound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (w : List Bool) : (pick op a b).eval w =
      op.eval [readOpt w a,readOpt w b] := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp [pick,Action.eval,readOpt,GateOp.eval,boolStep]

private theorem pickWell (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (a b : Option ℕ) (lim : ℕ) (va : validRef lim a) (vb : validRef lim b) :
    (pick op a b).Well lim := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;>
    simp_all [pick,Action.Well,validRef,GateOp.eval]

private theorem actionApply {n : ℕ} (gs : List Gate) (legal : IsAO2 n (⟨gs,0⟩ : Circuit))
    (act : Action) (well : act.Well (n+gs.length)) :
    IsAO2 n (⟨gs++act.newGates,0⟩ : Circuit) := by
  cases act with
  | reuse r => simpa [Action.newGates] using legal
  | add g =>
    obtain ⟨hop,hlen,back⟩ := well
    refine ⟨?_,?_,?_⟩
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.1 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hop
    · intro j hj i hi
      change j < (gs ++ [g]).length at hj
      simp only [List.length_append,List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · have he : gateAt ⟨gs++[g],0⟩ j = gateAt ⟨gs,0⟩ j := by
          rw [gateAt,gateAt,List.getD_append _ _ _ _ hlt]
        exact legal.2.1 j hlt i (he ▸ hi)
      · have heq : j = gs.length := by omega
        subst j
        have he : gateAt ⟨gs++[g],0⟩ gs.length = g := by
          rw [gateAt,List.getD_append_right _ _ _ _ (by simp),Nat.sub_self,List.getD_cons_zero]
        exact back i (he ▸ hi)
    · intro g' hm
      rcases List.mem_append.mp hm with h | h
      · exact legal.2.2 _ h
      · obtain rfl := List.mem_singleton.mp h
        exact hlen

private theorem oldSource (act : Action) (w : List Bool) (ref : Option ℕ)
    (vr : validRef w.length ref) :
    readOpt (scan boolStep act.newGates w) ref = readOpt w ref := by
  cases act with
  | reuse r => rfl
  | add g => exact optPrefix w _ ref vr

private theorem resultSource (act : Action) (w : List Bool) (ok : act.Well w.length) :
    readOpt (scan boolStep act.newGates w) (act.ref w.length) = act.eval w := by
  cases act with
  | reuse r => rfl
  | add g =>
    change (w ++ [boolStep w g]).getD w.length false = boolStep w g
    rw [List.getD_append_right _ _ _ _ (Nat.le_refl _),Nat.sub_self,List.getD_cons_zero]

private theorem refAvailable (act : Action) (lim : ℕ) (hw : act.Well lim) :
    validRef (lim+act.newGates.length) (act.ref lim) := by
  cases act with
  | reuse r => simpa [Action.ref,Action.newGates,Action.Well] using hw
  | add g => simp [Action.ref,Action.newGates,validRef]

private theorem validEnlarge (ref : Option ℕ) {a b : ℕ} (h : a ≤ b) (vr : validRef a ref) : validRef b ref :=
  fun i hi => Nat.lt_of_lt_of_le (vr i hi) h

private abbrev fixed {n : ℕ} (x : Fin n → Bool) (p : Fin n) := Function.update x p false

private structure Prefix (n : ℕ) (C : Circuit) (p : Fin n) (S : Finset ℕ) (j : ℕ) where
  gs : List Gate
  f : ℕ → Option ℕ
  legal : IsAO2 n (⟨gs,0⟩ : Circuit)
  cost : gs.length + (S.filter (· < j)).card ≤ j
  valids : ∀ i < n+j, validRef (n+gs.length) (f i)
  sound : ∀ i < n+j, ∀ x : Fin n → Bool,
    readOpt (W n gs x) (f i) = (W n C.gates (fixed x p)).getD i false

private theorem countFilterStep (S : Finset ℕ) (j : ℕ) :
    (S.filter (· < j+1)).card = (S.filter (· < j)).card + if j ∈ S then 1 else 0 := by
  by_cases hm : j ∈ S
  · have e : S.filter (· < j+1) = insert j (S.filter (· < j)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hl⟩
        by_cases e : i = j
        · exact Or.inl e
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [e,Finset.card_insert_of_notMem (by simp),ite_eq_left hm]
  · have e : S.filter (· < j+1) = S.filter (· < j) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hl⟩
        exact ⟨hi,by have hn : i ≠ j := fun eq => hm (eq ▸ hi); omega⟩
      · rintro ⟨hi,hl⟩; exact ⟨hi,by omega⟩
    rw [e,ite_eq_right hm,Nat.add_zero]

private def Prefix.step {n : ℕ} {C : Circuit} {p : Fin n} {S : Finset ℕ} {j : ℕ}
    (P : Prefix n C p S j) (act : Action) (hw : act.Well (n+P.gs.length))
    (hshort : act.newGates.length + (if j ∈ S then 1 else 0) ≤ 1)
    (ok : ∀ x : Fin n → Bool, act.eval (W n P.gs x) =
      (W n C.gates (fixed x p)).getD (n+j) false) : Prefix n C p S (j+1) := by
  let new := P.gs ++ act.newGates
  let ff (i : ℕ) := if i = n+j then act.ref (n+P.gs.length) else P.f i
  refine ⟨new,ff,actionApply P.gs P.legal act hw,?_,?_,?_⟩
  · have hc := P.cost
    rw [countFilterStep]
    simp only [new,List.length_append]
    omega
  · intro i hi
    by_cases he : i = n+j
    · simpa [ff,new,he,Nat.add_assoc] using refAvailable act (n+P.gs.length) hw
    · change validRef _ (if i = n+j then _ else P.f i)
      rw [ite_eq_right he]
      exact validEnlarge _ (by simp [new]) (P.valids _ (by omega))
  · intro i hi x
    have len : (W n P.gs x).length = n+P.gs.length := by rw [scan_length,List.length_ofFn]
    rw [show W n new x = scan boolStep act.newGates (W n P.gs x) by exact scan_append boolStep _ _ _]
    by_cases he : i = n+j
    · subst i
      simp only [ff,ite_true]
      rw [← len,resultSource _ _ (by rw [len]; exact hw)]
      exact ok x
    · simp only [ff,he,ite_false]
      rw [oldSource _ _ _ (by rw [len]; exact P.valids _ (by omega))]
      exact P.sound _ (by omega) x

private theorem build {n : ℕ} {C : Circuit} (p : Fin n) (S : Finset ℕ)
    (hC : IsAO2 n C)
    (aliases : ∀ j ∈ S, ∃ i < n+j, ∀ x : Fin n → Bool,
      (W n C.gates (fixed x p)).getD (n+j) false = (W n C.gates (fixed x p)).getD i false)
    (j : ℕ) (bound : j ≤ C.gates.length) : Nonempty (Prefix n C p S j) := by
  induction j with
  | zero =>
    refine ⟨⟨[],fun i => if i = p.val then none else some i,by simp [IsAO2,PEqualNP.EdgeOwnership.AndOrOnly,ReadsBack],by simp,?_,?_⟩⟩
    · intro i hi
      by_cases he : i = p.val
      · simp [he,validRef]
      · simpa [he,validRef] using hi
    · intro i hi x
      have hi' : i < n := by simpa using hi
      rw [inputAt C.gates _ i hi']
      by_cases he : i = p.val
      · have hp : (⟨i,hi'⟩ : Fin n) = p := Fin.ext he
        simp [he,readOpt,fixed]
      · have hp : (⟨i,hi'⟩ : Fin n) ≠ p := fun h => he (congrArg Fin.val h)
        simp only [he,ite_false,readOpt,Option.map_some,Option.getD_some]
        rw [inputAt [] x i hi']
        simp [fixed,Function.update_of_ne hp]
  | succ j ih =>
    obtain ⟨P⟩ := ih (by omega)
    have hj : j < C.gates.length := by omega
    by_cases hm : j ∈ S
    · obtain ⟨i,hi,he⟩ := aliases j hm
      refine ⟨P.step (.reuse (P.f i)) (P.valids i hi) (by simp [Action.newGates,hm]) (fun x => ?_)⟩
      exact (P.sound i hi x).trans (he x).symm
    · obtain ⟨hop,hin,ha,hb⟩ := ao2_gate_props hC hj
      let g := gateAt C j
      let a := opnd C j 0
      let b := opnd C j 1
      let act := pick g.op (P.f a) (P.f b)
      refine ⟨P.step act (pickWell _ hop _ _ _ (P.valids a ha) (P.valids b hb)) ?_ (fun x => ?_)⟩
      · simpa [hm] using newGatesSmall act
      · rw [wireAtGate C hC j hj,← gateAt_eq_getElem hj]
        rw [pickSound g.op hop, P.sound a ha, P.sound b hb]
        change g.op.eval [_ , _] = boolStep _ g
        rw [boolStep,show g.inputs = [a,b] from hin]
        rfl



theorem compile : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin x1) (x4 : Finset ℕ),   PEqualNP.TopForm.IsAO2 x1 x2 →     (∀ x6 ∈ x4,         x6 < x2.size ∧           ∃ x8 < x1 + x6,             ∀ (x9 : Fin x1 → Bool),               have x10 : List Bool := x2.wires (List.ofFn (Function.update x9 x3 Bool.false));               x10.getD (x1 + x6) Bool.false = x10.getD x8 Bool.false) →       (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool), x2.eval (List.ofFn (Function.update x7 x3 Bool.false)) ≠ x2.eval (List.ofFn (Function.update x8 x3 Bool.false))) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x8 ∧ x8.size + x4.card ≤ x2.size ∧ ∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = x2.eval (List.ofFn (Function.update x9 x3 Bool.false))) := by
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3568.Slice in
  intro n C p S hC hAlias nconst
  obtain ⟨P⟩ := build p S hC (fun j hj => (hAlias j hj).2) C.gates.length (Nat.le_refl _)
  have within : C.output < n + C.gates.length := by
    by_contra! h
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      change (W n C.gates (fixed z p)).getD C.output false = false
      apply List.getD_eq_default
      rwa [scan_length,List.length_ofFn]
    exact hn ((zero x).trans (zero y).symm)
  cases he : P.f C.output with
  | none =>
    obtain ⟨x,y,hn⟩ := nconst
    have zero (z : Fin n → Bool) : C.eval (List.ofFn (fixed z p)) = false := by
      have hz := P.sound C.output within z
      rw [he] at hz
      exact hz.symm
    exact False.elim (hn ((zero x).trans (zero y).symm))
  | some o =>
    have hsize := P.cost
    have hs : S.filter (· < C.gates.length) = S := Finset.filter_true_of_mem (fun _ hi => (hAlias _ hi).1)
    rw [hs] at hsize
    refine ⟨⟨P.gs,o⟩,P.legal,hsize,?_⟩
    intro x
    change (W n P.gs x).getD o false = (W n C.gates (fixed x p)).getD C.output false
    simpa only [he,readOpt,Option.map_some,Option.getD_some] using P.sound C.output within x

end PEqualNP.Outside.L_meta_3568.Slice

namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

variable {n : Nat} {C : Circuit}

private abbrev V (C : Circuit) (x : Fin n → Bool) (w : Nat) :=
  (C.wires (List.ofFn x)).getD w false

private theorem vin (x : Fin n → Bool) (p : Fin n) : V C x p.val = x p := by
  change Bypass.val C (List.ofFn x) p.val = x p
  rw [Bypass.val_input (List.length_ofFn) p.isLt, List.getD_eq_getElem _ _ (by simpa using p.isLt)]
  simp

private theorem vgate (hao : IsAO2 n C) (j : Nat) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    V C x (n+j) = (gateAt C j).op.eval
      [V C x (opnd C j 0), V C x (opnd C j 1)] := by
  obtain ⟨_, hin, ha, hb⟩ := Slice.ao2_gate_props hao hj
  change Bypass.val C _ _ = _
  rw [Bypass.val_gate (List.length_ofFn) hj, hin]
  simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb]
  rfl

private theorem inputs_pair (hao : IsAO2 n C) {j w : Nat} (hj : j < C.gates.length)
    (hw : w ∈ (gateAt C j).inputs) :
    ∃ t < n+j, (opnd C j 0 = w ∧ opnd C j 1 = t) ∨
      (opnd C j 0 = t ∧ opnd C j 1 = w) := by
  obtain ⟨_, hi, ha, hb⟩ := Slice.ao2_gate_props hao hj
  rw [hi] at hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with h | h
  · exact ⟨_,hb,Or.inl ⟨h.symm,rfl⟩⟩
  · exact ⟨_,ha,Or.inr ⟨rfl,h.symm⟩⟩

private theorem vseparate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) {j w : Nat} (hj : j < C.gates.length) (hw : w < n+j) :
    ¬ ∀ (x : Fin n → Bool), V C x (n+j) = V C x w := by
  intro same
  let D := Bypass.bypass n C j w
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_eq List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hw) (same x)
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hw) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j w).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private theorem live (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {j : Nat} (hj : j < C.gates.length)
    (hout : C.output ≠ n+j) : ∃ k < C.gates.length, n+j ∈ (gateAt C k).inputs := by
  by_contra! h
  let D := Bypass.bypass n C j p.val
  have hp : p.val < n+j := by have := p.isLt; omega
  have eqv : circuitFun n D = circuitFun n C := by
    funext x
    exact Bypass.bypass_eval_unread List.length_ofFn
      (fun k hk => (Slice.ao2_gate_props least.1 hk).1) hj (Or.inl hp) hout h
  have le := least.2.2 D (Bypass.isAO2_bypass least.1 hp) (eqv.trans least.2.1)
  change C.gates.length ≤ (Bypass.bypass n C j p.val).gates.length at le
  rw [Bypass.bypass_length] at le
  omega

private def Zero (C : Circuit) (p : Fin n) (w : Nat) : Prop :=
  ∀ x : Fin n → Bool, x p = false → V C x w = false

private theorem inputZero (p : Fin n) : Zero C p p.val := by
  intro x hx
  simpa only [vin] using hx

private theorem zeroAnd (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hand : (gateAt C j).op = .and)
    (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) : Zero C p (n+j) := by
  obtain ⟨t,_,h | h⟩ := inputs_pair hao hj hw <;> intro x hx <;>
    rw [vgate hao j hj x, hand, h.1, h.2, hz x hx] <;> simp [GateOp.eval]

private theorem aliasOfZeroRead (hao : IsAO2 n C) {p : Fin n} {j w : Nat}
    (hj : j < C.gates.length) (hw : w ∈ (gateAt C j).inputs) (hz : Zero C p w) :
    ∃ i < n+j, ∀ (x : Fin n → Bool), x p = false → V C x (n+j) = V C x i := by
  rcases (Slice.ao2_gate_props hao hj).1 with hand | hor
  · exact ⟨p.val,by have := p.isLt; omega,fun x hx => (zeroAnd hao hj hand hw hz x hx).trans
      (by rw [vin,hx])⟩
  · obtain ⟨t,ht,h | h⟩ := inputs_pair hao hj hw <;> refine ⟨t,ht,?_⟩ <;> intro x hx <;>
      rw [vgate hao j hj x, hor, h.1, h.2, hz x hx] <;> simp [GateOp.eval]

private theorem noJointReader (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {k j : Nat} (hk : k < C.gates.length)
    (pk : p.val ∈ (gateAt C k).inputs) (jk : n+j ∈ (gateAt C k).inputs)
    (hz : Zero C p (n+j)) : False := by
  obtain ⟨t,_,h | h⟩ := inputs_pair least.1 hk pk
  all_goals
    have ne : n+j ≠ p.val := by have := p.isLt; omega
    have hin := (Slice.ao2_gate_props least.1 hk).2.1
    rw [hin,h.1,h.2] at jk
    have ht : n+j = t := by simpa [ne] using jk
    subst t
    rcases (Slice.ao2_gate_props least.1 hk).1 with ha | ho
    · apply vseparate G least hk (w := n+j) (least.1.2.1 k hk _ (by rw [hin,h.1,h.2]; simp))
      intro x
      rw [vgate least.1 k hk x,ha,h.1,h.2,vin]
      cases hx : x p with
      | false => rw [hz x hx] <;> rfl
      | true => simp [GateOp.eval]
    · apply vseparate G least hk (w := p.val) (by have := p.isLt; omega)
      intro x
      rw [vgate least.1 k hk x,ho,h.1,h.2,vin]
      cases hx : x p with
      | false => rw [hz x hx] <;> rfl
      | true => simp [GateOp.eval]

noncomputable def direct (C : Circuit) (p : Fin n) : Finset Nat :=
  (Finset.range C.gates.length).filter fun j => p.val ∈ (gateAt C j).inputs

theorem count_direct_plus_one (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n)
    (hpos : ∃ x : Fin n → Bool, x p = false ∧ circuitFun n C x = true)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
      C.eval (List.ofFn (Function.update y p false)))
    (reader : ∃ j < C.gates.length, (gateAt C j).op = .and ∧ p.val ∈ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size + (direct C p).card + 1 ≤ C.size ∧
      ∀ x, circuitFun n D x = circuitFun n C (Function.update x p false) := by
  classical
  obtain ⟨j,hj,hand,hp⟩ := reader
  have hz := zeroAnd least.1 hj hand hp (inputZero p)
  obtain ⟨x,hx,hon⟩ := hpos
  have hout : C.output ≠ n+j := by
    intro eqv
    change V C x C.output = true at hon
    rw [eqv,hz x hx] at hon
    contradiction
  obtain ⟨k,hk,jk⟩ := live G least p hj hout
  have kn : k ∉ direct C p := by
    intro mem
    exact noJointReader G least p hk (Finset.mem_filter.mp mem).2 jk hz
  have aliases (g : Nat) (hg : g ∈ insert k (direct C p)) :
      g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
        V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
    have pack (hgt : g < C.gates.length) (w : Nat) (hw : w ∈ (gateAt C g).inputs)
        (zero : Zero C p w) : g < C.size ∧ ∃ i < n+g, ∀ x : Fin n → Bool,
          V C (Function.update x p false) (n+g) = V C (Function.update x p false) i := by
      obtain ⟨i,hi,he⟩ := aliasOfZeroRead least.1 hgt hw zero
      exact ⟨hgt,i,hi,fun x => he _ (by simp)⟩
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact pack hk _ jk hz
    · obtain ⟨hg,hread⟩ := Finset.mem_filter.mp hg
      exact pack (Finset.mem_range.mp hg) p.val hread (inputZero p)
  obtain ⟨D,hao,hle,hfun⟩ := Slice.compile n C p (insert k (direct C p)) least.1 aliases hnc
  rw [Finset.card_insert_of_notMem kn] at hle
  exact ⟨D,hao,by omega,hfun⟩

end PEqualNP.Outside.L_meta_3568.Reader
namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

variable {n : Nat} {C : Circuit}

noncomputable def directWithOp (C : Circuit) (p : Fin n) (op : GateOp) : Finset Nat := by
  classical
  exact (direct C p).filter fun j => (gateAt C j).op = op

private theorem zerosAtBoth (hao : IsAO2 n C) {p : Fin n} {j : Nat} (hj : j < C.gates.length)
    (h0 : Zero C p (opnd C j 0)) (h1 : Zero C p (opnd C j 1)) : Zero C p (n+j) := by
  intro x hx
  rw [vgate hao j hj x, h0 x hx, h1 x hx]
  rcases (Slice.ao2_gate_props hao hj).1 with h | h <;> rw [h] <;> decide

private theorem orNotZero (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n) {j : Nat} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = .or) (hp : p.val ∈ (gateAt C j).inputs) :
    ¬ Zero C p (n+j) := by
  intro zero
  apply vseparate G least hj (w := p.val) (by have := p.isLt; omega)
  intro x
  cases hx : x p with
  | false => rw [zero x hx,vin,hx]
  | true =>
    obtain ⟨t,_,h | h⟩ := inputs_pair least.1 hj hp <;>
      rw [vgate least.1 j hj x,hor,h.1,h.2,vin,hx] <;> simp [GateOp.eval]

theorem weighted_reader_bound (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (least : IsLeastAO G C) (p : Fin n)
    (hpos : ∃ x : Fin n → Bool, x p = false ∧ circuitFun n C x = true)
    (hnc : ∃ x y : Fin n → Bool, C.eval (List.ofFn (Function.update x p false)) ≠
      C.eval (List.ofFn (Function.update y p false))) :
    ∃ D : Circuit, IsAO2 n D ∧
      D.size + 2 * (directWithOp C p .and).card + (directWithOp C p .or).card ≤ C.size ∧
      ∀ x, circuitFun n D x = circuitFun n C (Function.update x p false) := by
  classical
  let R := Finset.range C.gates.length
  let A := directWithOp C p .and
  let B := directWithOp C p .or
  let K := R.filter fun j => Zero C p (n+j)
  let W := K.image (fun j => n+j)
  let slots (j : Nat) := (gateAt C j).inputs.toFinset ∩ W
  let M := (R \ K).filter fun j => (slots j).Nonempty
  have inK (j : Nat) : j ∈ K ↔ j < C.gates.length ∧ Zero C p (n+j) := by simp [K,R]
  have inA (j : Nat) : j ∈ A ↔ (j < C.gates.length ∧ p.val ∈ (gateAt C j).inputs)
      ∧ (gateAt C j).op = .and := by simp [A,directWithOp,direct]
  have inB (j : Nat) : j ∈ B ↔ (j < C.gates.length ∧ p.val ∈ (gateAt C j).inputs)
      ∧ (gateAt C j).op = .or := by simp [B,directWithOp,direct]
  have inM (j : Nat) : j ∈ M ↔ (j < C.gates.length ∧ j ∉ K) ∧ (slots j).Nonempty := by
    simp [M,R]
  have slot (j w : Nat) : w ∈ slots j ↔ w ∈ (gateAt C j).inputs ∧ w ∈ W := by simp [slots]
  have wzero (w : Nat) (hw : w ∈ W) : Zero C p w := by
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    exact ((inK j).mp hj).2
  have ak : A ⊆ K := by
    intro j hj
    obtain ⟨⟨hr,hp⟩,ha⟩ := (inA j).mp hj
    exact (inK j).mpr ⟨hr,zeroAnd least.1 hr ha hp (inputZero p)⟩
  have nopair (j : Nat) (hj : j < C.gates.length) (hp : p.val ∈ (gateAt C j).inputs) :
      ¬ (slots j).Nonempty := by
    rintro ⟨w,hw⟩
    obtain ⟨hread,hmem⟩ := (slot j w).mp hw
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hmem
    exact noJointReader G least p hj hp hread ((inK g).mp hg).2
  have oneslot (j : Nat) (hj : j ∈ M) : (slots j).card ≤ 1 := by
    obtain ⟨⟨hr,hn⟩,_⟩ := (inM j).mp hj
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hne
    obtain ⟨ar,aw⟩ := (slot j a).mp ha
    obtain ⟨br,bw⟩ := (slot j b).mp hb
    have hi := (Slice.ao2_gate_props least.1 hr).2.1
    simp only [hi,List.mem_cons,List.not_mem_nil,or_false] at ar br
    apply hn
    apply (inK j).mpr
    refine ⟨hr,?_⟩
    rcases ar with ar | ar <;> rcases br with br | br
    · exact (hne (ar.trans br.symm)).elim
    · exact zerosAtBoth least.1 hr (ar ▸ wzero a aw) (br ▸ wzero b bw)
    · exact zerosAtBoth least.1 hr (br ▸ wzero b bw) (ar ▸ wzero a aw)
    · exact (hne (ar.trans br.symm)).elim
  have twoslot (j : Nat) (hj : j ∈ K \ A) : (slots j).card ≤ 2 := by
    have hr := ((inK j).mp (Finset.mem_sdiff.mp hj).1).1
    have hlen := least.1.2.2 _ (Bypass.gateAt_mem hr)
    calc
      _ ≤ (gateAt C j).inputs.toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ (gateAt C j).inputs.length := List.toFinset_card_le _
      _ = 2 := hlen
  have used : W ⊆ ((K \ A) ∪ M).biUnion slots := by
    intro w hw
    obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hr,hz⟩ := (inK g).mp hg
    obtain ⟨x,hx,hon⟩ := hpos
    have hout : C.output ≠ n+g := by
      intro eqv
      change V C x C.output = true at hon
      rw [eqv,hz x hx] at hon
      contradiction
    obtain ⟨j,hj,hread⟩ := live G least p hr hout
    have hs := (slot j (n+g)).mpr ⟨hread,Finset.mem_image_of_mem _ hg⟩
    refine Finset.mem_biUnion.mpr ⟨j,?_,hs⟩
    by_cases jk : j ∈ K
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨jk,?_⟩
      intro ja
      exact nopair j hj (((inA j).mp ja).1.2) ⟨_,hs⟩
    · exact Finset.mem_union_right _ ((inM j).mpr ⟨⟨hj,jk⟩,_,hs⟩)
  have km : Disjoint K M := Finset.disjoint_left.mpr fun j hj hm => ((inM j).mp hm).1.2 hj
  have diffm : Disjoint (K \ A) M :=
    Finset.disjoint_left.mpr fun j hj hm => ((inM j).mp hm).1.2 (Finset.mem_sdiff.mp hj).1
  have limited : W.card ≤ 2*(K \ A).card + M.card := by
    calc
      W.card ≤ _ := Finset.card_le_card used
      _ ≤ ∑ j ∈ ((K \ A) ∪ M), (slots j).card := Finset.card_biUnion_le
      _ = (∑ j ∈ K \ A, (slots j).card) + ∑ j ∈ M, (slots j).card := Finset.sum_union diffm
      _ ≤ (∑ _j ∈ K \ A, 2) + ∑ _j ∈ M, 1 :=
        Nat.add_le_add (Finset.sum_le_sum twoslot) (Finset.sum_le_sum oneslot)
      _ = _ := by simp [Nat.mul_comm]
  have wc : W.card = K.card := Finset.card_image_of_injective _ (by
    intro i j eqv
    change n+i=n+j at eqv
    omega)
  have ka := Finset.card_sdiff_add_card_eq_card ak
  have kb : Disjoint (K ∪ M) B := by
    apply Finset.disjoint_left.mpr
    intro j hj jb
    obtain ⟨⟨hr,hp⟩,ho⟩ := (inB j).mp jb
    rcases Finset.mem_union.mp hj with jk | jm
    · exact orNotZero G least p hr ho hp ((inK j).mp jk).2
    · exact nopair j hr hp ((inM j).mp jm).2
  let S := (K ∪ M) ∪ B
  have sizeS : S.card = K.card + M.card + B.card := by
    dsimp only [S]
    rw [Finset.card_union_of_disjoint kb,Finset.card_union_of_disjoint km]
  have aliases (j : Nat) (hj : j ∈ S) : j < C.size ∧ ∃ i < n+j, ∀ x : Fin n → Bool,
        V C (Function.update x p false) (n+j) = V C (Function.update x p false) i := by
    have pack (hr : j < C.gates.length) (w : Nat) (hw : w ∈ (gateAt C j).inputs)
        (hz : Zero C p w) : j < C.size ∧ ∃ i < n+j, ∀ x : Fin n → Bool,
          V C (Function.update x p false) (n+j) = V C (Function.update x p false) i := by
      obtain ⟨i,hi,he⟩ := aliasOfZeroRead least.1 hr hw hz
      exact ⟨hr,i,hi,fun x => he _ (by simp)⟩
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨hr,hz⟩ := (inK j).mp h
        refine ⟨hr,p.val,by have := p.isLt; omega,?_⟩
        intro x
        rw [hz _ (by simp),vin]
        simp
      · obtain ⟨⟨hr,_⟩,w,hw⟩ := (inM j).mp h
        obtain ⟨hread,hmem⟩ := (slot j w).mp hw
        exact pack hr w hread (wzero _ hmem)
    · obtain ⟨⟨hr,hp⟩,_⟩ := (inB j).mp h
      exact pack hr p.val hp (inputZero p)
  obtain ⟨D,hao,hle,hfun⟩ := Slice.compile n C p S least.1 aliases hnc
  change ∃ D : Circuit, IsAO2 n D ∧ D.size + 2*A.card+B.card ≤ C.size ∧ _
  exact ⟨D,hao,by omega,hfun⟩

end PEqualNP.Outside.L_meta_3568.Reader
namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

variable {n : Nat} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

private theorem delAdj (z a b : Fin n) :
    (G.deleteEdges (G.incidenceSet z)).Adj a b ↔ G.Adj a b ∧ a ≠ z ∧ b ≠ z := by
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨edge,noInc⟩
    refine ⟨edge,?_,?_⟩
    · rintro rfl
      exact noInc ⟨(SimpleGraph.mem_edgeSet G).2 edge,Sym2.mem_mk_left _ _⟩
    · rintro rfl
      exact noInc ⟨(SimpleGraph.mem_edgeSet G).2 edge,Sym2.mem_mk_right _ _⟩
  · rintro ⟨edge,az,bz⟩
    refine ⟨edge,?_⟩
    rintro ⟨_,h⟩
    rcases Sym2.mem_iff.1 h with ha | hb
    · exact az ha.symm
    · exact bz hb.symm

private theorem slice_eq (z : Fin n) (y : Fin n → Bool) :
    graphFun G ∅ (Function.update y z false) =
      @decide (∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b ∧
        y a = true ∧ y b = true) (Classical.propDecidable _) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq,Finset.notMem_empty,false_and,
    exists_false, false_or]
  constructor
  · rintro ⟨a,b,edge,ha,hb⟩
    have az : a ≠ z := by rintro rfl; simp at ha
    have bz : b ≠ z := by rintro rfl; simp at hb
    exact ⟨a,b,(delAdj G z a b).mpr ⟨edge,az,bz⟩,by simpa [Function.update_of_ne az] using ha,
      by simpa [Function.update_of_ne bz] using hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    obtain ⟨ed,az,bz⟩ := (delAdj G z a b).mp edge
    exact ⟨a,b,ed,by simpa [Function.update_of_ne az] using ha,
      by simpa [Function.update_of_ne bz] using hb⟩

theorem delete_weighted (C : Circuit) (least : IsLeastAO G C) (z : Fin n)
    (remain : ∃ u v : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj u v) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a=true ∧ y b=true)
        (Classical.propDecidable _)) ∧
      D.size + 2 * (directWithOp C z .and).card + (directWithOp C z .or).card ≤ C.size := by
  classical
  obtain ⟨u,v,e⟩ := remain
  let on : Fin n → Bool := fun _ => true
  let off : Fin n → Bool := fun _ => false
  have yes : circuitFun n C (Function.update on z false) = true := by
    rw [least.2.1,slice_eq G z on]
    rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
    exact ⟨u,v,e,rfl,rfl⟩
  have no : circuitFun n C (Function.update off z false) = false := by
    rw [least.2.1,slice_eq G z off]
    apply (@decide_eq_false_iff_not _ (Classical.propDecidable _)).mpr
    rintro ⟨a,b,_,ha,_⟩
    cases ha
  obtain ⟨D,hd,bound,works⟩ := weighted_reader_bound G least z
    ⟨Function.update on z false,by simp,yes⟩
    ⟨on,off,by change circuitFun n C _ ≠ circuitFun n C _; rw [yes,no]; decide⟩
  refine ⟨D,hd,?_,bound⟩
  funext x
  rw [works,least.2.1,slice_eq]

end PEqualNP.Outside.L_meta_3568.Reader
namespace PEqualNP.Outside.L_meta_3568.Reader

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

variable {n : Nat}

private theorem pair_true (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  have pair (w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by simp [pairInput]
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pair]
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl ab).elim
    · exact ab
    · exact ab.symm
    · exact (G.irrefl ab).elim
  · intro edge
    exact ⟨u,v,edge,Or.inl rfl,Or.inr rfl⟩

def Fires (C : Circuit) (z u : Fin n) (j : Nat) : Prop :=
  ∀ i ∈ (gateAt C j).inputs, i ≠ z.val → val C (List.ofFn (pairInput u u)) i = true

theorem route_singletons (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hl : IsLeastAO G C) (z : Fin n)
    (only : ∀ j < C.gates.length, z.val ∈ (gateAt C j).inputs → (gateAt C j).op = .and)
    (u : Fin n) (e : G.Adj z u) :
    ∃ j ∈ directWithOp C z .and, Fires C z u j := by
  classical
  have out : C.output ≠ z.val := by
    intro eq
    have yes : circuitFun n C (pairInput z z) = true := by
      rw [circuitFun_val,eq,val_ofFn]
      simp [pairInput]
    rw [hl.2.1] at yes
    exact G.irrefl ((pair_true G z z).mp yes)
  have diff : circuitFun n C (pairInput u u) ≠ circuitFun n C (pairInput z u) := by
    rw [hl.2.1]
    intro eq
    have yes := (pair_true G z u).mpr e
    exact G.irrefl ((pair_true G u u).mp (eq.trans yes))
  obtain ⟨j,hj,hr,fire⟩ := first_reader C hl.1.2.1 z (pairInput u u) (pairInput z u)
    (fun a az => by simp [pairInput,az]) (by simp [pairInput,e.ne]) out diff only
  exact ⟨j,by simp [directWithOp,direct,hj,hr,only j hj hr],fire⟩

theorem singletons_force_multiple (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hl : IsLeastAO G C) (z : Fin n)
    (only : ∀ j < C.gates.length, z.val ∈ (gateAt C j).inputs → (gateAt C j).op = .and)
    (collisionFree : ∀ j ∈ directWithOp C z .and, ∀ u v, G.Adj z u → G.Adj z v →
       Fires C z u j → Fires C z v j → u = v) :
    G.degree z ≤ (directWithOp C z .and).card := by
  classical
  let N := G.neighborFinset z
  have routes (u : Fin n) (h : u ∈ N) := route_singletons G C hl z only u ((G.mem_neighborFinset z u).mp h)
  let reader (u : Fin n) := if h : u ∈ N then Classical.choose (routes u h) else 0
  have chosen (u : Fin n) (h : u ∈ N) : reader u ∈ directWithOp C z .and ∧ Fires C z u (reader u) := by
    simpa only [reader,dif_pos h] using Classical.choose_spec (routes u h)
  apply Finset.card_le_card_of_injOn reader (fun u hu => (chosen u hu).1)
  intro u hu v hv eq
  apply collisionFree (reader u) (chosen u hu).1 u v ((G.mem_neighborFinset z u).mp hu)
    ((G.mem_neighborFinset z v).mp hv) (chosen u hu).2
  rw [eq]
  exact (chosen v hv).2

theorem star_supported_deletion (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hl : IsLeastAO G C) (z : Fin n) (h4 : NoFourCycle G)
    (someAnd : (directWithOp C z .and).Nonempty)
    (only : ∀ j < C.gates.length, z.val ∈ (gateAt C j).inputs → (gateAt C j).op = .and)
    (localStar : ∀ j ∈ directWithOp C z .and, ∃ t : Fin n, t ≠ z ∧
       ∀ u, G.Adj z u → Fires C z u j → G.Adj t u)
    (remain : ∃ a b : Fin n, (G.deleteEdges (G.incidenceSet z)).Adj a b) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = (fun y : Fin n → Bool => @decide (∃ a b : Fin n,
        (G.deleteEdges (G.incidenceSet z)).Adj a b ∧ y a = true ∧ y b = true)
        (Classical.propDecidable _)) ∧ D.size + G.degree z + 1 ≤ C.size := by
  classical
  have cap := singletons_force_multiple G C hl z only (by
    intro j hj u v zu zv fu fv
    obtain ⟨t,tz,adj⟩ := localStar j hj
    let S := Finset.univ.filter fun w => G.Adj z w ∧ G.Adj t w
    have us : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,zu,adj u zu fu⟩
    have vs : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,zv,adj v zv fv⟩
    by_contra ne
    have inc : ({u,v} : Finset (Fin n)) ⊆ S := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl|wv
      · exact us
      · exact Finset.mem_singleton.mp wv ▸ vs
    have low := Finset.card_le_card inc
    have high : S.card ≤ 1 := h4 z t tz.symm
    simp [ne] at low
    omega)
  obtain ⟨D,d,f,size⟩ := delete_weighted G C hl z remain
  have pos := Finset.card_pos.mpr someAnd
  exact ⟨D,d,f,by omega⟩

end PEqualNP.Outside.L_meta_3568.Reader

namespace PEqualNP.Outside.L_meta_3568.Twins.Rename

open PEqualNP.CircuitLowerBounds

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]



end PEqualNP.Outside.L_meta_3568.Twins.Rename
namespace PEqualNP.Outside.L_meta_3568.Twins
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open Rename
variable {n : Nat} (i j : Fin n)

def ref (w : Fin n) : Fin (n+1) := if w=j then Fin.last n else w.castSucc
def fold (x : Fin n→Bool) (w : Fin n) := if w=j then x j || x i else x w
def mergeGate : Gate := ⟨.or,[j.val,i.val]⟩
def lift (C : Circuit) : Circuit :=
  ⟨mergeGate i j :: C.gates.map (relGate n (n+1) (ref j)), wmap n (n+1) (ref j) C.output⟩
theorem length_lift (C : Circuit) : (lift i j C).size=C.size+1 := by simp [Circuit.size,lift]

theorem lookup_old (C : Circuit) (t : ℕ) (hj : t<C.size) :
    gateAt (lift i j C) (t+1) = relGate n (n+1) (ref j) (gateAt C t) := by
  change t<C.gates.length at hj
  simp [lift,gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,hj]

theorem model_lift (C : Circuit) (hm : Monotone2 C) (hb : ReadsBack n C) :
    Monotone2 (lift i j C) ∧ ReadsBack n (lift i j C) := by
  constructor
  · intro g hg
    change g ∈ (mergeGate i j) :: C.gates.map _ at hg
    rcases List.mem_cons.mp hg with rfl|h
    · simp [mergeGate]
    · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp h
      simpa [relGate] using hm t ht
  · intro t hj w hi
    change t < (lift i j C).size at hj
    rw [length_lift] at hj
    cases t with
    | zero =>
      change w ∈ [j.val,i.val] at hi
      rcases (show w=j.val ∨ w=i.val by simpa using hi) with rfl|rfl <;> omega
    | succ t =>
      rw [lookup_old i j _ _ (by omega)] at hi
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
      have back := hb t (by change t<C.size; omega) w hw
      unfold wmap
      split
      · rename_i h
        have := ((ref j) ⟨w,h⟩).isLt
        omega
      · omega

theorem wire_lift (C : Circuit) (x : Fin n → Bool) (wire : ℕ) :
    ((lift i j C).wires (List.ofFn x)).getD (wmap n (n+1) (ref j) wire) false =
      (C.wires (List.ofFn (fold i j x))).getD wire false := by
  let y := x (j) || x i
  have startWire : step (List.ofFn x) (mergeGate i j) = List.ofFn x ++ [y] := by
    simp [step,mergeGate,y,GateOp.eval,List.getD_eq_getElem?_getD]
  have base : Rel n (n+1) (ref j) (List.ofFn (fold i j x)) (List.ofFn x ++ [y]) := by
    refine ⟨by simp,by simp <;> omega,?_⟩
    intro w
    by_cases h : w<n
    · let u : Fin n := ⟨w,h⟩
      have raw : (List.ofFn (fold i j x)).getD w false = fold i j x u := by simp [u,List.getD_eq_getElem?_getD,h]
      rw [raw,show wmap n (n+1) (ref j) w=((ref j) u).val by simp [wmap,h,u]]
      by_cases uc : u=j
      · simp [ref,uc,fold,y,List.getD_eq_getElem?_getD]
      · rw [show ((ref j) u).val=(u).val by simp [ref,uc],List.getD_append _ _ _ _ (by simp)]
        simp [fold,uc,List.getD_eq_getElem?_getD]
    · have newIndex : (List.ofFn x ++ [y]).length ≤ wmap n (n+1) (ref j) w := by
        simp [wmap,h]
      rw [List.getD_eq_default _ _ newIndex,List.getD_eq_default _ _ (by simp <;> omega)]
  have h := (rel_fold n (n+1) (ref j) C.gates _ _ base).2.2 wire
  change ((C.gates.map _).foldl step (step (List.ofFn x) (mergeGate i j))).getD _ false = _
  rw [startWire]
  exact h

theorem exact_lift (C : Circuit) (ao : IsAO2 n C) : IsAO2 n (lift i j C) := by
  have approx : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using ao.1 g hg,(ao.2.2 g hg).le⟩
  obtain ⟨ops,back⟩ := model_lift i j C approx ao.2.1
  refine ⟨fun g hg => by simpa using (ops g hg).1,back,?_⟩
  intro g hg
  change g∈mergeGate i j :: C.gates.map _ at hg
  rcases List.mem_cons.mp hg with rfl|mem
  · rfl
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp mem
    simpa [relGate] using ao.2.2 t ht

theorem graph_fold (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ij : i≠j) (tw : ∀ w,G.Adj i w ↔ G.Adj j w) (x : Fin n→Bool) :
    graphFun G ∅ x = graphFun (G.deleteIncidenceSet i) ∅ (fold i j x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
  have larger (a : Fin n) (ha : x a=true) : fold i j x a=true := by
    by_cases e : a=j
    · subst a; simp [fold,ha]
    · simp [fold,e,ha]
  have raw (a : Fin n) (ha : fold i j x a=true) : x a=true ∨ (a=j ∧ x i=true) := by
    by_cases e : a=j
    · subst a; simpa [fold] using ha
    · exact Or.inl (by simpa [fold,e] using ha)
  constructor
  · rintro ⟨a,b,ab,ha,hb⟩
    by_cases ai : a=i
    · subst a
      exact ⟨j,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨(tw b).mp ab,ij.symm,ab.ne.symm⟩,
        by simp [fold,ha],larger _ hb⟩
    by_cases bi : b=i
    · subst b
      exact ⟨a,j,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨((tw a).mp ab.symm).symm,ab.ne,ij.symm⟩,
        larger _ ha,by simp [fold,hb]⟩
    exact ⟨a,b,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨ab,ai,bi⟩,larger _ ha,larger _ hb⟩
  · rintro ⟨a,b,edge,ha,hb⟩
    have ab := (SimpleGraph.deleteIncidenceSet_adj.mp edge).1
    rcases raw a ha with h|⟨rfl,h⟩ <;> rcases raw b hb with k|⟨rfl,k⟩
    · exact ⟨a,b,ab,h,k⟩
    · exact ⟨a,i,((tw a).mpr ab.symm).symm,h,k⟩
    · exact ⟨i,b,(tw b).mpr ab,h,k⟩
    · exact (G.irrefl ab).elim

theorem restore_twin (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ij : i≠j) (tw : ∀ w,G.Adj i w ↔ G.Adj j w) (D : Circuit) (ao : IsAO2 n D)
    (de : circuitFun n D=graphFun (G.deleteIncidenceSet i) ∅) :
    IsAO2 n (lift i j D) ∧ circuitFun n (lift i j D)=graphFun G ∅ ∧
      (lift i j D).size=D.size+1 := by
  refine ⟨exact_lift i j D ao,?_,length_lift i j D⟩
  funext x
  exact (wire_lift i j D x D.output).trans ((congrFun de _).trans (graph_fold i j G ij tw x).symm)

theorem twin_readers (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ij : i≠j)
    (tw : ∀ w,G.Adj i w ↔ G.Adj j w) (active : ∃ p,G.Adj i p)
    (C : Circuit) (least : IsLeastAO G C) :
    (Reader.directWithOp C i .and).card=0 ∧ (Reader.directWithOp C i .or).card≤1 := by
  classical
  obtain ⟨p,ip⟩ := active
  have jp := (tw p).mp ip
  have far : ∃ a b,(G.deleteEdges (G.incidenceSet i)).Adj a b :=
    ⟨j,p,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨jp,ij.symm,ip.ne.symm⟩⟩
  obtain ⟨D,ao,eq,cost⟩ := Reader.delete_weighted G C least i far
  have de : circuitFun n D=graphFun (G.deleteIncidenceSet i) ∅ := by
    funext x
    rw [congrFun eq x]
    apply Bool.eq_iff_iff.mpr
    simp only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,decide_eq_true_eq]
    rfl
  obtain ⟨la,leq,ls⟩ := restore_twin i j G ij tw D ao de
  have bound := least.2.2 _ la leq
  omega

end PEqualNP.Outside.L_meta_3568.Twins

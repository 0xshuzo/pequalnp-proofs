import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9792.Compare

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## Core: strict binary DAGs, evaluation, and the shared definitions -/

/-- Gate operation: `true` is AND, `false` is OR. -/
def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

/-- A binary DAG: gate `j` is `(isAnd, a, b)` and, with `n` inputs, drives wire `n + j`. -/
abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

/-- One evaluation step: append the value of gate `g` read on the current wire list. -/
def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

/-- The wire list of `D` started from the wire list `w`. -/
def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

/-- Value of wire `w` of `D` on input `x` (`false` beyond the last wire). -/
def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

/-- Strict binary DAG on `n` inputs: both operands are earlier wires and they differ. -/
def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

/-- The gates reading wire `w`. -/
def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

/-- Every wire except the last one has a reader. -/
def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

/-- Strict, live, nonempty; the output is the last wire `n + D.length - 1`. -/
def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

/-- The output wire. -/
def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

/-- Singleton assignment. -/
def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

/-- Singleton support of a wire. -/
def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

/-- Surplus carried by a set of wires. -/
def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

/-- The wires other than the output. -/
def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

/-- Branching wires. -/
def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

/-- Eligible labels: carried by some branching wire. -/
def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

/-- Multiplicity-aware surplus units `⟨w, i⟩` with `i + 1 < fanout w`. -/
def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

/-- Arcs are operand positions `(gate, side)`; `false` is the first operand. -/
def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

/-- Union carrier of a label set `T`. -/
def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

/-- Difference carrier: wires carrying `x` and not `y`. -/
def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

/-- A choice of one pure branching carrier for every eligible label. -/
def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

/-! ### Evaluation lemmas -/

theorem tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

theorem wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

theorem getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

/-- The value of the gate `j` wire in terms of the wire list of the first `j` gates. -/
theorem wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

/-- Wires of an initial segment agree with the full wire list below its length. -/
theorem wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

theorem val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

/-- Values of an initial segment of a DAG. -/
theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

/-- The gate equation of a strict DAG. -/
theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

/-- A strict DAG has exactly one solution of its input and gate equations. -/
theorem val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]

/-! ## Block A: official Monotone2 circuits to strict live binary DAGs -/

/-- Symbolic reference: a Boolean constant or an emitted wire index. -/
abbrev Ref := Bool ⊕ ℕ

/-- Value of a symbolic reference on a wire list. -/
def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

/-- Stage-dependent lookup: an index not yet mapped reads constant false. -/
def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

/-- Two-operand simplifier: a reference, or two distinct emitted wires needing a gate. -/
def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

/-- One translation step for an official gate; the state is (map of old wires, emitted DAG). -/
def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

/-- A reference is valid below the bound `B`. -/
def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

/-- Structural invariant of the translation state. -/
def na_Good (n : ℕ) (st : List Ref × Dag) : Prop :=
  Strict n st.2 ∧ ∀ r ∈ st.1, na_ok (n + st.2.length) r

theorem na_ok_mono {B B' : ℕ} (h : B ≤ B') (r : Ref) (hr : na_ok B r) : na_ok B' r := by
  rcases r with b | k
  · trivial
  · exact lt_of_lt_of_le hr h

theorem na_look_val (W : List Bool) (m : List Ref) (i : ℕ) :
    refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
  simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases m[i]? <;> rfl

theorem na_look_ok (B : ℕ) (m : List Ref) (hm : ∀ r ∈ m, na_ok B r) (i : ℕ) :
    na_ok B (na_look m i) := by
  simp only [na_look, List.getD_eq_getElem?_getD]
  rcases h : m[i]? with _ | r
  · trivial
  · exact hm r (List.mem_of_getElem? h)

theorem na_refVal_wstep (W : List Bool) (g : Bool × ℕ × ℕ) (r : Ref) (hr : na_ok W.length r) :
    refVal (wstep W g) r = refVal W r := by
  rcases r with b | k
  · rfl
  · exact wstep_getD_lt W g k hr

theorem na_comb_inl (t : Bool) (W : List Bool) (a b r : Ref) (h : na_comb t a b = Sum.inl r) :
    refVal W r = gop t (refVal W a) (refVal W b) := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h
    cases t <;> cases a <;> simp [refVal]
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h
      cases t <;> cases b <;> simp [refVal]
    · simp only [na_comb] at h
      split_ifs at h with hij
      simp only [Sum.inl.injEq] at h
      subst h; subst hij
      cases t <;> simp [refVal]

theorem na_comb_ok (B : ℕ) (t : Bool) (a b r : Ref) (ha : na_ok B a) (hb : na_ok B b)
    (h : na_comb t a b = Sum.inl r) : na_ok B r := by
  rcases a with a | i
  · simp only [na_comb, Sum.inl.injEq] at h
    subst h; split_ifs
    · exact hb
    · trivial
  · rcases b with b | j
    · simp only [na_comb, Sum.inl.injEq] at h
      subst h; split_ifs
      · exact ha
      · trivial
    · simp only [na_comb] at h
      split_ifs at h
      simp only [Sum.inl.injEq] at h
      subst h; exact ha

theorem na_comb_inr (t : Bool) (a b : Ref) (p : ℕ × ℕ) (h : na_comb t a b = Sum.inr p) :
    a = Sum.inr p.1 ∧ b = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
  rcases a with a | i
  · simp [na_comb] at h
  · rcases b with b | j
    · simp [na_comb] at h
    · simp only [na_comb] at h
      split_ifs at h with hij
      cases h
      exact ⟨rfl, rfl, hij⟩

theorem na_eval0 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    op.eval [] = na_isAnd op := by
  rcases hop with rfl | rfl <;> rfl

theorem na_eval1 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (u : Bool) :
    op.eval [u] = u := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval]

theorem na_eval2 (op : GateOp) (hop : op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (u v : Bool) : op.eval [u, v] = gop (na_isAnd op) u v := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, na_isAnd]

theorem na_getD_append_lt (D E : Dag) (k : ℕ) (h : k < D.length) :
    (D ++ E).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem na_getD_snoc (D : Dag) (g : Bool × ℕ × ℕ) :
    (D ++ [g]).getD D.length (false, 0, 0) = g := by
  simp [List.getD_eq_getElem?_getD]

theorem na_strict_snoc {n : ℕ} {D : Dag} (hS : Strict n D) (t : Bool) (i j : ℕ)
    (hi : i < n + D.length) (hj : j < n + D.length) (hij : i ≠ j) :
    Strict n (D ++ [(t, i, j)]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  by_cases hk' : k < D.length
  · simp only [opA, opB, na_getD_append_lt D _ k hk']
    exact hS k hk'
  · have hkD : k = D.length := by omega
    subst hkD
    simp only [opA, opB, na_getD_snoc]
    exact ⟨hi, hj, hij⟩

theorem na_strict_take {n : ℕ} {D : Dag} (hS : Strict n D) (k : ℕ) : Strict n (D.take k) := by
  intro j hj
  simp only [List.length_take] at hj
  have hj1 : j < k := by omega
  have hj2 : j < D.length := by omega
  have e : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
    simp [List.getD_eq_getElem?_getD, hj1]
  simp only [opA, opB, e]
  exact hS j hj2

/-- One step keeps the invariant, emits at most one gate, and tracks the official fold. -/
theorem na_step_spec (n : ℕ) (st : List Ref × Dag) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : na_Good n st) :
    na_Good n (na_step n st g) ∧ (na_step n st g).2.length ≤ st.2.length + 1 ∧
    ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
      (na_step n st g).1.map (refVal (wl (na_step n st g).2 (List.ofFn x))) =
        w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
  obtain ⟨m, D⟩ := st
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  obtain ⟨hS, hok⟩ := h
  dsimp only at hS hok hop hlen ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · trivial
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, na_eval0 op hop]
  · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
    · intro r hr
      simp only [na_step, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hok r hr
      · exact na_look_ok _ m hok a
    · subst hw
      simp only [na_step, List.map_append, List.map_cons, List.map_nil, na_eval1 op hop,
        na_look_val]
  · have hla := na_look_ok _ m hok a
    have hlb := na_look_ok _ m hok b
    rcases hc : na_comb (na_isAnd op) (na_look m a) (na_look m b) with r | p
    · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact hok r' hr
        · exact na_comb_ok _ _ _ _ _ hla hlb hc
      · subst hw
        simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, na_eval2 op hop,
          na_comb_inl _ (wl D (List.ofFn x)) _ _ _ hc, na_look_val]
    · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
      rw [ea] at hla
      rw [eb] at hlb
      have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
      refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
        fun x w hw => ?_⟩
      · intro r' hr
        simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
          List.length_singleton] at hr ⊢
        rcases hr with hr | rfl
        · exact na_ok_mono (by omega) r' (hok r' hr)
        · show n + D.length < n + (D.length + 1)
          omega
      · subst hw
        have hWlen : (wl D (List.ofFn x)).length = n + D.length := by
          rw [wl_length, List.length_ofFn]
        have hW' : wl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
            wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
          rw [wl_append]; rfl
        have h1 : m.map (refVal (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
            m.map (refVal (wl D (List.ofFn x))) :=
          List.map_congr_left (fun r hr => na_refVal_wstep _ _ r (by rw [hWlen]; exact hok r hr))
        have h2 : (wstep (wl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (n + D.length) false =
            gop (na_isAnd op) ((m.map (refVal (wl D (List.ofFn x)))).getD a false)
              ((m.map (refVal (wl D (List.ofFn x)))).getD b false) := by
          rw [← hWlen, wstep_getD_last, ← na_look_val, ← na_look_val, ea, eb]; rfl
        simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
          h2, na_eval2 op hop]
  · simp at hlen

/-- The whole translation fold keeps the invariant and tracks the official wire list. -/
theorem na_fold_spec (n : ℕ) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ st : List Ref × Dag, na_Good n st →
      na_Good n (gs.foldl (na_step n) st) ∧
      (gs.foldl (na_step n) st).2.length ≤ st.2.length + gs.length ∧
      ∀ (x : Fin n → Bool) (w : List Bool), st.1.map (refVal (wl st.2 (List.ofFn x))) = w →
        (gs.foldl (na_step n) st).1.map
            (refVal (wl (gs.foldl (na_step n) st).2 (List.ofFn x))) =
          gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs with
  | nil => intro st h; exact ⟨h, by simp, fun x w hw => hw⟩
  | cons g gs ih =>
    intro st h
    obtain ⟨h1, h2, h3⟩ := na_step_spec n st g (hgs g (by simp)) h
    obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
    refine ⟨i1, ?_, fun x w hw => ?_⟩
    · simp only [List.foldl_cons, List.length_cons]; omega
    · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)

theorem na_init (n : ℕ) (x : Fin n → Bool) :
    ((List.range n).map Sum.inr).map (refVal (wl ([] : Dag) (List.ofFn x))) = List.ofFn x := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [refVal, wl, List.getD_eq_getElem?_getD, h1]


def freeReaders (v : Nat) (gs : List Gate) : Nat :=
  (gs.filter (fun g => g.inputs.contains v)).length

theorem stepCons (n : Nat) (st : List Ref × Dag) (g : Gate) :
    ∃r, (na_step n st g).1 = st.1 ++ [r] := by
  rcases g with ⟨o,l⟩
  cases l with
  | nil => exact ⟨_,rfl⟩
  | cons a l =>
    cases l with
    | nil => exact ⟨_,rfl⟩
    | cons b tail =>
      cases he : na_comb (na_isAnd o) (na_look st.1 a) (na_look st.1 b) <;>
        simp [na_step,he]

theorem freeStep (n : Nat) (st : List Ref × Dag) (g : Gate) (v : Nat)
    (fv : na_look st.1 v=Sum.inl false) (use : v∈g.inputs) (len : g.inputs.length≤2) :
    (na_step n st g).2 = st.2 := by
  rcases g with ⟨o,l⟩
  change v∈l at use
  change l.length≤2 at len
  cases l with
  | nil => simp at use
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l =>
      cases l with
      | cons c rest => simp at len
      | nil =>
        rcases List.mem_cons.mp use with rfl|hb
        · simp [na_step,fv,na_comb]
        · have eq : v=b := by simpa using hb
          subst b
          cases h : na_look st.1 a <;> simp [na_step,fv,na_comb,h]

theorem mappedArity (n : Nat) (gs : List Gate) (st : List Ref × Dag) :
    (gs.foldl (na_step n) st).1.length = st.1.length+gs.length := by
  induction gs generalizing st with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨r,e⟩ := stepCons n st g
    simp [List.foldl_cons,ih,e,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem priceFold (n v : Nat) (gs : List Gate)
    (legal : ∀g∈gs, g.op∈({GateOp.and, GateOp.or}:Set GateOp) ∧ g.inputs.length≤2)
    (st : List Ref × Dag) (good : na_Good n st)
    (prior : v<st.1.length) (fv : na_look st.1 v=Sum.inl false) :
    (gs.foldl (na_step n) st).2.length+freeReaders v gs ≤ st.2.length+gs.length := by
  induction gs generalizing st with
  | nil => simp [freeReaders]
  | cons g gs ih =>
    obtain ⟨good',step,_⟩ := na_step_spec n st g (legal g List.mem_cons_self) good
    obtain ⟨r,e⟩ := stepCons n st g
    have pv : v<(na_step n st g).1.length := by rw [e,List.length_append];omega
    have f' : na_look (na_step n st g).1 v=Sum.inl false := by
      simpa only [na_look,e,List.getD_eq_getElem?_getD,List.getElem?_append_left prior] using fv
    have tail := ih (fun g hg => legal g (List.mem_cons_of_mem _ hg)) _ good' pv f'
    by_cases use : v∈g.inputs
    · have fr := freeStep n st g v fv use (legal g List.mem_cons_self).2
      rw [fr] at tail
      have on : g.inputs.contains v=true := by simpa using use
      have hcount : freeReaders v (g::gs)=freeReaders v gs+1 := by
        unfold freeReaders
        rw [List.filter_cons]
        simp [on,use]
      simp only [List.foldl_cons,hcount,List.length_cons]
      omega
    · have off : ¬g.inputs.contains v=true := by simpa using use
      have hcount : freeReaders v (g::gs)=freeReaders v gs := by
        unfold freeReaders
        rw [List.filter_cons]
        simp [off,use]
      simp only [List.foldl_cons,hcount,List.length_cons]
      omega

def muted (pre post : List Gate) (out : Nat) : Circuit := ⟨pre ++ (⟨.or,[]⟩ :: post),out⟩

theorem clampedPrice (n : Nat) (pre post : List Gate) (out : Nat)
    (legal : Monotone2 (muted pre post out)) :
    ∃ D : Dag, ∃ q : Ref, Strict n D ∧
      D.length + freeReaders (n+pre.length) post ≤ pre.length+post.length ∧
      ∀x : Fin n → Bool, (muted pre post out).eval (List.ofFn x)=refVal (wl D (List.ofFn x)) q := by
  let ini : List Ref × Dag := ((List.range n).map Sum.inr,[])
  have initial : na_Good n ini := by
    refine ⟨fun j hj => absurd hj (by simp [ini]),fun r hr => ?_⟩
    simp only [ini,List.mem_map,List.mem_range] at hr
    obtain ⟨k,hk,rfl⟩ := hr
    simpa [ini,na_ok] using hk
  let s := pre.foldl (na_step n) ini
  let h := na_step n s ⟨.or,[]⟩
  let t := post.foldl (na_step n) h
  have pg (g : Gate) (hg : g∈pre) := legal g (List.mem_append_left _ hg)
  have qg (g : Gate) (hg : g∈post) := legal g (List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  obtain ⟨good,budget,sem⟩ := na_fold_spec n pre pg ini initial
  have sl : s.1.length=n+pre.length := by simpa [s,ini] using mappedArity n pre ini
  have zeroLegal : (GateOp.or∈({GateOp.and,GateOp.or}:Set GateOp)) ∧ ([] : List Nat).length≤2 := by simp
  have g' := (na_step_spec n s ⟨.or,[]⟩ zeroLegal good).1
  have inside : n+pre.length<h.1.length := by simp [h,na_step,sl]
  have zero : na_look h.1 (n+pre.length)=Sum.inl false := by
    rw [←sl]
    simp [h,na_step,na_look,List.getD_eq_getElem?_getD,na_isAnd]
  have sz := priceFold n (n+pre.length) post qg h g' inside zero
  have hlen : h.2.length=s.2.length := rfl
  change s.2.length≤0+pre.length at budget
  change t.2.length+freeReaders (n+pre.length) post≤h.2.length+post.length at sz
  have full : (muted pre post out).gates.foldl (na_step n) ini=t := by
    simp only [muted,List.foldl_append,List.foldl_cons];rfl
  obtain ⟨ag,_,track⟩ := na_fold_spec n (muted pre post out).gates legal ini initial
  rw [full] at ag track
  refine ⟨t.2,na_look t.1 out,ag.1,by omega,?_⟩
  intro x
  rw [na_look_val,track x (List.ofFn x) (na_init n x)]
  rfl

def matGate (g : Bool × Nat × Nat) : Gate :=
  ⟨if g.1 then .and else .or,[g.2.1,g.2.2]⟩
def materialize (D : Dag) (k : Nat) : Circuit := ⟨D.map matGate,k⟩

theorem matLegal (D : Dag) (k : Nat) : Monotone2 (materialize D k) := by
  intro g hg
  obtain ⟨⟨t,a,b⟩,_,rfl⟩ := List.mem_map.mp hg
  cases t <;> simp [matGate]

theorem matWires (D : Dag) (k : Nat) (w : List Bool) :
    (materialize D k).wires w=wl D w := by
  induction D generalizing w with
  | nil => rfl
  | cons g ds ih =>
    rcases g with ⟨t,a,b⟩
    change (materialize ds k).wires (w ++ [(matGate (t,a,b)).op.eval
      ((matGate (t,a,b)).inputs.map (fun i => w.getD i false))])=wl ds (wstep w (t,a,b))
    rw [ih]
    cases t <;> simp [matGate,GateOp.eval,wstep]

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]
theorem W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega
theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]
theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h
def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true
theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩
theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (W gs x) (W gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (W gs x).length = (W gs y).length := by simp [W_length, hl]
    rw [W_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (W gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (W gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht
def original (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  ⟨pre++(g::post),out⟩
def value (pre : List Gate) (g : Gate) (x : List Bool) :=
  g.op.eval (g.inputs.map fun i => (W pre x).getD i false)
def after (pre post : List Gate) (out : Nat) (x : List Bool) (v : Bool) :=
  (W post (W pre x++[v])).getD out false

theorem origSplit (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) (x : List Bool) :
    (original pre g post out).eval x=after pre post out x (value pre g x) := by
  simp only [original,Circuit.eval,Circuit.wires,after,W,value,List.foldl_append,List.foldl_cons]

theorem mutedSplit (pre post : List Gate) (out : Nat) (x : List Bool) :
    (muted pre post out).eval x=after pre post out x false := by
  simp only [muted,Circuit.eval,Circuit.wires,after,W,List.foldl_append,List.foldl_cons]
  rfl

theorem protectedWire (gs : List Gate) (w : List Bool) (i : Nat) (small : i<w.length) :
    (W gs w).getD i false=w.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g h =>
    rw [W_snoc,getD_snoc,if_pos (by rw [W_length]; omega),h]

def rewire (n : Nat) (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat) : Circuit :=
  let k := n+pre.length+1+post.length
  muted pre (post++[g,⟨.or,[out,k]⟩]) (k+1)

theorem rewireLegal (n : Nat) (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ok : Monotone2 (original pre g post out)) : Monotone2 (rewire n pre g post out) := by
  intro a ha
  change a∈pre++(_::(post++[g,_])) at ha
  rcases List.mem_append.mp ha with h|h
  · exact ok _ (List.mem_append_left _ h)
  · rcases List.mem_cons.mp h with rfl|h
    · simp
    · rcases List.mem_append.mp h with h|h
      · exact ok _ (List.mem_append_right _ (List.mem_cons_of_mem _ h))
      · rcases List.mem_cons.mp h with rfl|h
        · exact ok _ (List.mem_append_right _ List.mem_cons_self)
        · obtain rfl := List.mem_singleton.mp h
          simp

theorem rewireEval {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀i∈g.inputs,i<n+pre.length) (output : out<n+pre.length+1+post.length)
    (x : Fin n → Bool) :
    (rewire n pre g post out).eval (List.ofFn x) =
      (after pre post out (List.ofFn x) false || value pre g (List.ofFn x)) := by
  let w := W pre (List.ofFn x)
  let z := W post (w++[false])
  let k := n+pre.length+1+post.length
  have wlen : w.length=n+pre.length := by simp [w,W_length]
  have zlen : z.length=k := by simp [z,k,W_length,wlen,Nat.add_assoc]
  have atRead (i) (hi : i∈g.inputs) : z.getD i false=w.getD i false := by
    have sm : i<w.length := wlen.symm ▸ ordered i hi
    rw [show z=W post (w++[false]) from rfl,protectedWire _ _ _ (by simp;omega),getD_snoc,if_pos sm]
  have same : g.inputs.map (fun i => z.getD i false)=g.inputs.map (fun i => w.getD i false) :=
    List.map_congr_left atRead
  have folded : (rewire n pre g post out).eval (List.ofFn x)=
      (W [g,⟨.or,[out,k]⟩] z).getD (k+1) false := by
    simp [rewire,muted,Circuit.eval,Circuit.wires,W,z,w,k,List.foldl_append,GateOp.eval]
  rw [folded]
  let v := g.op.eval (g.inputs.map fun i => z.getD i false)
  change (((z++[v])++[GateOp.or.eval ([out,k].map fun i => (z++[v]).getD i false)])).getD (k+1) false = _
  have small : out<z.length := by simpa [zlen,k] using output
  rw [getD_snoc,if_neg (by simp [zlen]),if_pos (by simp [zlen])]
  simp only [List.map_cons,List.map_nil,GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false]
  rw [getD_snoc,if_pos small,getD_snoc,if_neg (by omega),if_pos (by omega)]
  change (z.getD out false || g.op.eval (g.inputs.map fun i => z.getD i false))=_
  rw [same]
  rfl

theorem semanticCut {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ok : Monotone2 (original pre g post out))
    (safe : ∀x : Fin n → Bool, value pre g (List.ofFn x)=true →
       (original pre g post out).eval (List.ofFn x)=true)
    (x : Fin n → Bool) :
      (after pre post out (List.ofFn x) false || value pre g (List.ofFn x)) =
        (original pre g post out).eval (List.ofFn x) := by
  cases h : value pre g (List.ofFn x) with
  | false => simp [origSplit,h]
  | true => simp [safe x h]


theorem preserveReaders {n : Nat} (pre : List Gate) (g : Gate) (post : List Gate) (out : Nat)
    (ordered : ∀i∈g.inputs,i<n+pre.length) (output : out<n+pre.length+1+post.length)
    (least : IsMinimalMonoCircuit n (original pre g post out))
    (vary : ∃x y : Fin n → Bool, (original pre g post out).eval (List.ofFn x) ≠
      (original pre g post out).eval (List.ofFn y))
    (safe : ∀x : Fin n → Bool, value pre g (List.ofFn x)=true →
       (original pre g post out).eval (List.ofFn x)=true) :
      freeReaders (n+pre.length) post ≤ 1 := by
  let k := n+pre.length+1+post.length
  let tail := post++[g,⟨.or,[out,k]⟩]
  have legal : Monotone2 (muted pre tail (k+1)) := rewireLegal n pre g post out least.1
  obtain ⟨D,q,_,price,calcD⟩ := clampedPrice n pre tail (k+1) legal
  have compute (x : Fin n → Bool) : (original pre g post out).eval (List.ofFn x) =
      refVal (wl D (List.ofFn x)) q := by
    exact ((semanticCut pre g post out least.1 safe x).symm.trans
      (rewireEval pre g post out ordered output x).symm).trans (calcD x)
  have cost : freeReaders (n+pre.length) post ≤ freeReaders (n+pre.length) tail := by
    simp [freeReaders,tail,List.filter_append]
  rcases q with c|w
  · obtain ⟨x,y,h⟩ := vary
    exact (h ((compute x).trans (compute y).symm)).elim
  · have same : circuitFun n (materialize D w) = circuitFun n (original pre g post out) := by
      funext x
      change ((materialize D w).wires (List.ofFn x)).getD w false=_
      rw [matWires]
      exact (compute x).symm
    have bound := least.2 _ (matLegal D w) same
    change (pre++(g::post)).length ≤ (D.map matGate).length at bound
    simp only [List.length_map,List.length_append,List.length_cons] at bound
    have len : tail.length=post.length+2 := by simp [tail]
    omega

end PEqualNP.Outside.L_meta_9792.Compare

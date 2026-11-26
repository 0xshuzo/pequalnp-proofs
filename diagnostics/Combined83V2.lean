import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_971_aux

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

/-- Translation: a constant, an input projection, or a strict DAG no larger than `C`. -/
theorem exists_strict_of_monotone2 {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    (∃ b : Bool, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = b) ∨
    (∃ i : Fin n, ∀ x : Fin n → Bool, C.eval (List.ofFn x) = x i) ∨
    (∃ D : Dag, Strict n D ∧ D ≠ [] ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x)) := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hmono _ h0
  generalize C.gates.foldl (na_step n) ((List.range n).map Sum.inr, ([] : Dag)) = st
    at hS hok hlen hsem
  obtain ⟨m, D⟩ := st
  dsimp only at hS hok hlen hsem
  have hev : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = refVal (wl D (List.ofFn x)) (na_look m C.output) := by
    intro x
    rw [na_look_val, hsem x (List.ofFn x) (na_init n x)]
    rfl
  have hk := na_look_ok _ m hok C.output
  rcases hr : na_look m C.output with b | k
  · exact Or.inl ⟨b, fun x => by rw [hev x, hr]; rfl⟩
  · rw [hr] at hk
    have hk' : k < n + D.length := hk
    by_cases hkn : k < n
    · exact Or.inr (Or.inl ⟨⟨k, hkn⟩, fun x => by rw [hev x, hr]; exact val_input D x k hkn⟩)
    · have hl : (D.take (k - n + 1)).length = k - n + 1 := by
        rw [List.length_take]; omega
      refine Or.inr (Or.inr ⟨D.take (k - n + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩)
      · intro h
        rw [h] at hl
        simp at hl
      · rw [hl]
        simp only [List.length_nil, Nat.zero_add] at hlen
        unfold Circuit.size
        omega
      · have ho : outW n (D.take (k - n + 1)) = k := by unfold outW; rw [hl]; omega
        rw [ho, val_take D x (k - n + 1) k (by omega) (by omega), hev x, hr]
        rfl

theorem na_no_reader {D : Dag} {w : ℕ} (h : fanout D w = 0) (j : ℕ) (hj : j < D.length) :
    opA D j ≠ w ∧ opB D j ≠ w := by
  unfold fanout readers at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  have := h (Finset.mem_range.mpr hj)
  tauto

/-- Shift an operand index down past a deleted wire `c`. -/
def na_sh (c a : ℕ) : ℕ := if c < a then a - 1 else a

/-- Inverse shift: the old index of a new wire or gate. -/
def na_up (c w : ℕ) : ℕ := if w < c then w else w + 1

/-- Delete gate `j` and shift larger operand indices down by one. -/
def na_del (n j : ℕ) (D : Dag) : Dag :=
  (D.eraseIdx j).map (fun g => (g.1, na_sh (n + j) g.2.1, na_sh (n + j) g.2.2))

theorem na_del_length (n j : ℕ) (D : Dag) (hj : j < D.length) :
    (na_del n j D).length = D.length - 1 := by
  simp [na_del, List.length_eraseIdx, hj]

theorem na_del_ops (n j : ℕ) (D : Dag) (k : ℕ) (hk : na_up j k < D.length) :
    tag (na_del n j D) k = tag D (na_up j k) ∧
    opA (na_del n j D) k = na_sh (n + j) (opA D (na_up j k)) ∧
    opB (na_del n j D) k = na_sh (n + j) (opB D (na_up j k)) := by
  have e : (na_del n j D).getD k (false, 0, 0) =
      ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
        na_sh (n + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
    simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
    unfold na_up at hk ⊢
    split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
  unfold tag opA opB
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

theorem na_del_strict {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) : Strict n (na_del n j D) := by
  intro k hk
  rw [na_del_length n j D hj] at hk
  have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
  have hk2 : (k < j ∧ na_up j k = k) ∨ (j ≤ k ∧ na_up j k = k + 1) := by
    unfold na_up; split_ifs <;> omega
  obtain ⟨ha, hb, hab⟩ := hS _ hk'
  obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
  obtain ⟨-, ea, eb⟩ := na_del_ops n j D k hk'
  rw [ea, eb]
  generalize na_up j k = k' at *
  generalize opA D k' = a at *
  generalize opB D k' = b at *
  refine ⟨?_, ?_, ?_⟩ <;> unfold na_sh <;> split_ifs <;> omega

theorem na_del_val {n : ℕ} {D : Dag} (hS : Strict n D) (j : ℕ) (hj : j < D.length)
    (hf : fanout D (n + j) = 0) (x : Fin n → Bool) (w : ℕ) (hw : w < n + (D.length - 1)) :
    val (na_del n j D) x w = val D x (na_up (n + j) w) := by
  refine val_unique (na_del_strict hS j hj hf) x (fun u => val D x (na_up (n + j) u))
    (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length n j D hj]; exact hw)
  · have e : na_up (n + j) i = i := by unfold na_up; split_ifs <;> omega
    show val D x (na_up (n + j) i) = x ⟨i, hi⟩
    rw [e]; exact val_input D x i hi
  · rw [na_del_length n j D hj] at hk
    have hk' : na_up j k < D.length := by unfold na_up; split_ifs <;> omega
    obtain ⟨et, ea, eb⟩ := na_del_ops n j D k hk'
    obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
    have e1 : na_up (n + j) (n + k) = n + na_up j k := by unfold na_up; split_ifs <;> omega
    have e2 : ∀ a, a ≠ n + j → na_up (n + j) (na_sh (n + j) a) = a := by
      intro a ha; unfold na_up na_sh; split_ifs <;> omega
    show val D x (na_up (n + j) (n + k)) = gop (tag (na_del n j D) k)
      (val D x (na_up (n + j) (opA (na_del n j D) k)))
      (val D x (na_up (n + j) (opB (na_del n j D) k)))
    rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
    exact val_gate hS x _ hk'

theorem na_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, hD⟩
    · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < n + D.length ∧ fanout D w = 0 := by
        by_contra hcon
        exact hL (fun w hw => by
          by_contra h0
          exact hcon ⟨w, hw, by omega⟩)
      by_cases hwn : w < n
      · exfalso
        obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
        apply hFne
        rw [← hD x, ← hD y]
        have hout : outW n D ≠ w := by unfold outW; omega
        have key := val_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else val D x u)
          (fun i hi => by
            by_cases hiw : i = w
            · subst hiw; simp
            · simp only [hiw, ite_false]
              rw [val_input D x i hi]
              exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
          (fun j hj => by
            obtain ⟨ha, hb⟩ := na_no_reader hf0 j hj
            have hnj : n + j ≠ w := by omega
            simp only [hnj, ha, hb, ite_false]
            exact val_gate hS x j hj)
          (outW n D) (by unfold outW; omega)
        simp only [hout, ite_false] at key
        exact key.symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        have hl := na_del_length n j D hj
        obtain ⟨D', h1, h2, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, h3⟩

/-- Liveness by minimality: a strict DAG for a function with all inputs essential can be
replaced by a strict live one that is no larger. -/
theorem exists_strictLive_of_strict {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y)
    (D : Dag) (hS : Strict n D) (hne : D ≠ [])
    (hD : ∀ x : Fin n → Bool, val D x (outW n D) = F x) :
    ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ D.length ∧
      ∀ x : Fin n → Bool, val D' x (outW n D') = F x :=
  na_live_aux F hess D.length D rfl hS hne hD

/-- The bridge from the official model to strict live binary DAGs. -/
theorem normalize_strictLive {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
      C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Dag, StrictLive n D ∧ D.length ≤ C.size ∧
      ∀ x : Fin n → Bool, val D x (outW n D) = C.eval (List.ofFn x) := by
  rcases exists_strict_of_monotone2 (n := n) C hmono with
    ⟨b, hb⟩ | ⟨i, hi⟩ | ⟨D, hS, hne, hlen, hD⟩
  · obtain ⟨x, hx⟩ := hnc b
    exact absurd (hb x) hx
  · obtain ⟨x, hx⟩ := hnp i
    exact absurd (hi x) hx
  · obtain ⟨D', h1, h2, h3⟩ :=
      exists_strictLive_of_strict (fun x => C.eval (List.ofFn x)) hess D hS hne hD
    exact ⟨D', h1, by omega, h3⟩

/-! ## Block B: surplus identity, supports, carrier flow, units -/

section SurplusFlow

variable {n : ℕ} {D : Dag}

theorem sb_mem_inner {w : ℕ} : w ∈ inner n D ↔ w + 1 < n + D.length := by
  unfold inner; rw [Finset.mem_range]; omega

theorem sb_src_false (j : ℕ) : src D (j, false) = opA D j := by simp [src]

theorem sb_src_true (j : ℕ) : src D (j, true) = opB D j := by simp [src]

/-! ### Fanout and the global surplus identity -/

theorem fanout_eq_zero_of_ge (hS : Strict n D) (w : ℕ) (h : n + D.length ≤ w + 1) :
    fanout D w = 0 := by
  unfold fanout readers
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  have hj2 := Finset.mem_range.mp hj
  have := hS j hj2
  omega

theorem lt_of_fanout_pos (hS : Strict n D) {w : ℕ} (h : 1 ≤ fanout D w) :
    w + 1 < n + D.length := by
  by_contra hc
  have := fanout_eq_zero_of_ge hS w (by omega)
  omega

theorem sb_card_arcs_filter (P : ℕ × Bool → Prop) [DecidablePred P] :
    ((arcs D).filter P).card = ∑ j ∈ Finset.range D.length,
      ((if P (j, false) then 1 else 0) + (if P (j, true) then 1 else 0)) := by
  rw [Finset.card_filter, arcs, Finset.sum_product]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Fintype.sum_bool, add_comm]

theorem sb_card_arcs : (arcs D).card = 2 * D.length := by
  simp [arcs, Finset.card_product, Nat.mul_comm]

theorem sb_src_lt (hS : Strict n D) (e : ℕ × Bool) (he : e ∈ arcs D) :
    src D e + 1 < n + D.length := by
  obtain ⟨j, c⟩ := e
  have hj : j < D.length := by simpa [arcs] using he
  have := hS j hj
  cases c
  · rw [sb_src_false]; omega
  · rw [sb_src_true]; omega

/-- Fanout counts the operand positions reading the wire. -/
theorem sb_fanout_arcs (hS : Strict n D) (w : ℕ) :
    fanout D w = ((arcs D).filter (fun e => src D e = w)).card := by
  rw [sb_card_arcs_filter, fanout, readers, Finset.card_filter]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have := (hS j (Finset.mem_range.mp hj)).2.2
  rw [sb_src_false, sb_src_true]
  split_ifs <;> omega

theorem sb_sum_fanout_eq (hS : Strict n D) (K : Finset ℕ) :
    ∑ w ∈ K, fanout D w = ((arcs D).filter (fun e => src D e ∈ K)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := src D)
    (s := (arcs D).filter (fun e => src D e ∈ K)) (t := K)
    (fun e he => Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2)]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [sb_fanout_arcs hS, Finset.filter_filter]
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl⟩; exact ⟨he, hw, rfl⟩
  · rintro ⟨he, -, h⟩; exact ⟨he, h⟩

theorem sb_surplus_add_card {K : Finset ℕ} (hL : ∀ w ∈ K, 1 ≤ fanout D w) :
    surplusOn D K + K.card = ∑ w ∈ K, fanout D w := by
  rw [surplusOn, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun w hw => Nat.sub_add_cancel (hL w hw))

theorem sum_fanout (hS : Strict n D) :
    ∑ w ∈ Finset.range (n + D.length), fanout D w = 2 * D.length := by
  rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
  intro e he
  have := sb_src_lt hS e he
  exact Finset.mem_range.mpr (by omega)

/-- The global identity `B = s - n + 1`, in addition form. -/
theorem surplus_identity (h : StrictLive n D) : totalSurplus n D + n = D.length + 1 := by
  obtain ⟨hS, hL, hne⟩ := h
  have hpos : 0 < D.length := List.length_pos_iff.mpr hne
  have h1 : surplusOn D (inner n D) + (inner n D).card = ∑ w ∈ inner n D, fanout D w :=
    sb_surplus_add_card (fun w hw => hL w (sb_mem_inner.mp hw))
  have h2 : ∑ w ∈ inner n D, fanout D w = 2 * D.length := by
    rw [sb_sum_fanout_eq hS, Finset.filter_true_of_mem, sb_card_arcs]
    intro e he
    exact sb_mem_inner.mpr (sb_src_lt hS e he)
  have h3 : (inner n D).card = n + D.length - 1 := Finset.card_range _
  unfold totalSurplus
  omega

theorem totalSurplus_split (n : ℕ) (D : Dag) : totalSurplus n D = Bplus n D + Bzero n D := by
  unfold totalSurplus Bplus Bzero surplusOn
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

theorem Bplus_le_total (n : ℕ) (D : Dag) : Bplus n D ≤ totalSurplus n D := by
  rw [totalSurplus_split]; omega

theorem Bplus_le_twelve (h13 : totalSurplus n D ≤ 13) (h0 : 1 ≤ Bzero n D) :
    Bplus n D ≤ 12 := by
  rw [totalSurplus_split] at h13; omega

/-- Every wire has a reader path to the output. -/
theorem live_reaches_out (h : StrictLive n D) (w : ℕ) (hw : w < n + D.length) :
    Relation.ReflTransGen (fun a b => b < n + D.length ∧ n ≤ b ∧
      (opA D (b - n) = a ∨ opB D (b - n) = a)) w (outW n D) := by
  obtain ⟨hS, hL, -⟩ := h
  generalize hk : n + D.length - w = k
  induction k using Nat.strong_induction_on generalizing w with
  | _ k ih =>
    by_cases hlast : w + 1 = n + D.length
    · have hw2 : w = outW n D := by unfold outW; omega
      rw [hw2]
    · obtain ⟨j, hj⟩ := Finset.card_pos.mp (hL w (by omega))
      simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
      have hs := hS j hj.1
      refine Relation.ReflTransGen.head (b := n + j) ⟨by omega, by omega, ?_⟩
        (ih (n + D.length - (n + j)) (by omega) (n + j) (by omega) rfl)
      simpa using hj.2

/-! ### Semantics of singleton supports -/

theorem mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

theorem val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

theorem val_zero (hS : Strict n D) (w : ℕ) : val D (fun _ : Fin n => false) w = false := by
  by_cases hw : w < n + D.length
  · exact val_unique hS _ (fun _ => false) (fun _ _ => rfl)
      (fun j _ => by cases tag D j <;> rfl) w hw
  · exact val_ge D _ w (by omega)

theorem supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

theorem supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

theorem supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp]

/-! ### Carrier flow -/

/-- `e_K + M_K = sources_K + B_K` for a wire set missing the output in which every gate
has an operand. -/
theorem carrier_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D)
    (hpred : ∀ j, j < D.length → n + j ∈ K → opA D j ∈ K ∨ opB D j ∈ K) :
    (exitArcs n D K).card + (merges n D K).card = (sources n K).card + surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have := hpred j (Finset.mem_range.mp hj)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card = (sources n K).card +
      ((Finset.range D.length).filter (fun j => n + j ∈ K)).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K) (fun w => w < n), sources]
    congr 1
    have himg : K.filter (fun w => ¬ w < n) =
        ((Finset.range D.length).filter (fun j => n + j ∈ K)).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj⟩, rfl⟩
        exact ⟨hj, by omega⟩
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

theorem sb_carrierT_sub (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) : carrierT n D T ⊆ inner n D := by
  intro w hw
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hw
  rw [sb_mem_inner]
  by_contra hc
  have hw2 : w = outW n D := by unfold outW; omega
  rw [hw2, hout] at hw
  exact Finset.not_nonempty_empty hw.2

theorem sb_sources_carrierT (D : Dag) (T : Finset (Fin n)) :
    (sources n (carrierT n D T)).card = T.card := by
  have himg : sources n (carrierT n D T) = T.image (fun v : Fin n => v.val) := by
    ext w
    simp only [sources, carrierT, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨-, v, hv⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_inter, Finset.mem_singleton] at hv
      exact ⟨v, hv.2, by rw [hv.1]⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨by have := v.isLt; omega, v, ?_⟩, v.isLt⟩
      rw [supp_input]; simp [hv]
  rw [himg, Finset.card_image_of_injective _ Fin.val_injective]

/-- Flow for the union carrier of a label set. -/
theorem carrier_flow_union (h : StrictLive n D) (T : Finset (Fin n))
    (hout : supp n D (outW n D) ∩ T = ∅) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card =
      T.card + surplusOn D (carrierT n D T) := by
  rw [← sb_sources_carrierT D T]
  refine carrier_flow h _ (sb_carrierT_sub T hout) (fun j hj hK => ?_)
  obtain ⟨ha, hb, -⟩ := h.1 j hj
  simp only [carrierT, Finset.mem_filter, Finset.mem_range] at hK ⊢
  obtain ⟨v, hv⟩ := hK.2
  rw [Finset.mem_inter, supp_gate h.1 j hj] at hv
  split_ifs at hv with ht
  · rw [Finset.mem_inter] at hv
    exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩
  · rw [Finset.mem_union] at hv
    rcases hv.1 with h1 | h1
    · exact Or.inl ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩
    · exact Or.inr ⟨by omega, v, Finset.mem_inter.mpr ⟨h1, hv.2⟩⟩

/-- Flow for the carrier of `x` without `y`. -/
theorem carrier_flow_diff (h : StrictLive n D) (x y : Fin n) (hxy : x ≠ y)
    (hout : x ∉ supp n D (outW n D)) :
    (exitArcs n D (carrierDiff n D x y)).card + (merges n D (carrierDiff n D x y)).card =
      1 + surplusOn D (carrierDiff n D x y) := by
  have hsub : carrierDiff n D x y ⊆ inner n D := by
    intro w hw
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hw
    rw [sb_mem_inner]
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2] at hw
    exact hout hw.2.1
  have hsrc : sources n (carrierDiff n D x y) = {x.val} := by
    ext w
    simp only [sources, carrierDiff, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨-, hx, -⟩, hw⟩
      have hs : supp n D w = {⟨w, hw⟩} := supp_input D ⟨w, hw⟩
      rw [hs, Finset.mem_singleton] at hx
      rw [hx]
    · rintro rfl
      refine ⟨⟨by have := x.isLt; omega, ?_, ?_⟩, x.isLt⟩
      · rw [supp_input]; exact Finset.mem_singleton_self x
      · rw [supp_input, Finset.mem_singleton]; exact fun hc => hxy hc.symm
  have hfl := carrier_flow h _ hsub (fun j hj hK => ?_)
  · rw [hsrc, Finset.card_singleton] at hfl; exact hfl
  · obtain ⟨ha, hb, -⟩ := h.1 j hj
    simp only [carrierDiff, Finset.mem_filter, Finset.mem_range] at hK ⊢
    obtain ⟨-, hx, hy⟩ := hK
    rw [supp_gate h.1 j hj] at hx hy
    split_ifs at hx hy with ht
    · rw [Finset.mem_inter] at hx hy
      by_cases hya : y ∈ supp n D (opA D j)
      · exact Or.inr ⟨by omega, hx.2, fun hc => hy ⟨hya, hc⟩⟩
      · exact Or.inl ⟨by omega, hx.1, hya⟩
    · rw [Finset.mem_union] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl ⟨by omega, h1, fun hc => hy (Or.inl hc)⟩
      · exact Or.inr ⟨by omega, h1, fun hc => hy (Or.inr hc)⟩

/-! ### Multiplicity-aware surplus units -/

theorem mem_units {u : Σ _ : ℕ, ℕ} :
    u ∈ units n D ↔ u.1 ∈ inner n D ∧ u.2 + 1 < fanout D u.1 := by
  rw [units, Finset.mem_sigma, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem sb_card_units_filter (n : ℕ) (D : Dag) (p : ℕ → Prop) [DecidablePred p] :
    ((units n D).filter (fun u => p u.1)).card = surplusOn D ((inner n D).filter p) := by
  have hs : (units n D).filter (fun u => p u.1) =
      ((inner n D).filter p).sigma (fun w => Finset.range (fanout D w - 1)) := by
    ext u; simp only [units, Finset.mem_filter, Finset.mem_sigma]; tauto
  rw [hs, Finset.card_sigma, surplusOn]
  simp

theorem card_units (n : ℕ) (D : Dag) : (units n D).card = totalSurplus n D := by
  rw [units, Finset.card_sigma, totalSurplus, surplusOn]
  simp

theorem card_unitsPlus (n : ℕ) (D : Dag) : (unitsPlus n D).card = Bplus n D := by
  unfold unitsPlus Bplus
  exact sb_card_units_filter n D (fun w => (supp n D w).Nonempty)

theorem card_unitsOn (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (unitsOn n D K).card = surplusOn D K := by
  rw [unitsOn, sb_card_units_filter n D (fun w => w ∈ K), Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hK]

/-! ### Eligible labels and reserved units -/

theorem mem_eligSet {v : Fin n} :
    v ∈ eligSet n D ↔ ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := by
  simp only [eligSet, branchW, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨w, ⟨-, h2⟩, hv⟩; exact ⟨w, h2, hv⟩
  · rintro ⟨w, h2, hv⟩
    refine ⟨w, ⟨?_, h2⟩, hv⟩
    by_contra hc
    rw [supp_ge D w (by omega)] at hv
    exact Finset.notMem_empty v hv

theorem mem_ineligSet {v : Fin n} :
    v ∈ ineligSet n D ↔ ∀ w, v ∈ supp n D w → fanout D w ≤ 1 := by
  rw [ineligSet, Finset.mem_sdiff, mem_eligSet]
  constructor
  · rintro ⟨-, h⟩ w hw
    by_contra hc
    exact h ⟨w, by omega, hw⟩
  · intro h
    refine ⟨Finset.mem_univ v, ?_⟩
    rintro ⟨w, hw, hv⟩
    have := h w hv
    omega

theorem sb_singleton_inter_nonempty {v : Fin n} {T : Finset (Fin n)} :
    (({v} : Finset (Fin n)) ∩ T).Nonempty ↔ v ∈ T := by
  constructor
  · rintro ⟨u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2
  · intro h
    exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self v, h⟩⟩

theorem sb_reserved_inj (b : Fin n → ℕ) (hb : PureBranch n D b) :
    Set.InjOn (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) (eligSet n D : Set (Fin n)) := by
  intro v hv v2 hv2 he
  have hbv : b v = b v2 := congrArg Sigma.fst he
  have h1 := (hb v hv).2
  rw [hbv, (hb v2 hv2).2] at h1
  exact (Finset.singleton_injective h1).symm

theorem reserved_subset (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    reservedUnits n D b ⊆ unitsPlus n D := by
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨h2, hs⟩ := hb v hv
  have h1 : 1 ≤ fanout D (b v) := by omega
  rw [unitsPlus, Finset.mem_filter, mem_units]
  refine ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS h1), ?_⟩, ?_⟩
  · show 0 + 1 < fanout D (b v)
    omega
  · show (supp n D (b v)).Nonempty
    rw [hs]; exact Finset.singleton_nonempty v

theorem card_reserved (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (reservedUnits n D b).card = (eligSet n D).card :=
  Finset.card_image_of_injOn (sb_reserved_inj b hb)

/-- `p ≤ B_+`. -/
theorem elig_le_Bplus (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (eligSet n D).card ≤ Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_le_card (reserved_subset hS b hb)

theorem card_residual (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b) :
    (residualUnits n D b).card + (eligSet n D).card = Bplus n D := by
  rw [← card_reserved b hb, ← card_unitsPlus]
  exact Finset.card_sdiff_add_card_eq_card (reserved_subset hS b hb)

/-- `B_T = |T ∩ S| +` the number of residual units carrying a label of `T`. -/
theorem surplus_carrierT_eq (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) = (T ∩ eligSet n D).card +
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
  have h1 : surplusOn D (carrierT n D T) =
      ((units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty)).card := by
    rw [sb_card_units_filter n D (fun w => (supp n D w ∩ T).Nonempty)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      have := sb_mem_inner.mp hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hw.2⟩
    · rw [carrierT, Finset.mem_filter] at hw
      have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, hw.2⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) ∪
        (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · exact Or.inl ⟨hr, hu.2⟩
      · exact Or.inr ⟨⟨⟨hu.1, hu.2.mono Finset.inter_subset_left⟩, hr⟩, hu.2⟩
    · rintro (hu | hu)
      · exact ⟨(Finset.mem_filter.mp (hsub hu.1)).1, hu.2⟩
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : Disjoint ((reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty))
      ((residualUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty)) :=
    Finset.disjoint_filter_filter Finset.disjoint_sdiff
  have h4 : (reservedUnits n D b).filter (fun u => (supp n D u.1 ∩ T).Nonempty) =
      (T ∩ eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ)) := by
    rw [reservedUnits, Finset.filter_image]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hne⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty] at hne
      exact ⟨hne, hv⟩
    · rintro ⟨hT, hv⟩
      refine ⟨hv, ?_⟩
      rw [(hb v hv).2, sb_singleton_inter_nonempty]
      exact hT
  rw [h1, h2, Finset.card_union_of_disjoint h3, h4,
    Finset.card_image_of_injOn ((sb_reserved_inj b hb).mono
      (Finset.coe_subset.mpr Finset.inter_subset_right))]

/-- `B_T ≤ |T ∩ S| + (B_+ - p)`, in addition form. -/
theorem surplus_carrierT_le (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    (T : Finset (Fin n)) :
    surplusOn D (carrierT n D T) + (eligSet n D).card ≤
      (T ∩ eligSet n D).card + Bplus n D := by
  have h1 := surplus_carrierT_eq hS b hb T
  have h2 := card_residual hS b hb
  have h3 := Finset.card_filter_le (residualUnits n D b)
    (fun u => (supp n D u.1 ∩ T).Nonempty)
  omega

end SurplusFlow

/-! ## Block T: transport along a permutation of the input labels -/

/-- The action of `σ` on wires: input wires are permuted, gate wires are fixed. -/
def liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (σ ⟨w, h⟩).val else w

/-- The DAG with every operand moved by `liftP σ`. -/
def relabel {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) : Dag :=
  D.map (fun g => (g.1, liftP σ g.2.1, liftP σ g.2.2))

theorem tr_liftP_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : w < n) :
    liftP σ w = (σ ⟨w, h⟩).val := by
  simp [liftP, h]

theorem tr_liftP_ge {n : ℕ} (σ : Equiv.Perm (Fin n)) {w : ℕ} (h : n ≤ w) : liftP σ w = w := by
  simp [liftP, Nat.not_lt.mpr h]

theorem tr_liftP_lt_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (w : ℕ) :
    liftP σ w < m ↔ w < m := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h]
    have := (σ ⟨w, h⟩).isLt
    constructor <;> intro <;> omega
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h)]

theorem liftP_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ⁻¹ (liftP σ w) = w := by
  by_cases h : w < n
  · rw [tr_liftP_lt σ h, tr_liftP_lt σ⁻¹ (σ ⟨w, h⟩).isLt]; simp
  · rw [tr_liftP_ge σ (Nat.not_lt.mp h), tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]

theorem tr_liftP_inv' {n : ℕ} (σ : Equiv.Perm (Fin n)) (w : ℕ) : liftP σ (liftP σ⁻¹ w) = w := by
  simpa using liftP_inv σ⁻¹ w

theorem tr_liftP_inj {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : ℕ} :
    liftP σ a = liftP σ b ↔ a = b := by
  refine ⟨fun h => ?_, congrArg _⟩
  have := congrArg (liftP σ⁻¹) h
  rwa [liftP_inv, liftP_inv] at this

theorem relabel_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    (relabel σ D).length = D.length := by
  simp [relabel]

theorem tr_tag {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    tag (relabel σ D) j = tag D j := by
  rw [tag_eq _ j (by rw [relabel_length]; exact hj), tag_eq D j hj]; simp [relabel]

theorem tr_opA {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opA (relabel σ D) j = liftP σ (opA D j) := by
  rw [opA_eq _ j (by rw [relabel_length]; exact hj), opA_eq D j hj]; simp [relabel]

theorem tr_opB {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (j : ℕ) (hj : j < D.length) :
    opB (relabel σ D) j = liftP σ (opB D j) := by
  rw [opB_eq _ j (by rw [relabel_length]; exact hj), opB_eq D j hj]; simp [relabel]

theorem relabel_strict {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Strict n (relabel σ D) := by
  intro j hj
  rw [relabel_length] at hj
  obtain ⟨ha, hb, hab⟩ := hS j hj
  rw [tr_opA σ D j hj, tr_opB σ D j hj]
  exact ⟨(tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr ha,
    (tr_liftP_lt_iff σ (Nat.le_add_right n j) _).mpr hb, fun h => hab ((tr_liftP_inj σ).mp h)⟩

/-- The relabelled DAG on `x` has the values of the old DAG on `x ∘ σ`. -/
theorem relabel_val {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (w : ℕ) :
    val (relabel σ D) x (liftP σ w) = val D (fun i => x (σ i)) w := by
  by_cases hw : w < n + D.length
  · refine (val_unique (relabel_strict σ hS) x
      (fun w' => val D (fun i => x (σ i)) (liftP σ⁻¹ w')) ?_ ?_ (liftP σ w) ?_).trans ?_
    · intro i hi
      show val D (fun i => x (σ i)) (liftP σ⁻¹ i) = x ⟨i, hi⟩
      rw [tr_liftP_lt σ⁻¹ hi, val_input D _ _ (σ⁻¹ ⟨i, hi⟩).isLt]
      simp
    · intro j hj
      rw [relabel_length] at hj
      show val D (fun i => x (σ i)) (liftP σ⁻¹ (n + j)) =
        gop (tag (relabel σ D) j) (val D (fun i => x (σ i)) (liftP σ⁻¹ (opA (relabel σ D) j)))
          (val D (fun i => x (σ i)) (liftP σ⁻¹ (opB (relabel σ D) j)))
      rw [tr_liftP_ge σ⁻¹ (Nat.le_add_right n j), tr_tag σ D j hj, tr_opA σ D j hj,
        tr_opB σ D j hj, liftP_inv, liftP_inv, val_gate hS _ j hj]
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · show val D (fun i => x (σ i)) (liftP σ⁻¹ (liftP σ w)) = _
      rw [liftP_inv]
  · have hw' := Nat.not_lt.mp hw
    rw [tr_liftP_ge σ (le_trans (Nat.le_add_right _ _) hw'),
      val_ge _ _ _ (by rw [relabel_length]; exact hw'), val_ge _ _ _ hw']

theorem relabel_fanout {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (w : ℕ) :
    fanout (relabel σ D) (liftP σ w) = fanout D w := by
  unfold fanout readers
  rw [relabel_length]
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [tr_opA σ D j hj', tr_opB σ D j hj', tr_liftP_inj, tr_liftP_inj]

theorem relabel_live {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hL : Live n D) :
    Live n (relabel σ D) := by
  rcases eq_or_ne D [] with rfl | hne
  · exact hL
  · intro w' hw'
    rw [relabel_length] at hw'
    have hpos := List.length_pos_iff.mpr hne
    rw [← tr_liftP_inv' σ w', relabel_fanout]
    apply hL
    by_cases h : w' < n
    · have := (tr_liftP_lt_iff σ⁻¹ le_rfl w').mpr h
      omega
    · rw [tr_liftP_ge σ⁻¹ (Nat.not_lt.mp h)]; exact hw'

theorem relabel_strictLive {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (h : StrictLive n D) :
    StrictLive n (relabel σ D) :=
  ⟨relabel_strict σ h.1, relabel_live σ h.2.1, by simpa [relabel] using h.2.2⟩

theorem relabel_out {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (hne : D ≠ [])
    (x : Fin n → Bool) :
    val (relabel σ D) x (outW n (relabel σ D)) = val D (fun i => x (σ i)) (outW n D) := by
  have hpos := List.length_pos_iff.mpr hne
  have e : outW n (relabel σ D) = liftP σ (outW n D) := by
    rw [tr_liftP_ge σ (by unfold outW; omega)]; simp [outW, relabel_length]
  rw [e, relabel_val σ hS]

theorem tr_single_comp {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n) :
    (fun i => single v (σ i)) = single (σ⁻¹ v) := by
  funext i
  simp only [single, decide_eq_decide]
  constructor
  · intro h; rw [← h]; simp
  · intro h; rw [h]; simp

theorem relabel_supp {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) (w : ℕ) :
    supp n (relabel σ D) (liftP σ w) = (supp n D w).image σ := by
  ext v
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [relabel_val σ hS, tr_single_comp]
  constructor
  · intro h; exact ⟨σ⁻¹ v, h, by simp⟩
  · rintro ⟨a, ha, rfl⟩; simpa using ha

/-- Reindexing a filtered sum over an initial range by `liftP σ`. -/
theorem tr_sum_liftP {n : ℕ} (σ : Equiv.Perm (Fin n)) {m : ℕ} (hm : n ≤ m) (P : ℕ → Prop)
    [DecidablePred P] (g : ℕ → ℕ) :
    ∑ w ∈ (Finset.range m).filter (fun w => P (liftP σ w)), g (liftP σ w) =
      ∑ w ∈ (Finset.range m).filter P, g w := by
  refine Finset.sum_nbij' (liftP σ) (liftP σ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ hm a).mpr ha.1, ha.2⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
    exact ⟨(tr_liftP_lt_iff σ⁻¹ hm a).mpr ha.1, by rw [tr_liftP_inv']; exact ha.2⟩
  · intro a _; exact liftP_inv σ a
  · intro a _; exact tr_liftP_inv' σ a
  · intro a _; rfl

/-- Surplus on a filtered set of inner wires is preserved when the filters correspond. -/
theorem tr_surplus_filter {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (hPQ : ∀ w, Q (liftP σ w) ↔ P w) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter Q) =
      surplusOn D ((inner n D).filter P) := by
  rcases eq_or_ne D [] with rfl | hne
  · simp [surplusOn, relabel, fanout, readers]
  · have hpos := List.length_pos_iff.mpr hne
    have hm : n ≤ n + D.length - 1 := by omega
    unfold surplusOn inner
    rw [relabel_length]
    exact (tr_sum_liftP σ hm Q (fun w => fanout (relabel σ D) w - 1)).symm.trans
      (Finset.sum_congr (Finset.filter_congr fun w _ => hPQ w)
        fun w _ => by rw [relabel_fanout])

theorem relabel_totalSurplus {n : ℕ} (σ : Equiv.Perm (Fin n)) (D : Dag) :
    totalSurplus n (relabel σ D) = totalSurplus n D := by
  simpa [totalSurplus] using
    tr_surplus_filter σ D (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)

theorem relabel_Bplus {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bplus n (relabel σ D) = Bplus n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_Bzero {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    Bzero n (relabel σ D) = Bzero n D :=
  tr_surplus_filter σ D _ _ (fun w => by rw [relabel_supp σ hS]; simp)

theorem relabel_eligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    eligSet n (relabel σ D) = (eligSet n D).image σ := by
  ext v
  simp only [eligSet, Finset.mem_biUnion, Finset.mem_image, branchW, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro ⟨w', ⟨hw', hf⟩, hv⟩
    obtain ⟨w, rfl⟩ : ∃ w, w' = liftP σ w := ⟨liftP σ⁻¹ w', (tr_liftP_inv' σ w').symm⟩
    rw [relabel_supp σ hS, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [relabel_fanout] at hf
    rw [relabel_length, tr_liftP_lt_iff σ (Nat.le_add_right _ _)] at hw'
    exact ⟨a, ⟨w, ⟨hw', hf⟩, ha⟩, rfl⟩
  · rintro ⟨a, ⟨w, ⟨hw, hf⟩, ha⟩, rfl⟩
    refine ⟨liftP σ w, ⟨?_, ?_⟩, ?_⟩
    · rw [relabel_length]; exact (tr_liftP_lt_iff σ (Nat.le_add_right _ _) w).mpr hw
    · rw [relabel_fanout]; exact hf
    · rw [relabel_supp σ hS]; exact Finset.mem_image_of_mem _ ha

theorem relabel_ineligSet {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D) :
    ineligSet n (relabel σ D) = (ineligSet n D).image σ := by
  ext v
  simp only [ineligSet, relabel_eligSet σ hS, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ v, fun hm => h ⟨σ⁻¹ v, hm, by simp⟩, by simp⟩
  · rintro ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact ha (σ.injective hab ▸ hb)

theorem relabel_pureBranch {n : ℕ} (σ : Equiv.Perm (Fin n)) {D : Dag} (hS : Strict n D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) :
    PureBranch n (relabel σ D) (fun v => liftP σ (b (σ⁻¹ v))) := by
  intro v hv
  rw [relabel_eligSet σ hS, Finset.mem_image] at hv
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨hf, hs⟩ := hb u hu
  have e : σ⁻¹ (σ u) = u := by simp
  show 2 ≤ fanout (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) ∧
    supp n (relabel σ D) (liftP σ (b (σ⁻¹ (σ u)))) = {σ u}
  rw [e, relabel_fanout, relabel_supp σ hS, hs, Finset.image_singleton]
  exact ⟨hf, rfl⟩

/-! ## Block C: Heawood / Fano geometry and independent sets up to automorphism -/

/-- The official 21 oriented edges (point, line), in the official order. -/
def edgeList : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11),
    (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

/-- The official Heawood edge predicate on an assignment. -/
def HeawoodEdge (x : Fin 14 → Bool) : Prop :=
  ∃ u v : Fin 14, (u.val, v.val) ∈ edgeList ∧ x u = true ∧ x v = true

/-- Undirected Heawood adjacency. -/
abbrev Adj (u v : Fin 14) : Prop := (u.val, v.val) ∈ edgeList ∨ (v.val, u.val) ∈ edgeList

/-- Fano incidence of point `p` and line `l`; line `l` is the official vertex `l + 7`. -/
def inc (p l : Fin 7) : Bool :=
  (([11, 69, 98, 49, 88, 44, 22] : List ℕ).getD l.val 0).testBit p.val

/-- Fast Boolean adjacency through neighbour bit masks. -/
def hc_adjB (u v : Fin 14) : Bool :=
  (([1408, 8832, 12544, 6272, 11264, 5632, 2816, 11, 69, 98, 49, 88, 44, 22] : List ℕ).getD
    u.val 0).testBit v.val

theorem hc_adjB_iff : ∀ u v : Fin 14, hc_adjB u v = true ↔ Adj u v := by decide +kernel

theorem hc_edge_inc : ∀ p l : Fin 7, (p.val, l.val + 7) ∈ edgeList ↔ inc p l = true := by
  decide +kernel

theorem hc_edge_sides : ∀ u v : Fin 14, (u.val, v.val) ∈ edgeList → u.val < 7 ∧ 7 ≤ v.val := by
  decide +kernel

theorem edge_iff_inc (u v : Fin 14) : (u.val, v.val) ∈ edgeList ↔
    ∃ p l : Fin 7, u.val = p.val ∧ v.val = l.val + 7 ∧ inc p l = true := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hc_edge_sides u v h
    have hv : v.val = v.val - 7 + 7 := by omega
    refine ⟨⟨u.val, h1⟩, ⟨v.val - 7, by omega⟩, rfl, hv, (hc_edge_inc _ _).mp ?_⟩
    rw [← hv]; exact h
  · rintro ⟨p, l, hu, hv, hi⟩
    rw [hu, hv]; exact (hc_edge_inc p l).mpr hi

theorem adj_symm {u v : Fin 14} : Adj u v → Adj v u := Or.symm

theorem adj_irrefl (u : Fin 14) : ¬ Adj u u := by revert u; decide +kernel

theorem heawoodEdge_iff_adj (x : Fin 14 → Bool) :
    HeawoodEdge x ↔ ∃ u v : Fin 14, Adj u v ∧ x u = true ∧ x v = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩; exact ⟨u, v, Or.inl h, hu, hv⟩
  · rintro ⟨u, v, h | h, hu, hv⟩
    · exact ⟨u, v, h, hu, hv⟩
    · exact ⟨v, u, h, hv, hu⟩

theorem degree_three (v : Fin 14) : (Finset.univ.filter (fun u => Adj v u)).card = 3 := by
  rw [Finset.filter_congr (fun u _ => (hc_adjB_iff v u).symm)]
  revert v; decide +kernel

theorem fano_unique_line (p q : Fin 7) (h : p ≠ q) :
    ∃! l : Fin 7, inc p l = true ∧ inc q l = true := by
  revert p q; unfold ExistsUnique; decide +kernel

theorem fano_unique_point (l m : Fin 7) (h : l ≠ m) :
    ∃! p : Fin 7, inc p l = true ∧ inc p m = true := by
  revert l m; unfold ExistsUnique; decide +kernel

theorem common_nbr_le_one (u v : Fin 14) (h : u ≠ v) :
    (Finset.univ.filter (fun z => Adj u z ∧ Adj v z)).card ≤ 1 := by
  rw [Finset.filter_congr (fun z _ => and_congr (hc_adjB_iff u z).symm (hc_adjB_iff v z).symm)]
  revert u v; decide +kernel

theorem hc_nbr_diff : ∀ v w : Fin 14, v ≠ w →
    ∃ z, hc_adjB v z = true ∧ hc_adjB w z = false := by decide +kernel

theorem nbr_diff_exists (v w : Fin 14) (h : v ≠ w) : ∃ z, Adj v z ∧ ¬ Adj w z := by
  obtain ⟨z, h1, h2⟩ := hc_nbr_diff v w h
  refine ⟨z, (hc_adjB_iff v z).mp h1, fun h3 => ?_⟩
  rw [← hc_adjB_iff, h2] at h3
  exact Bool.false_ne_true h3

def IsCover (S : Finset (Fin 14)) : Prop := ∀ u v : Fin 14, Adj u v → u ∈ S ∨ v ∈ S

def IsIndep (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, ¬ Adj u v

theorem indep_iff_cover_compl (I : Finset (Fin 14)) : IsIndep I ↔ IsCover (Finset.univ \ I) := by
  constructor
  · intro h u v huv
    by_contra hc
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_or, not_not] at hc
    exact h u hc.1 v hc.2 huv
  · intro h u hu v hv huv
    rcases h u v huv with h1 | h1 <;> simp [hu, hv] at h1

/-- The explicit perfect matching. -/
def matching : List (Fin 14 × Fin 14) :=
  [(0, 7), (1, 13), (2, 8), (3, 12), (4, 11), (5, 10), (6, 9)]

/-- The matching partner of a vertex. -/
def hc_mate (v : Fin 14) : Fin 14 :=
  Fin.ofNat 14 (([7, 13, 8, 12, 11, 10, 9, 0, 2, 6, 5, 4, 3, 1] : List ℕ).getD v.val 0)

theorem hc_match1 : ∀ e ∈ matching, Adj e.1 e.2 := by decide +kernel

theorem hc_match2 : ∀ v : Fin 14, hc_adjB v (hc_mate v) = true ∧ hc_mate (hc_mate v) = v := by
  decide +kernel

theorem hc_match3 : ∀ v : Fin 14, (v, hc_mate v) ∈ matching ∨ (hc_mate v, v) ∈ matching := by
  decide +kernel

theorem matching_adj : (∀ e ∈ matching, Adj e.1 e.2) ∧ ∀ v : Fin 14, Adj v (hc_mate v) ∧
    hc_mate (hc_mate v) = v ∧ ((v, hc_mate v) ∈ matching ∨ (hc_mate v, v) ∈ matching) :=
  ⟨hc_match1, fun v => ⟨(hc_adjB_iff _ _).mp (hc_match2 v).1, (hc_match2 v).2, hc_match3 v⟩⟩

theorem cover_card_ge_seven (S : Finset (Fin 14)) (h : IsCover S) : 7 ≤ S.card := by
  have hsub : (Finset.univ : Finset (Fin 14)) ⊆ S ∪ S.image hc_mate := by
    intro v _
    rcases h v (hc_mate v) (matching_adj.2 v).1 with hv | hv
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hv, (matching_adj.2 v).2.1⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le S (S.image hc_mate)
  have h3 := Finset.card_image_le (s := S) (f := hc_mate)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem indep_card_le_seven (I : Finset (Fin 14)) (h : IsIndep I) : I.card ≤ 7 := by
  have h1 := cover_card_ge_seven _ ((indep_iff_cover_compl I).mp h)
  rw [Finset.card_univ_sdiff, Fintype.card_fin] at h1
  omega

/-- Automorphisms of the Heawood graph. -/
def IsAut (σ : Equiv.Perm (Fin 14)) : Prop := ∀ u v : Fin 14, Adj (σ u) (σ v) ↔ Adj u v

theorem hc_isAut_of {σ : Equiv.Perm (Fin 14)}
    (h : ∀ u v : Fin 14, hc_adjB (σ u) (σ v) = hc_adjB u v) : IsAut σ := fun u v => by
  rw [← hc_adjB_iff, ← hc_adjB_iff u v, h]

theorem isAut_one : IsAut 1 := fun _ _ => Iff.rfl

theorem isAut_mul {σ τ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) (hτ : IsAut τ) : IsAut (σ * τ) :=
  fun u v => (hσ (τ u) (τ v)).trans (hτ u v)

theorem isAut_inv {σ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) : IsAut σ⁻¹ := fun u v => by
  rw [Equiv.Perm.inv_def]
  have h := hσ (σ.symm u) (σ.symm v)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h.symm

theorem heawoodEdge_aut (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) (x : Fin 14 → Bool) :
    HeawoodEdge (fun i => x (σ i)) ↔ HeawoodEdge x := by
  rw [heawoodEdge_iff_adj, heawoodEdge_iff_adj]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩; exact ⟨σ u, σ v, (hσ u v).mpr h, hu, hv⟩
  · rintro ⟨u, v, h, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, ?_, by simpa using hu, by simpa using hv⟩
    rw [← hσ, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact h

theorem indep_image_aut {σ : Equiv.Perm (Fin 14)} (hσ : IsAut σ) {I : Finset (Fin 14)}
    (hI : IsIndep I) : IsIndep (I.image σ) := by
  intro u hu v hv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
  rw [hσ a b]; exact hI a ha b hb

/-- A vertex map given by a table of images. -/
def hc_ofList (l : List ℕ) (v : Fin 14) : Fin 14 := Fin.ofNat 14 (l.getD v.val 0)

/-- The duality (a polarity): swaps the point side and the line side. -/
def dualPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    hc_ofList [13, 8, 7, 12, 10, 11, 9, 2, 1, 6, 4, 5, 3, 0],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem dualPerm_isAut : IsAut dualPerm := hc_isAut_of (by decide +kernel)

/-- A collineation of order seven: the cyclic shift of the points. -/
def collPerm : Equiv.Perm (Fin 14) :=
  ⟨hc_ofList [1, 2, 3, 4, 5, 6, 0, 13, 7, 8, 9, 10, 11, 12],
    hc_ofList [6, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 13, 7],
    by intro x; revert x; decide +kernel, by intro x; revert x; decide +kernel⟩

theorem collPerm_isAut : IsAut collPerm := hc_isAut_of (by decide +kernel)

/-- The fourteen canonical independent sets, by decreasing size. -/
def canonI : List (Finset (Fin 14)) :=
  [{0, 1, 2, 3, 4, 5, 6}, {0, 1, 2, 3, 4, 5}, {0, 1, 2, 3, 4}, {0, 1, 2, 5, 11}, {0, 1, 2, 3},
    {0, 1, 2, 5}, {0, 1, 2, 11}, {0, 1, 11, 12}, {0, 1, 2}, {0, 1, 3}, {0, 1, 11}, {0, 1},
    {0, 9}, {0}]

/-- The empty set followed by the canonical sets. -/
def hc_rep (n : Fin 15) : Finset (Fin 14) := ((∅ : Finset (Fin 14)) :: canonI).getD n.val ∅

theorem hc_rep_of_mem {R : Finset (Fin 14)} (h : R ∈ canonI) :
    ∃ n : Fin 15, n ≠ 0 ∧ hc_rep n = R := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  have hi' : i < 14 := hi
  refine ⟨⟨i + 1, by omega⟩, by simp [Fin.ext_iff], ?_⟩
  show ((∅ : Finset (Fin 14)) :: canonI).getD (i + 1) ∅ = canonI[i]
  rw [List.getD_cons_succ]; exact List.getD_eq_getElem _ _ hi

/-- Independence through the fast adjacency. -/
abbrev hc_ind (I : Finset (Fin 14)) : Prop := ∀ u ∈ I, ∀ v ∈ I, hc_adjB u v = false

theorem hc_ind_iff {I : Finset (Fin 14)} : hc_ind I ↔ IsIndep I := by
  refine forall₂_congr fun u _ => forall₂_congr fun v _ => ?_
  rw [← hc_adjB_iff, Bool.not_eq_true]

theorem hc_rep_ind : ∀ n : Fin 15, hc_ind (hc_rep n) := by decide +kernel

theorem canonI_indep : ∀ R ∈ canonI, IsIndep R := by
  intro R h
  obtain ⟨n, -, rfl⟩ := hc_rep_of_mem h
  exact hc_ind_iff.mp (hc_rep_ind n)

theorem canonI_by_card (R : Finset (Fin 14)) (h : R ∈ canonI) :
    (R.card = 7 ∧ R = {0, 1, 2, 3, 4, 5, 6}) ∨ (R.card = 6 ∧ R = {0, 1, 2, 3, 4, 5}) ∨
    (R.card = 5 ∧ (R = {0, 1, 2, 3, 4} ∨ R = {0, 1, 2, 5, 11})) ∨
    (R.card = 4 ∧ (R = {0, 1, 2, 3} ∨ R = {0, 1, 2, 5} ∨ R = {0, 1, 2, 11} ∨
      R = {0, 1, 11, 12})) ∨
    (R.card = 3 ∧ (R = {0, 1, 2} ∨ R = {0, 1, 3} ∨ R = {0, 1, 11})) ∨
    (R.card = 2 ∧ (R = {0, 1} ∨ R = {0, 9})) ∨ (R.card = 1 ∧ R = {0}) := by
  obtain ⟨n, hn, rfl⟩ := hc_rep_of_mem h
  revert n; decide +kernel

/-- Twenty explicit automorphisms covering every one-vertex extension of a canonical set. -/
def hc_tab : List (List ℕ) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13], [1,0,4,3,5,6,2,7,13,8,9,12,11,10],
    [0,3,2,1,5,4,6,7,8,11,10,9,13,12], [0,1,5,3,6,2,4,7,10,13,8,11,12,9],
    [0,2,1,6,4,5,3,8,7,12,10,11,9,13], [0,2,4,6,1,3,5,8,10,12,7,9,11,13],
    [0,2,3,6,5,4,1,8,7,13,10,9,11,12], [1,3,5,0,2,4,6,7,9,11,13,8,10,12],
    [1,2,5,4,3,0,6,13,9,8,7,11,10,12], [1,6,0,5,2,4,3,9,7,11,13,12,10,8],
    [1,6,2,5,0,3,4,9,13,11,7,10,12,8], [11,13,8,10,12,7,9,4,6,1,3,5,0,2],
    [11,13,12,10,8,9,7,4,3,1,6,0,5,2], [11,7,13,12,9,8,10,3,4,0,6,5,2,1],
    [1,2,3,4,5,6,0,13,7,8,9,10,11,12], [2,0,1,6,3,5,4,8,13,10,12,11,9,7],
    [13,8,7,12,10,11,9,2,1,6,4,5,3,0], [8,13,7,12,9,11,10,2,0,4,6,5,3,1],
    [8,13,9,12,7,10,11,2,6,4,0,3,5,1], [8,7,13,10,9,11,12,0,2,3,6,5,4,1]]

def hc_fn (k : Fin 20) : Fin 14 → Fin 14 := hc_ofList (hc_tab.getD k.val [])

theorem hc_fn_inj : ∀ k : Fin 20, ∀ a b : Fin 14, hc_fn k a = hc_fn k b → a = b := by
  decide +kernel

theorem hc_fn_adj : ∀ k : Fin 20, ∀ u v : Fin 14,
    hc_adjB (hc_fn k u) (hc_fn k v) = hc_adjB u v := by decide +kernel

theorem hc_fn_aut (k : Fin 20) : ∃ τ : Equiv.Perm (Fin 14), IsAut τ ∧ ⇑τ = hc_fn k := by
  have hinj : Function.Injective (hc_fn k) := fun a b h => hc_fn_inj k a b h
  exact ⟨Equiv.ofBijective (hc_fn k) ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩,
    hc_isAut_of fun u v => hc_fn_adj k u v, rfl⟩

/-- Witness table: row `n`, column `w` is the automorphism index for `insert w (hc_rep n)`. -/
def hc_witTab : List (List ℕ) :=
  [[0,1,9,7,10,8,14,19,17,13,18,12,11,16], [], [], [0,0,0,0,0,0,1], [], [0,0,0,0,0,2,1],
    [0,0,0,2,5,0,6], [], [], [0,0,0,0,15,0,4], [0,0,0,0,7,3,1], [0,0,0,0,0,3],
    [0,0,0,0,5,3,1,0,0,0,0,0,1], [0,0,9,2,10,0,0,0,0,0,0,12,11,13],
    [0,0,4,2,5,8,6,0,0,0,0,2,4,3]]

def hc_wit (n : Fin 15) (w : Fin 14) : Fin 20 :=
  Fin.ofNat 20 ((hc_witTab.getD n.val []).getD w.val 0)

theorem hc_check : ∀ n : Fin 15, ∀ w : Fin 14, w ∉ hc_rep n →
    hc_ind (insert w (hc_rep n)) →
    (insert w (hc_rep n)).image (hc_fn (hc_wit n w)) ∈ canonI := by decide +kernel

theorem hc_step (R : Finset (Fin 14)) (hR : R = ∅ ∨ R ∈ canonI) (w : Fin 14) (hw : w ∉ R)
    (hI : IsIndep (insert w R)) :
    ∃ τ : Equiv.Perm (Fin 14), IsAut τ ∧ (insert w R).image τ ∈ canonI := by
  obtain ⟨n, rfl⟩ : ∃ n : Fin 15, hc_rep n = R := by
    rcases hR with rfl | hR
    · exact ⟨0, rfl⟩
    · obtain ⟨n, -, h⟩ := hc_rep_of_mem hR; exact ⟨n, h⟩
  obtain ⟨τ, hτ, he⟩ := hc_fn_aut (hc_wit n w)
  exact ⟨τ, hτ, by rw [he]; exact hc_check n w hw (hc_ind_iff.mpr hI)⟩

theorem hc_class (I : Finset (Fin 14)) : IsIndep I →
    I = ∅ ∨ ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  induction I using Finset.induction_on with
  | empty => intro _; exact Or.inl rfl
  | insert v J hv ih =>
    intro hI
    have hJ : IsIndep J := fun u hu w hw =>
      hI u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw)
    obtain ⟨σ, hσ, R, hR, hJR⟩ : ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧
        ∃ R, (R = ∅ ∨ R ∈ canonI) ∧ J.image σ = R := by
      rcases ih hJ with h | ⟨σ, hσ, hm⟩
      · exact ⟨1, isAut_one, ∅, Or.inl rfl, by simp [h]⟩
      · exact ⟨σ, hσ, _, Or.inr hm, rfl⟩
    have h1 : (insert v J).image σ = insert (σ v) R := by rw [Finset.image_insert, hJR]
    have h2 : σ v ∉ R := by rw [← hJR]; simpa using hv
    have h3 : IsIndep (insert (σ v) R) := by rw [← h1]; exact indep_image_aut hσ hI
    obtain ⟨τ, hτ, hm⟩ := hc_step R hR (σ v) h2 h3
    refine Or.inr ⟨τ * σ, isAut_mul hτ hσ, ?_⟩
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, h1]; exact hm

/-- Every nonempty independent set is an automorphic image of a canonical one. -/
theorem indep_classification (I : Finset (Fin 14)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI := by
  rcases hc_class I hI with h | h
  · exact absurd h hne.ne_empty
  · exact h

theorem indep_classification_card (I : Finset (Fin 14)) (hI : IsIndep I) (hne : I.Nonempty) :
    ∃ σ : Equiv.Perm (Fin 14), IsAut σ ∧ I.image σ ∈ canonI ∧ (I.image σ).card = I.card := by
  obtain ⟨σ, hσ, hm⟩ := indep_classification I hI hne
  exact ⟨σ, hσ, hm, Finset.card_image_of_injective _ σ.injective⟩

/-! ### Facts on the Heawood edge function used by the normalisation -/

theorem heawood_not_empty : ¬ HeawoodEdge (fun _ => false) := by
  rintro ⟨u, v, -, h, -⟩; exact Bool.false_ne_true h

theorem heawood_not_single (v : Fin 14) : ¬ HeawoodEdge (fun i => decide (i = v)) := by
  rw [heawoodEdge_iff_adj]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb; exact adj_irrefl _ hab

theorem heawood_pair_iff (u v : Fin 14) :
    HeawoodEdge (fun i => decide (i = u) || decide (i = v)) ↔ Adj u v := by
  rw [heawoodEdge_iff_adj]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [Bool.or_eq_true, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (adj_irrefl _)
    · exact hab
    · exact adj_symm hab
    · exact absurd hab (adj_irrefl _)
  · intro h; exact ⟨u, v, h, by simp, by simp⟩

theorem heawood_pair {u v : Fin 14} (h : Adj u v) :
    HeawoodEdge (fun i => decide (i = u) || decide (i = v)) := (heawood_pair_iff u v).mpr h

theorem heawood_essential (i : Fin 14) : ∃ x y : Fin 14 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ ¬ HeawoodEdge x ∧ HeawoodEdge y := by
  refine ⟨fun k => decide (k = hc_mate i), fun k => decide (k = i) || decide (k = hc_mate i),
    ?_, heawood_not_single _, heawood_pair (matching_adj.2 i).1⟩
  intro k hk; simp [hk]

/-! ## Heawood glue: official bridge, symmetry transport, budget -/

/-- `D` computes the official Heawood edge function at its last wire. -/
def Correct (D : Dag) : Prop :=
  ∀ x : Fin 14 → Bool, val D x (outW 14 D) = true ↔ HeawoodEdge x

/-- The official bridge: every `Monotone2` circuit for the Heawood edge function yields a
strict live constant-free binary DAG with at most as many gates. -/
theorem heawood_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ HeawoodEdge x) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h07 : Adj (0 : Fin 14) 7 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 14) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (heawood_pair h07)⟩
      · exact ⟨fun _ => false, fun h => heawood_not_empty ((hC _).1 h)⟩)
    (by
      intro i
      refine ⟨fun k => decide (k = i), fun h => heawood_not_single i ((hC _).1 ?_)⟩
      rw [h]; simp)
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := heawood_essential i
      refine ⟨x, y, hxy, fun h => hx ((hC x).1 ?_)⟩
      rw [h]; exact (hC y).2 hy)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

/-- The output of a correct DAG carries no singleton label. -/
theorem heawood_supp_out {D : Dag} (hD : Correct D) : supp 14 D (outW 14 D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => heawood_not_single v ((hD _).1 (mem_supp.1 hv)))

/-- Relabelling the inputs by a Heawood automorphism keeps every counted quantity. -/
theorem heawood_relabel (σ : Equiv.Perm (Fin 14)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) :
    StrictLive 14 (relabel σ D) ∧ Correct (relabel σ D) ∧
      (relabel σ D).length = D.length ∧
      totalSurplus 14 (relabel σ D) = totalSurplus 14 D ∧
      Bplus 14 (relabel σ D) = Bplus 14 D ∧ Bzero 14 (relabel σ D) = Bzero 14 D ∧
      eligSet 14 (relabel σ D) = (eligSet 14 D).image σ ∧
      ineligSet 14 (relabel σ D) = (ineligSet 14 D).image σ := by
  refine ⟨relabel_strictLive σ h, fun x => ?_, relabel_length σ D, relabel_totalSurplus σ D,
    relabel_Bplus σ h.1, relabel_Bzero σ h.1, relabel_eligSet σ h.1, relabel_ineligSet σ h.1⟩
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact heawoodEdge_aut σ hσ x

theorem inelig_card_add (n : ℕ) (D : Dag) : (ineligSet n D).card + (eligSet n D).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet n D))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem heawood_cover_iff_indep (D : Dag) :
    IsCover (eligSet 14 D) ↔ IsIndep (ineligSet 14 D) := by
  have h : Finset.univ \ ineligSet 14 D = eligSet 14 D := by simp [ineligSet]
  rw [indep_iff_cover_compl, h]

/-- Without loss of generality the ineligible set is one of the fourteen canonical sets. -/
theorem heawood_wlog {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : IsIndep (ineligSet 14 D)) (hne : (ineligSet 14 D).Nonempty) :
    ∃ D' : Dag, StrictLive 14 D' ∧ Correct D' ∧ D'.length = D.length ∧
      totalSurplus 14 D' = totalSurplus 14 D ∧ Bplus 14 D' = Bplus 14 D ∧
      Bzero 14 D' = Bzero 14 D ∧ (eligSet 14 D').card = (eligSet 14 D).card ∧
      ineligSet 14 D' ∈ canonI := by
  obtain ⟨σ, hσ, hmem⟩ := indep_classification _ hI hne
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := heawood_relabel σ hσ h hD
  refine ⟨relabel σ D, h1, h2, h3, h4, h5, h6, ?_, ?_⟩
  · rw [h7, Finset.card_image_of_injective _ σ.injective]
  · rw [h8]; exact hmem

/-- Fourteen live inputs: `B = s - 13`, in addition form. -/
theorem heawood_budget {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26) :
    totalSurplus 14 D + 13 = D.length ∧ totalSurplus 14 D ≤ 13 := by
  have := surplus_identity h
  omega

/-- `7 ≤ p ≤ B_+ ≤ B ≤ 13` for at most 26 gates, given the pure first branches and the
vertex-cover property of the eligible set. -/
theorem heawood_p_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ totalSurplus 14 D ∧ totalSurplus 14 D ≤ 13 :=
  ⟨cover_card_ge_seven _ hcov, elig_le_Bplus h.1 b hb, Bplus_le_total 14 D,
    (heawood_budget h hlen).2⟩

/-- Under the same hypotheses some input is ineligible, and at most seven are. -/
theorem heawood_inelig_bounds {D : Dag} (h : StrictLive 14 D) (hlen : D.length ≤ 26)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (hcov : IsCover (eligSet 14 D)) :
    (ineligSet 14 D).Nonempty ∧ (ineligSet 14 D).card ≤ 7 := by
  obtain ⟨h7, hp, hB, h13⟩ := heawood_p_bounds h hlen b hb hcov
  have hc := inelig_card_add 14 D
  exact ⟨Finset.card_pos.1 (by omega), by omega⟩

/-! ## Block D: semantic core, dominance, purity, consumers -/

/-- Edge function of a graph relation on an assignment. -/
def sem_Edge {n : ℕ} (G : Fin n → Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G u v ∧ x u = true ∧ x v = true

/-- `D` computes the edge function of `G` at its last wire. -/
def sem_Comp (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) : Prop :=
  ∀ x : Fin n → Bool, val D x (outW n D) = true ↔ sem_Edge G x

/-- Graph hypotheses: symmetric, irreflexive, separated neighbourhoods, and for every
vertex a neighbour different from any given vertex. -/
def sem_Gr {n : ℕ} (G : Fin n → Fin n → Prop) : Prop :=
  (∀ u v, G u v → G v u) ∧ (∀ u, ¬ G u u) ∧ (∀ v w, v ≠ w → ∃ z, G v z ∧ ¬ G w z) ∧
    (∀ u v, ∃ a, G u a ∧ a ≠ v)

/-- Reader step: the gate wire `b` reads the wire `a`. -/
def sem_step (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  b < n + D.length ∧ n ≤ b ∧ (opA D (b - n) = a ∨ opB D (b - n) = a)

/-- The assignment with exactly `u` and `z` true. -/
def sem_two {n : ℕ} (u z : Fin n) : Fin n → Bool := fun i => decide (i = u) || decide (i = z)

/-- The assignment `x` with `v` switched on. -/
def sem_ins {n : ℕ} (v : Fin n) (x : Fin n → Bool) : Fin n → Bool := fun i => decide (i = v) || x i

/-- The indicator assignment of a finite set. -/
def sem_ind {n : ℕ} (A : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ A)

theorem sem_rtg_mono {α : Type} {r p : α → α → Prop} (h : ∀ a b, r a b → p a b) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.tail ih (h _ _ hbc)

section SemCore

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ins_agree (v : Fin n) (x : Fin n → Bool) : ∀ k, k ≠ v → x k = sem_ins v x k := by
  intro k hk; simp [sem_ins, hk]

theorem sem_ins_self (v : Fin n) (x : Fin n → Bool) : sem_ins v x v = true := by simp [sem_ins]

theorem sem_ins_ge (v : Fin n) (x : Fin n → Bool) : ∀ i, x i = true → sem_ins v x i = true := by
  intro i hi; simp [sem_ins, hi]

theorem sem_single_le {x : Fin n → Bool} {u : Fin n} (hu : x u = true) :
    ∀ i, single u i = true → x i = true := by
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  rw [hi]; exact hu

/-- A wire carrying `u` is true on every assignment containing `u`. -/
theorem sem_val_of_supp (hS : Strict n D) {u : Fin n} {w : ℕ} (hu : u ∈ supp n D w)
    {x : Fin n → Bool} (hx : x u = true) : val D x w = true :=
  val_mono hS (single u) x (sem_single_le hx) w (mem_supp.mp hu)

theorem sem_supp_lt {v : Fin n} {w : ℕ} (hv : v ∈ supp n D w) : w < n + D.length := by
  by_contra hc
  rw [supp_ge D w (by omega)] at hv
  exact Finset.notMem_empty v hv

theorem sem_supp_and (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true) :
    supp n D (n + j) = supp n D (opA D j) ∩ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_or (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false) :
    supp n D (n + j) = supp n D (opA D j) ∪ supp n D (opB D j) := by
  rw [supp_gate hS j hj]; simp [ht]

theorem sem_supp_and_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = true)
    (s : Bool) : supp n D (n + j) ⊆ supp n D (src D (j, s)) := by
  rw [sem_supp_and hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.inter_subset_left
  · rw [sb_src_true]; exact Finset.inter_subset_right

theorem sem_src_lt (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) < n + j := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  cases s
  · rw [sb_src_false]; exact ha
  · rw [sb_src_true]; exact hb

theorem sem_src_ne (hS : Strict n D) {j : ℕ} (hj : j < D.length) (s : Bool) :
    src D (j, s) ≠ src D (j, !s) := by
  obtain ⟨-, -, hne⟩ := hS j hj
  cases s
  · simpa [src] using hne
  · simpa [src] using hne.symm

theorem sem_step_src {j : ℕ} (hj : j < D.length) (s : Bool) :
    sem_step n D (src D (j, s)) (n + j) := by
  refine ⟨by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  cases s
  · exact Or.inl (sb_src_false j).symm
  · exact Or.inr (sb_src_true j).symm

theorem sem_step_iff {a b : ℕ} : sem_step n D a b ↔
    ∃ j s, j < D.length ∧ b = n + j ∧ src D (j, s) = a := by
  constructor
  · rintro ⟨h1, h2, h3 | h3⟩
    · exact ⟨b - n, false, by omega, by omega, by rw [sb_src_false]; exact h3⟩
    · exact ⟨b - n, true, by omega, by omega, by rw [sb_src_true]; exact h3⟩
  · rintro ⟨j, s, hj, rfl, rfl⟩
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    cases s
    · exact Or.inl (sb_src_false j).symm
    · exact Or.inr (sb_src_true j).symm

theorem sem_step_lt (hS : Strict n D) {a b : ℕ} (h : sem_step n D a b) : a < b := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hS (b - n) (by omega)
  omega

theorem sem_step_reader {a c : ℕ} (h : sem_step n D a c) : c - n ∈ readers D a := by
  unfold readers
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by have := h.1; have := h.2.1; omega, h.2.2⟩

theorem sem_step_fanout {a c : ℕ} (h : sem_step n D a c) : 1 ≤ fanout D a :=
  Finset.card_pos.mpr ⟨_, sem_step_reader h⟩

theorem sem_step_unique {a c c' : ℕ} (h1 : sem_step n D a c) (h2 : sem_step n D a c')
    (hf : fanout D a = 1) : c = c' := by
  have m1 := sem_step_reader h1
  have m2 := sem_step_reader h2
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (show (readers D a).card = 1 from hf)
  rw [hr, Finset.mem_singleton] at m1 m2
  have := h1.2.1
  have := h2.2.1
  omega

/-! ### Changed-value paths and dominance -/

/-- If two assignments differ only at `v` and change the wire `w`, a reader path of changed
wires leads from the input `v` to `w`. -/
theorem sem_changed_path (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (w : ℕ) (hw : val D x w ≠ val D y w) :
    Relation.ReflTransGen (fun a b => sem_step n D a b ∧ val D x b ≠ val D y b) v.val w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn] at hw
      have hwv : (⟨w, hn⟩ : Fin n) = v := by
        by_contra hc; exact hw (hxy _ hc)
      rw [← hwv]
    · by_cases hlt : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        have hg := hw
        rw [val_gate hS x j hj, val_gate hS y j hj] at hg
        by_cases h1 : val D x (opA D j) = val D y (opA D j)
        · have h2 : val D x (opB D j) ≠ val D y (opB D j) := by
            intro h2; apply hg; rw [h1, h2]
          exact Relation.ReflTransGen.tail (ih _ hb h2)
            ⟨⟨hlt, by omega, Or.inr (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
        · exact Relation.ReflTransGen.tail (ih _ ha h1)
            ⟨⟨hlt, by omega, Or.inl (by rw [Nat.add_sub_cancel_left])⟩, hw⟩
      · exfalso; apply hw; rw [val_ge D x w (by omega), val_ge D y w (by omega)]

/-- `b` dominates the wire `v`: it is `v` itself or lies on every reader path from `v` to
the output. -/
def sem_Dom (n : ℕ) (D : Dag) (b v : ℕ) : Prop :=
  b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v (outW n D)

/-- Assignments differing only at `v` and agreeing at a dominating wire agree at the output. -/
theorem sem_dom_eq (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b : ℕ) (hdom : sem_Dom n D b v.val)
    (hb : val D x b = val D y b) : val D x (outW n D) = val D y (outW n D) := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

/-- Reader paths through wires with exactly one reader. -/
def sem_Chain (n : ℕ) (D : Dag) (a b : ℕ) : Prop :=
  Relation.ReflTransGen (fun a c => sem_step n D a c ∧ fanout D a = 1) a b

/-- The end of a single-reader chain dominates its start. -/
theorem sem_chain_dom (hS : Strict n D) {v b : ℕ} (h : sem_Chain n D v b) :
    sem_Dom n D b v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep _ ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest⟩
      · have h0 := fanout_eq_zero_of_ge hS a (by rw [heq]; unfold outW; omega)
        have h1 := hstep.2
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest

/-- A carrier of `v` all of whose earlier carriers have at most one reader is reached from
the input `v` through single-reader carriers. -/
theorem sem_carrier_chain (hS : Strict n D) (v : Fin n) : ∀ w, v ∈ supp n D w →
    (∀ u, u < w → v ∈ supp n D u → fanout D u ≤ 1) → sem_Chain n D v.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv hlow
    by_cases hn : w < n
    · have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
      rw [hs, Finset.mem_singleton] at hv
      rw [hv]; exact Relation.ReflTransGen.refl
    · have hlt := sem_supp_lt hv
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      have key : ∀ s : Bool, v ∈ supp n D (src D (j, s)) → sem_Chain n D v.val (n + j) := by
        intro s hva
        have hstep : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
        have hlt' := sem_src_lt hS hj s
        have h1 := sem_step_fanout hstep
        have h2 := hlow _ hlt' hva
        exact Relation.ReflTransGen.tail (ih _ hlt' hva (fun u hu => hlow u (by omega)))
          ⟨hstep, by omega⟩
      rw [supp_gate hS j hj] at hv
      split_ifs at hv with ht
      · exact key false (by rw [sb_src_false]; exact (Finset.mem_inter.mp hv).1)
      · rcases Finset.mem_union.mp hv with h1 | h1
        · exact key false (by rw [sb_src_false]; exact h1)
        · exact key true (by rw [sb_src_true]; exact h1)

theorem sem_single_no_edge (hG : sem_Gr G) (v : Fin n) : ¬ sem_Edge G (single v) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [single, decide_eq_true_eq] at ha hc
  rw [ha, hc] at hac
  exact hG.2.1 _ hac

theorem sem_two_edge {u v : Fin n} (huv : G u v) : sem_Edge G (sem_two u v) :=
  ⟨u, v, huv, by simp [sem_two], by simp [sem_two]⟩

/-- The output of a circuit for an edge function carries no singleton label. -/
theorem sem_supp_out (hG : sem_Gr G) (hC : sem_Comp n G D) : supp n D (outW n D) = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2
    (fun v hv => sem_single_no_edge hG v ((hC _).1 (mem_supp.1 hv)))

/-- Dominator purity: a wire dominating the input `v` carries no other singleton label. -/
theorem sem_dom_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) : supp n D b ⊆ {v} := by
  intro u hu
  rw [Finset.mem_singleton]
  by_contra huv
  obtain ⟨hsym, hirr, hsep, -⟩ := hG
  obtain ⟨z, hvz, huz⟩ := hsep v u (Ne.symm huv)
  have hxb : val D (sem_two u z) b = true := sem_val_of_supp hS hu (by simp [sem_two])
  have hyb : val D (sem_ins v (sem_two u z)) b = true :=
    sem_val_of_supp hS hu (by simp [sem_ins, sem_two])
  have hout := sem_dom_eq hS _ _ v (sem_ins_agree v (sem_two u z)) b hdom (by rw [hxb, hyb])
  have h1 : ¬ sem_Edge G (sem_two u z) := by
    rintro ⟨a, c, hac, ha, hc⟩
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at ha hc
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · exact hirr _ hac
    · exact huz hac
    · exact huz (hsym _ _ hac)
    · exact hirr _ hac
  have h2 : sem_Edge G (sem_ins v (sem_two u z)) :=
    ⟨v, z, hvz, sem_ins_self v _, by simp [sem_ins, sem_two]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact h1 ((hC _).mp h3)

/-- The first branching carrier of an eligible label: pure, and reached from the input
through single-reader wires. -/
theorem sem_first_branch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) (v : Fin n)
    (hv : v ∈ eligSet n D) :
    ∃ b, 2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
  classical
  have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hch : sem_Chain n D v.val (Nat.find hex) :=
    sem_carrier_chain hS v _ h2 (fun u hu huv => by
      have := Nat.find_min hex hu
      by_contra hc
      exact this ⟨by omega, huv⟩)
  exact ⟨Nat.find hex, h1, Finset.Subset.antisymm
    (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2), hch⟩

/-- A choice of first branches: pure, branching, and on the single-reader chain. -/
def sem_FirstBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v)

theorem sem_exists_firstBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_FirstBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · obtain ⟨b, hb⟩ := sem_first_branch hG hS hC v hv
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_firstBranch_pure {b : Fin n → ℕ} (hb : sem_FirstBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

theorem sem_exists_pureBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, PureBranch n D b := by
  obtain ⟨b, hb⟩ := sem_exists_firstBranch hG hS hC
  exact ⟨b, sem_firstBranch_pure hb⟩

/-! ### Ineligible labels -/

theorem sem_mem_inelig {v : Fin n} : v ∈ ineligSet n D ↔ v ∉ eligSet n D := by
  simp [ineligSet]

/-- Every carrier of an ineligible label is reached through single-reader wires. -/
theorem sem_inelig_chain (hS : Strict n D) {v : Fin n} (hv : v ∈ ineligSet n D) {w : ℕ}
    (hw : v ∈ supp n D w) : sem_Chain n D v.val w :=
  sem_carrier_chain hS v w hw (fun u _ hu => mem_ineligSet.mp hv u hu)

/-- Every carrier of an ineligible label is pure. -/
theorem sem_inelig_pure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {w : ℕ} (hw : v ∈ supp n D w) : supp n D w = {v} :=
  Finset.Subset.antisymm (sem_dom_pure hG hS hC v w (sem_chain_dom hS (sem_inelig_chain hS hv hw)))
    (Finset.singleton_subset_iff.mpr hw)

theorem sem_mem_carrier1 {v : Fin n} {w : ℕ} : w ∈ carrierT n D {v} ↔ v ∈ supp n D w := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, u, hu⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at hu
    exact hu.2 ▸ hu.1
  · intro h
    exact ⟨sem_supp_lt h, v, Finset.mem_inter.mpr ⟨h, Finset.mem_singleton_self v⟩⟩

theorem sem_mem_exit1 {v : Fin n} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D {v}) ↔
    e.1 < D.length ∧ v ∈ supp n D (src D e) ∧ v ∉ supp n D (n + e.1) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_carrier1]

theorem sem_inelig_surplus {v : Fin n} (hv : v ∈ ineligSet n D) :
    surplusOn D (carrierT n D {v}) = 0 := by
  unfold surplusOn
  refine Finset.sum_eq_zero (fun w hw => ?_)
  have := mem_ineligSet.mp hv w (sem_mem_carrier1.mp hw)
  omega

/-! ### Joint meeting of an edge -/

/-- Every edge `uv` has an AND gate true on `{u, v}`, carrying neither endpoint, whose two
operands carry `u` without `v` and `v` without `u`. -/
theorem sem_joint_meeting (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) :
    ∃ j, j < D.length ∧ tag D j = true ∧ val D (sem_two u v) (n + j) = true ∧
      u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) ∧
      ∃ s : Bool, u ∈ supp n D (src D (j, s)) ∧ v ∉ supp n D (src D (j, s)) ∧
        v ∈ supp n D (src D (j, !s)) ∧ u ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ w, val D (sem_two u v) w = true ∧ u ∉ supp n D w ∧ v ∉ supp n D w :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), by rw [sem_supp_out hG hC]; simp,
      by rw [sem_supp_out hG hC]; simp⟩
  obtain ⟨hw1, hw2, hw3⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true →
      u ∈ supp n D a ∨ v ∈ supp n D a := by
    intro a ha hva
    by_contra hc
    rw [not_or] at hc
    exact Nat.find_min hex ha ⟨hva, hc.1, hc.2⟩
  generalize Nat.find hex = w at hw1 hw2 hw3 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hc' : w < n := by omega
    rw [val_input D _ w hc'] at hw1
    have hs : supp n D w = {⟨w, hc'⟩} := supp_input D ⟨w, hc'⟩
    rw [hs, Finset.mem_singleton] at hw2 hw3
    simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hw1
    rcases hw1 with h | h
    · exact hw2 h.symm
    · exact hw3 h.symm
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  rw [supp_gate hS j hj] at hw2 hw3
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1 hw2 hw3
    simp only [gop_false, Bool.or_eq_true] at hw1
    simp only [Bool.false_eq_true, ite_false, Finset.mem_union, not_or] at hw2 hw3
    rcases hw1 with h | h
    · rcases hmin _ ha h with h' | h'
      · exact hw2.1 h'
      · exact hw3.1 h'
    · rcases hmin _ hb h with h' | h'
      · exact hw2.2 h'
      · exact hw3.2 h'
  · rw [ht] at hw1 hw2 hw3
    simp only [gop_true, Bool.and_eq_true] at hw1
    simp only [ite_true, Finset.mem_inter, not_and] at hw2 hw3
    have hsupp : u ∉ supp n D (n + j) ∧ v ∉ supp n D (n + j) := by
      rw [sem_supp_and hS hj ht]
      simp only [Finset.mem_inter, not_and]
      exact ⟨hw2, hw3⟩
    refine ⟨j, hj, ht, hval, hsupp.1, hsupp.2, ?_⟩
    rcases hmin _ ha hw1.1 with hA | hA
    · have hB : u ∉ supp n D (opB D j) := hw2 hA
      have hBv : v ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_left hB
      exact ⟨false, by simpa [src] using hA, by simpa [src] using fun h => hw3 h hBv,
        by simpa [src] using hBv, by simpa [src] using hB⟩
    · have hB : v ∉ supp n D (opB D j) := hw3 hA
      have hBu : u ∈ supp n D (opB D j) := (hmin _ hb hw1.2).resolve_right hB
      exact ⟨true, by simpa [src] using hBu, by simpa [src] using hB,
        by simpa [src] using hA, by simpa [src] using fun h => hw2 h hBu⟩

/-! ### The unique consumer of an ineligible label -/

/-- An ineligible label has one consuming position: an AND gate with empty support, a pure
operand on the label side, and every neighbour carried by the opposite operand. Its carrier
has no internal merge. -/
theorem sem_inelig_consumer (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {v : Fin n} (hv : v ∈ ineligSet n D) :
    ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧ supp n D (src D e) = {v} ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G v a → a ∈ supp n D (src D (e.1, !e.2))) ∧
      exitArcs n D (carrierT n D {v}) = {e} ∧ merges n D (carrierT n D {v}) = ∅ := by
  have hS := h.1
  have hfl := carrier_flow_union h {v} (by rw [sem_supp_out hG hC]; simp)
  rw [sem_inelig_surplus hv, Finset.card_singleton] at hfl
  have hmeet : ∀ a, G v a → ∃ j s, j < D.length ∧ tag D j = true ∧
      (j, s) ∈ exitArcs n D (carrierT n D {v}) ∧ a ∈ supp n D (src D (j, !s)) := by
    intro a hva
    obtain ⟨j, hj, ht, -, hju, -, s, h1, -, h3, -⟩ := sem_joint_meeting hG hS hC hva
    exact ⟨j, s, hj, ht, sem_mem_exit1.mpr ⟨hj, h1, hju⟩, h3⟩
  obtain ⟨a0, ha0, -⟩ := hG.2.2.2 v v
  obtain ⟨j0, s0, hj0, ht0, hm0, -⟩ := hmeet a0 ha0
  have hcard : (exitArcs n D (carrierT n D {v})).card = 1 := by
    have := Finset.card_pos.mpr ⟨_, hm0⟩
    omega
  have hmer : merges n D (carrierT n D {v}) = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  rw [he, Finset.mem_singleton] at hm0
  subst hm0
  have hsrc : supp n D (src D (j0, s0)) = {v} :=
    sem_inelig_pure hG hS hC hv
      (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.1
  have hnot : v ∉ supp n D (n + j0) :=
    (sem_mem_exit1.mp (by rw [he]; exact Finset.mem_singleton_self _)).2.2
  refine ⟨(j0, s0), hj0, ht0, hsrc, ?_, ?_, he, hmer⟩
  · refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
    have hx2 := sem_supp_and_sub hS hj0 ht0 s0 hx
    rw [hsrc, Finset.mem_singleton] at hx2
    exact hnot (hx2 ▸ hx)
  · intro a hva
    obtain ⟨j, s, -, -, hm, ha⟩ := hmeet a hva
    rw [he, Finset.mem_singleton] at hm
    rw [Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact ha

/-- Every gate carrying an ineligible label is an OR. -/
theorem sem_inelig_or (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) {v : Fin n}
    (hv : v ∈ ineligSet n D) {j : ℕ} (hj : j < D.length) (hc : v ∈ supp n D (n + j)) :
    tag D j = false := by
  obtain ⟨e, -, -, -, -, -, -, hmer⟩ := sem_inelig_consumer hG h hC hv
  by_contra ht
  rw [Bool.not_eq_false] at ht
  have hc2 := hc
  rw [sem_supp_and h.1 hj ht, Finset.mem_inter] at hc2
  have : j ∈ merges n D (carrierT n D {v}) := by
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sem_mem_carrier1.mpr hc, sem_mem_carrier1.mpr hc2.1, sem_mem_carrier1.mpr hc2.2⟩
  rw [hmer] at this
  exact Finset.notMem_empty _ this

/-- The eligible labels form a vertex cover. -/
theorem sem_elig_cover (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) : u ∈ eligSet n D ∨ v ∈ eligSet n D := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨eu, -, -, -, -, hnu, hxu, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.1)
  obtain ⟨ev, -, -, hsv, -, -, hxv, -⟩ := sem_inelig_consumer hG h hC (sem_mem_inelig.mpr hc.2)
  obtain ⟨j, hj, -, -, hju, hjv, s, h1, -, h3, -⟩ := sem_joint_meeting hG h.1 hC huv
  have m1 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, h1, hju⟩
  have m2 : (j, !s) ∈ exitArcs n D (carrierT n D {v}) := sem_mem_exit1.mpr ⟨hj, h3, hjv⟩
  rw [hxu, Finset.mem_singleton] at m1
  rw [hxv, Finset.mem_singleton] at m2
  subst m1
  subst m2
  obtain ⟨a, hua, hav⟩ := hG.2.2.2 u v
  have h5 : a ∈ supp n D (src D (j, !s)) := hnu a hua
  rw [hsv, Finset.mem_singleton] at h5
  exact hav h5

/-! ### Exposure and first productions of projected masks -/

theorem sem_ind_no_edge {A : Finset (Fin n)} (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) :
    ¬ sem_Edge G (sem_ind A) := by
  rintro ⟨a, c, hac, ha, hc⟩
  simp only [sem_ind, decide_eq_true_eq] at ha hc
  exact hA a ha c hc hac

/-- Exposure: for an independent set `A` and a label `x` with a neighbour in `A`, some AND
position consuming `x` has an operand whose whole singleton support misses `A`. -/
theorem sem_exposure (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (A : Finset (Fin n)) (hA : ∀ a ∈ A, ∀ b ∈ A, ¬ G a b) (x : Fin n)
    (hnb : ∃ a ∈ A, G x a) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ x ∈ supp n D (src D (j, s)) ∧
      x ∉ supp n D (n + j) ∧ Disjoint (supp n D (src D (j, s))) A := by
  by_contra hcon
  have hmask : ∀ j s, j < D.length → tag D j = true → x ∈ supp n D (src D (j, s)) →
      x ∉ supp n D (n + j) → val D (sem_ind A) (src D (j, s)) = true ∧
        val D (sem_ins x (sem_ind A)) (src D (j, s)) = true := by
    intro j s hj ht h1 h2
    have hnd : ¬ Disjoint (supp n D (src D (j, s))) A :=
      fun hd => hcon ⟨j, s, hj, ht, h1, h2, hd⟩
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨a, ha1, ha2⟩ := hnd
    exact ⟨sem_val_of_supp hS ha1 (by simp [sem_ind, ha2]),
      sem_val_of_supp hS ha1 (by simp [sem_ins, sem_ind, ha2])⟩
  have key : ∀ w, x ∉ supp n D w → val D (sem_ind A) w = val D (sem_ins x (sem_ind A)) w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hn : w < n
      · rw [val_input D _ w hn, val_input D _ w hn]
        have hs : supp n D w = {⟨w, hn⟩} := supp_input D ⟨w, hn⟩
        rw [hs, Finset.mem_singleton] at hw
        exact sem_ins_agree x _ _ (fun hc => hw hc.symm)
      · by_cases hlt : w < n + D.length
        · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [val_gate hS _ j hj, val_gate hS _ j hj]
          cases ht : tag D j
          · rw [sem_supp_or hS hj ht, Finset.mem_union, not_or] at hw
            rw [ih _ ha hw.1, ih _ hb hw.2]
          · have hw2 := hw
            rw [sem_supp_and hS hj ht, Finset.mem_inter, not_and] at hw2
            by_cases hxa : x ∈ supp n D (opA D j)
            · have h1 := hmask j false hj ht (by rw [sb_src_false]; exact hxa) hw
              rw [sb_src_false] at h1
              rw [ih _ hb (hw2 hxa), h1.1, h1.2]
            · by_cases hxb : x ∈ supp n D (opB D j)
              · have h1 := hmask j true hj ht (by rw [sb_src_true]; exact hxb) hw
                rw [sb_src_true] at h1
                rw [ih _ ha hxa, h1.1, h1.2]
              · rw [ih _ ha hxa, ih _ hb hxb]
        · rw [val_ge D _ w (by omega), val_ge D _ w (by omega)]
  have hout := key (outW n D) (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  obtain ⟨a, ha, hxa⟩ := hnb
  have h2 : sem_Edge G (sem_ins x (sem_ind A)) :=
    ⟨x, a, hxa, sem_ins_self x _, by simp [sem_ins, sem_ind, ha]⟩
  have h3 := (hC _).mpr h2
  rw [← hout] at h3
  exact sem_ind_no_edge hA ((hC _).mp h3)

/-- First production of a projected mask `M` with at least two labels: it happens at a
gate that is an internal merge of the union carrier of `T`. An AND has two strictly
larger parent masks; an OR has two nonempty strictly smaller parent masks with union `M`. -/
theorem sem_first_mask (hS : Strict n D) (T M : Finset (Fin n)) (hM : 2 ≤ M.card) (w : ℕ)
    (hw : supp n D w ∩ T = M) :
    ∃ j, j < D.length ∧ n + j ≤ w ∧ supp n D (n + j) ∩ T = M ∧
      j ∈ merges n D (carrierT n D T) ∧ (∀ u, u < n + j → supp n D u ∩ T ≠ M) ∧
      ((tag D j = true ∧ M ⊂ supp n D (opA D j) ∩ T ∧ M ⊂ supp n D (opB D j) ∩ T) ∨
        (tag D j = false ∧ supp n D (opA D j) ∩ T ⊂ M ∧ supp n D (opB D j) ∩ T ⊂ M ∧
          (supp n D (opA D j) ∩ T) ∪ (supp n D (opB D j) ∩ T) = M ∧
          (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty)) := by
  classical
  have hex : ∃ u, supp n D u ∩ T = M := ⟨w, hw⟩
  have hle : Nat.find hex ≤ w := Nat.find_min' hex hw
  have hmin : ∀ u, u < Nat.find hex → supp n D u ∩ T ≠ M := fun u hu => Nat.find_min hex hu
  have hspec := Nat.find_spec hex
  generalize Nat.find hex = f at hle hmin hspec
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hmem : ∀ {u : ℕ}, (supp n D u ∩ T).Nonempty → u ∈ carrierT n D T := by
    intro u hu
    obtain ⟨v, hv⟩ := hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (sem_supp_lt (Finset.mem_inter.mp hv).1), v, hv⟩
  have hflt : f < n + D.length := by
    obtain ⟨v, hv⟩ := hMne
    rw [← hspec] at hv
    exact sem_supp_lt (Finset.mem_inter.mp hv).1
  have hfn : n ≤ f := by
    by_contra hc
    have hc' : f < n := by omega
    have hs : supp n D f = {⟨f, hc'⟩} := supp_input D ⟨f, hc'⟩
    have h1 : M.card ≤ 1 := by
      rw [← hspec, hs]
      exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  refine ⟨j, hj, hle, hspec, ?_, hmin, ?_⟩
  · have hAB : (supp n D (opA D j) ∩ T).Nonempty ∧ (supp n D (opB D j) ∩ T).Nonempty := by
      cases ht : tag D j
      · rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
        constructor
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.empty_union] at hspec
          exact hnb hspec
        · rw [Finset.nonempty_iff_ne_empty]
          intro he
          rw [he, Finset.union_empty] at hspec
          exact hna hspec
      · rw [sem_supp_and hS hj ht] at hspec
        obtain ⟨v, hv⟩ := hMne
        rw [← hspec] at hv
        simp only [Finset.mem_inter] at hv
        exact ⟨⟨v, Finset.mem_inter.mpr ⟨hv.1.1, hv.2⟩⟩, ⟨v, Finset.mem_inter.mpr ⟨hv.1.2, hv.2⟩⟩⟩
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hmem (by rw [hspec]; exact hMne), hmem hAB.1, hmem hAB.2⟩
  · cases ht : tag D j
    · right
      rw [sem_supp_or hS hj ht, Finset.union_inter_distrib_right] at hspec
      have hsa : supp n D (opA D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_left
      have hsb : supp n D (opB D j) ∩ T ⊆ M := by rw [← hspec]; exact Finset.subset_union_right
      refine ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, hnb⟩, hspec, ?_, ?_⟩
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.empty_union] at hspec
        exact hnb hspec
      · rw [Finset.nonempty_iff_ne_empty]
        intro he
        rw [he, Finset.union_empty] at hspec
        exact hna hspec
    · left
      rw [sem_supp_and hS hj ht] at hspec
      have hsa : M ⊆ supp n D (opA D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.1, hv.2⟩
      have hsb : M ⊆ supp n D (opB D j) ∩ T := by
        rw [← hspec]
        intro v hv
        simp only [Finset.mem_inter] at hv ⊢
        exact ⟨hv.1.2, hv.2⟩
      exact ⟨rfl, Finset.ssubset_iff_subset_ne.mpr ⟨hsa, Ne.symm hna⟩,
        Finset.ssubset_iff_subset_ne.mpr ⟨hsb, Ne.symm hnb⟩⟩

end SemCore

/-! ### Heawood forms: the two hypotheses of Layer 1 -/

theorem sem_hw_second : ∀ u v : Fin 14, ∃ a, hc_adjB u a = true ∧ a ≠ v := by decide +kernel

theorem sem_heawood_gr : sem_Gr (fun u v : Fin 14 => Adj u v) :=
  ⟨fun _ _ => adj_symm, adj_irrefl, nbr_diff_exists, fun u v => by
    obtain ⟨a, h1, h2⟩ := sem_hw_second u v
    exact ⟨a, (hc_adjB_iff u a).mp h1, h2⟩⟩

theorem sem_heawood_comp {D : Dag} (hD : Correct D) : sem_Comp 14 (fun u v : Fin 14 => Adj u v) D :=
  fun x => (hD x).trans (heawoodEdge_iff_adj x)

/-- Every correct Heawood DAG has a pure first-branch choice. -/
theorem exists_pureBranch {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    ∃ b : Fin 14 → ℕ, PureBranch 14 D b :=
  sem_exists_pureBranch sem_heawood_gr h.1 (sem_heawood_comp hD)

/-- The eligible labels of a correct Heawood DAG form a vertex cover. -/
theorem elig_isCover {D : Dag} (h : StrictLive 14 D) (hD : Correct D) :
    IsCover (eligSet 14 D) :=
  fun _ _ huv => sem_elig_cover sem_heawood_gr h (sem_heawood_comp hD) huv

/-- From an official circuit of size at most 26 to a canonical strict live DAG. -/
theorem heawood_wlog_canon (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ HeawoodEdge x)
    (hsize : C.size ≤ 26) :
    ∃ D : Dag, StrictLive 14 D ∧ Correct D ∧ D.length ≤ 26 ∧
      totalSurplus 14 D + 13 = D.length ∧ totalSurplus 14 D ≤ 13 ∧
      7 ≤ (eligSet 14 D).card ∧ (eligSet 14 D).card ≤ Bplus 14 D ∧
      Bplus 14 D ≤ totalSurplus 14 D ∧ ineligSet 14 D ∈ canonI := by
  obtain ⟨D0, h0, hlen0, hD0⟩ := heawood_normalize C hmono hC
  have hlen : D0.length ≤ 26 := by omega
  obtain ⟨b, hb⟩ := exists_pureBranch h0 hD0
  have hcov := elig_isCover h0 hD0
  obtain ⟨hne, -⟩ := heawood_inelig_bounds h0 hlen b hb hcov
  obtain ⟨D, h1, h2, h3, h4, h5, -, h7, h8⟩ :=
    heawood_wlog h0 hD0 ((heawood_cover_iff_indep D0).mp hcov) hne
  have hlen' : D.length ≤ 26 := by omega
  obtain ⟨b', hb'⟩ := exists_pureBranch h1 h2
  obtain ⟨p1, p2, p3, p4⟩ := heawood_p_bounds h1 hlen' b' hb' (elig_isCover h1 h2)
  exact ⟨D, h1, h2, hlen', (heawood_budget h1 hlen').1, p4, p1, p2, p3, h8⟩

/-! ### Signed consumption codes, cover-freeness, private positions -/

/-- The consumption code of `x`: the operand positions carrying `x` at gates that do not. -/
def sem_W (n : ℕ) (D : Dag) (x : Fin n) : Finset (ℕ × Bool) := exitArcs n D (carrierT n D {x})

/-- The opposite operand position at the same gate. -/
def sem_bar (e : ℕ × Bool) : ℕ × Bool := (e.1, !e.2)

section SemCodes

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_W {x : Fin n} {e : ℕ × Bool} : e ∈ sem_W n D x ↔
    e.1 < D.length ∧ x ∈ supp n D (src D e) ∧ x ∉ supp n D (n + e.1) := sem_mem_exit1

theorem sem_bar_bar (e : ℕ × Bool) : sem_bar (sem_bar e) = e := by simp [sem_bar]

theorem sem_bar_ne (e : ℕ × Bool) : sem_bar e ≠ e := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [sem_bar] at h2

theorem sem_same_gate {e f : ℕ × Bool} (h : e.1 = f.1) : f = e ∨ f = sem_bar e := by
  obtain ⟨j, s⟩ := e
  obtain ⟨k, t⟩ := f
  simp only at h
  subst h
  cases s <;> cases t <;> simp [sem_bar]

/-- A consuming gate is an AND. -/
theorem sem_W_and (hS : Strict n D) {x : Fin n} {e : ℕ × Bool} (he : e ∈ sem_W n D x) :
    tag D e.1 = true := by
  obtain ⟨hj, h1, h2⟩ := sem_mem_W.mp he
  by_contra ht
  rw [Bool.not_eq_true] at ht
  apply h2
  rw [sem_supp_or hS hj ht, Finset.mem_union]
  obtain ⟨j, s⟩ := e
  cases s
  · left; simpa [src] using h1
  · right; simpa [src] using h1

/-- Single-label flow: `|W_x| + M_x = 1 + B_x`. -/
theorem sem_flow1 (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + surplusOn D (carrierT n D {x}) := by
  have h1 := carrier_flow_union h {x} (by rw [sem_supp_out hG hC]; simp)
  rwa [Finset.card_singleton] at h1

/-- Every edge is met at opposite consumption positions. -/
theorem sem_edge_slots (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x y : Fin n}
    (hxy : G x y) : ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      y ∉ supp n D (src D e) ∧ x ∉ supp n D (src D (sem_bar e)) ∧
      val D (sem_two x y) (n + e.1) = true := by
  obtain ⟨j, hj, -, hval, hju, hjv, s, h1, h2, h3, h4⟩ := sem_joint_meeting hG hS hC hxy
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, hju⟩, sem_mem_W.mpr ⟨hj, h3, hjv⟩, h2, h4, hval⟩

/-- Cover-freeness in operand form: if `a`, `b` are nonadjacent and `x` has a neighbour `y`
adjacent to neither, some position consuming `x` has an operand carrying neither `a` nor
`b`. The case `a = b` is allowed. -/
theorem sem_cover_free (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {x a b y : Fin n} (hab : ¬ G a b) (hxy : G x y) (hya : ¬ G y a) (hyb : ¬ G y b) :
    ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) ∧ b ∉ supp n D (src D e) := by
  have hsym := hG.1
  have hirr := hG.2.1
  have hA : ∀ u ∈ ({a, b, y} : Finset (Fin n)), ∀ v ∈ ({a, b, y} : Finset (Fin n)),
      ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;> rw [hu, hv]
    · exact hirr a
    · exact hab
    · exact fun h => hya (hsym _ _ h)
    · exact fun h => hab (hsym _ _ h)
    · exact hirr b
    · exact fun h => hyb (hsym _ _ h)
    · exact hya
    · exact hyb
    · exact hirr y
  obtain ⟨j, s, hj, -, h1, h2, hd⟩ := sem_exposure hG hS hC {a, b, y} hA x ⟨y, by simp, hxy⟩
  exact ⟨(j, s), sem_mem_W.mpr ⟨hj, h1, h2⟩, fun h => Finset.disjoint_left.mp hd h (by simp),
    fun h => Finset.disjoint_left.mp hd h (by simp)⟩

/-- Antichain property in operand form. -/
theorem sem_antichain (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {x a : Fin n}
    (hxa : x ≠ a) : ∃ e, e ∈ sem_W n D x ∧ a ∉ supp n D (src D e) := by
  obtain ⟨z, hxz, haz⟩ := hG.2.2.1 x a hxa
  obtain ⟨e, he, h1, -⟩ := sem_cover_free hG hS hC (a := a) (b := a) (hG.2.1 a) hxz
    (fun h => haz (hG.1 _ _ h)) (fun h => haz (hG.1 _ _ h))
  exact ⟨e, he, h1⟩

/-- A necessary free AND: an eligible edge forces an AND gate with empty support, two
supported operands, true on the edge, none of whose operands carries an ineligible label. -/
theorem sem_free_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u v : Fin n} (huv : G u v) (hu : u ∈ eligSet n D) (hv : v ∈ eligSet n D) :
    ∃ j, j < D.length ∧ tag D j = true ∧ supp n D (n + j) = ∅ ∧
      (supp n D (opA D j)).Nonempty ∧ (supp n D (opB D j)).Nonempty ∧
      val D (sem_two u v) (n + j) = true ∧
      ∀ i ∈ ineligSet n D, i ∉ supp n D (opA D j) ∧ i ∉ supp n D (opB D j) := by
  classical
  have hS := h.1
  have hex : ∃ w, val D (sem_two u v) w = true ∧ supp n D w = ∅ :=
    ⟨outW n D, (hC _).2 (sem_two_edge huv), sem_supp_out hG hC⟩
  obtain ⟨hw1, hw2⟩ := Nat.find_spec hex
  have hmin : ∀ a, a < Nat.find hex → val D (sem_two u v) a = true → (supp n D a).Nonempty := by
    intro a ha hva
    rw [Finset.nonempty_iff_ne_empty]
    exact fun hc => Nat.find_min hex ha ⟨hva, hc⟩
  generalize Nat.find hex = w at hw1 hw2 hmin
  have hlt : w < n + D.length := by
    by_contra hc
    rw [val_ge D _ w (by omega)] at hw1
    exact Bool.false_ne_true hw1
  have hn : n ≤ w := by
    by_contra hc
    have hs : supp n D w = {⟨w, by omega⟩} := supp_input D ⟨w, by omega⟩
    rw [hs] at hw2
    exact Finset.singleton_ne_empty _ hw2
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hval := hw1
  rw [val_gate hS _ j hj] at hw1
  have hdead : ∀ w', w' < n + j → ∀ i ∈ ineligSet n D, i ∈ supp n D w' →
      val D (sem_two u v) w' = false := by
    intro w'
    induction w' using Nat.strong_induction_on with
    | _ w' ih =>
      intro hlt' i hi hiw
      have hpure := sem_inelig_pure hG hS hC hi hiw
      by_cases hn' : w' < n
      · have hs : supp n D w' = {⟨w', hn'⟩} := supp_input D ⟨w', hn'⟩
        rw [hs, Finset.mem_singleton] at hiw
        rw [val_input D _ w' hn', ← hiw]
        have hiu : i ≠ u := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hu)
        have hiv : i ≠ v := fun hc => (sem_mem_inelig.mp hi) (hc ▸ hv)
        simp [sem_two, hiu, hiv]
      · obtain ⟨j', rfl⟩ : ∃ j', w' = n + j' := ⟨w' - n, by omega⟩
        have hj' : j' < D.length := by omega
        obtain ⟨ha', hb', -⟩ := hS j' hj'
        have ht' := sem_inelig_or hG h hC hi hj' hiw
        have hop : ∀ a, a < n + j' → supp n D a ⊆ {i} → val D (sem_two u v) a = false := by
          intro a hlt2 hsub
          by_cases hia : i ∈ supp n D a
          · exact ih a hlt2 (by omega) i hi hia
          · by_contra hc
            rw [Bool.not_eq_false] at hc
            obtain ⟨q, hq⟩ := hmin a (by omega) hc
            have := hsub hq
            rw [Finset.mem_singleton] at this
            exact hia (this ▸ hq)
        rw [sem_supp_or hS hj' ht'] at hpure
        rw [val_gate hS _ j' hj', ht', gop_false,
          hop _ ha' (by rw [← hpure]; exact Finset.subset_union_left),
          hop _ hb' (by rw [← hpure]; exact Finset.subset_union_right)]
        rfl
  cases ht : tag D j
  · exfalso
    rw [ht] at hw1
    simp only [gop_false, Bool.or_eq_true] at hw1
    rw [sem_supp_or hS hj ht, Finset.union_eq_empty] at hw2
    rcases hw1 with h1 | h1
    · have := hmin _ ha h1
      rw [hw2.1] at this
      exact Finset.not_nonempty_empty this
    · have := hmin _ hb h1
      rw [hw2.2] at this
      exact Finset.not_nonempty_empty this
  · rw [ht] at hw1
    simp only [gop_true, Bool.and_eq_true] at hw1
    refine ⟨j, hj, ht, hw2, hmin _ ha hw1.1, hmin _ hb hw1.2, hval, fun i hi => ⟨?_, ?_⟩⟩
    · intro hc
      have := hdead _ ha i hi hc
      rw [hw1.1] at this
      exact Bool.noConfusion this
    · intro hc
      have := hdead _ hb i hi hc
      rw [hw1.2] at this
      exact Bool.noConfusion this

end SemCodes

/-! ### Heawood forms of cover-freeness and the private-position lemma -/

theorem sem_hw_third : ∀ x a b : Fin 14, x ≠ a → x ≠ b → hc_adjB a b = false →
    ∃ y, hc_adjB x y = true ∧ hc_adjB y a = false ∧ hc_adjB y b = false := by decide +kernel

theorem sem_hw_two_nbrs : ∀ i x : Fin 14, ∃ r s, r ≠ s ∧ hc_adjB i r = true ∧
    hc_adjB i s = true ∧ r ≠ x ∧ s ≠ x := by decide +kernel

theorem sem_hw_common : ∀ r s t i : Fin 14, r ≠ s → hc_adjB i r = true → hc_adjB i s = true →
    hc_adjB t r = true → hc_adjB t s = true → t = i := by decide +kernel

theorem sem_adjB_false {u v : Fin 14} : hc_adjB u v = false ↔ ¬ Adj u v := by
  rw [← hc_adjB_iff, Bool.not_eq_true]

/-- Heawood cover-freeness: for `x` different from nonadjacent `a`, `b` (possibly equal),
some position consuming `x` has an operand carrying neither. -/
theorem sem_hw_cover_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {x a b : Fin 14}
    (hxa : x ≠ a) (hxb : x ≠ b) (hab : ¬ Adj a b) :
    ∃ e, e ∈ sem_W 14 D x ∧ a ∉ supp 14 D (src D e) ∧ b ∉ supp 14 D (src D e) := by
  obtain ⟨y, h1, h2, h3⟩ := sem_hw_third x a b hxa hxb (sem_adjB_false.mpr hab)
  exact sem_cover_free sem_heawood_gr h.1 (sem_heawood_comp hD) hab ((hc_adjB_iff x y).mp h1)
    (sem_adjB_false.mp h2) (sem_adjB_false.mp h3)

/-- The private-position lemma: if the code of `x` has at most two positions and contains
the position opposite the pure operand of an ineligible `i`, then it is that position
together with one position `Z` consuming no other label, at a gate assigned to no
ineligible label. -/
theorem sem_hw_private_slot {D : Dag} (h : StrictLive 14 D) (hD : Correct D) {i x : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hxi : x ≠ i) {e : ℕ × Bool} (he : sem_W 14 D i = {e})
    (hY : sem_bar e ∈ sem_W 14 D x) (hc : (sem_W 14 D x).card ≤ 2) :
    ∃ Z, Z ≠ sem_bar e ∧ sem_W 14 D x = {sem_bar e, Z} ∧ (∀ t, t ≠ x → Z ∉ sem_W 14 D t) ∧
      ∀ i' ∈ ineligSet 14 D, ∀ e', sem_W 14 D i' = {e'} → Z.1 ≠ e'.1 := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  have hcons : ∀ i' ∈ ineligSet 14 D, ∀ e', sem_W 14 D i' = {e'} →
      supp 14 D (src D e') = {i'} ∧ supp 14 D (14 + e'.1) = ∅ ∧
        ∀ q, Adj i' q → q ∈ supp 14 D (src D (sem_bar e')) := by
    intro i' hi' e' he'
    obtain ⟨e0, -, -, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi'
    have h1 : ({e'} : Finset (ℕ × Bool)) = {e0} := he'.symm.trans hx0
    have h2 : e' = e0 := Finset.singleton_injective h1
    subst h2
    exact ⟨hsrc0, hemp0, hnb0⟩
  obtain ⟨hsrc, -, hYn⟩ := hcons i hi e he
  obtain ⟨r, s, hrs, hir, his, hrx, hsx⟩ := sem_hw_two_nbrs i x
  rw [hc_adjB_iff] at hir his
  obtain ⟨Z, hZ, hZr⟩ := sem_antichain hG hS hC (x := x) (a := r) (Ne.symm hrx)
  have hZY : Z ≠ sem_bar e := by
    rintro rfl
    exact hZr (hYn r hir)
  have hW : sem_W 14 D x = {sem_bar e, Z} := by
    symm
    refine Finset.eq_of_subset_of_card_le (fun f hf => ?_) ?_
    · rw [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact hY
      · exact hZ
    · rw [Finset.card_pair (Ne.symm hZY)]; exact hc
  have hpriv : ∀ t, t ≠ x → Z ∉ sem_W 14 D t := by
    intro t htx hZt
    have key : ∀ q, q ≠ x → q ∈ supp 14 D (src D (sem_bar e)) → Adj q t := by
      intro q hqx hq
      by_contra hqt
      obtain ⟨f, hf, h1, h2⟩ := sem_hw_cover_free h hD (x := x) (a := q) (b := t)
        (Ne.symm hqx) (Ne.symm htx) hqt
      rw [hW, Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact h1 hq
      · exact h2 (sem_mem_W.mp hZt).2.1
    have hrt := adj_symm (key r hrx (hYn r hir))
    have hst := adj_symm (key s hsx (hYn s his))
    have hti : t = i := sem_hw_common r s t i hrs ((hc_adjB_iff _ _).mpr hir)
      ((hc_adjB_iff _ _).mpr his) ((hc_adjB_iff _ _).mpr hrt) ((hc_adjB_iff _ _).mpr hst)
    rw [hti, he, Finset.mem_singleton] at hZt
    have hx2 := (sem_mem_W.mp hZ).2.1
    rw [hZt, hsrc, Finset.mem_singleton] at hx2
    exact hxi hx2
  refine ⟨Z, hZY, hW, hpriv, ?_⟩
  intro i' hi' e' he' hgate
  obtain ⟨-, hemp', hYn'⟩ := hcons i' hi' e' he'
  have hxi' : x ≠ i' := by
    intro hc
    have h1 : (sem_W 14 D x).card = 2 := by rw [hW, Finset.card_pair (Ne.symm hZY)]
    rw [hc, he', Finset.card_singleton] at h1
    omega
  rcases sem_same_gate hgate.symm with h1 | h1
  · exact hpriv i' (Ne.symm hxi') (by rw [he', Finset.mem_singleton]; exact h1)
  · obtain ⟨r', s', hrs', hir', his', hrx', -⟩ := sem_hw_two_nbrs i' x
    rw [hc_adjB_iff] at hir'
    refine hpriv r' hrx' (sem_mem_W.mpr ⟨(sem_mem_W.mp hZ).1, ?_, ?_⟩)
    · rw [h1]; exact hYn' r' hir'
    · rw [hgate, hemp']; exact Finset.notMem_empty _

/-! ### Zero-merge carriers: single-reader arms and common terminals -/

theorem sem_rtg_comparable {α : Type} {R : α → α → Prop}
    (hfun : ∀ a a' b, R a b → R a' b → a = a') {u v c : α}
    (hu : Relation.ReflTransGen R u c) (hv : Relation.ReflTransGen R v c) :
    Relation.ReflTransGen R u v ∨ Relation.ReflTransGen R v u := by
  induction hu with
  | refl => exact Or.inr hv
  | tail hab hbc ih =>
    rcases Relation.ReflTransGen.cases_tail hv with h | ⟨b', hvb', hb'c⟩
    · left
      rw [← h]
      exact Relation.ReflTransGen.tail hab hbc
    · have hbb : b' = _ := hfun _ _ _ hb'c hbc
      rw [hbb] at hvb'
      exact ih hvb'

/-- A first-branch choice that is also the earliest branching carrier. -/
def sem_MinBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v} ∧ sem_Chain n D v.val (b v) ∧
    ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b v ≤ w

/-- Arm steps for a label set `X`: out of a single-reader wire, both ends carrying all of `X`. -/
def sem_Arm (n : ℕ) (D : Dag) (X : Finset (Fin n)) (a b : ℕ) : Prop :=
  sem_step n D a b ∧ fanout D a = 1 ∧ ∀ x ∈ X, x ∈ supp n D a ∧ x ∈ supp n D b

section SemArms

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_rtg_le (hS : Strict n D) {R : ℕ → ℕ → Prop} (hR : ∀ a b, R a b → sem_step n D a b)
    {a b : ℕ} (h : Relation.ReflTransGen R a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans ih (le_of_lt (sem_step_lt hS (hR _ _ hbc)))

theorem sem_exists_minBranch (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) :
    ∃ b : Fin n → ℕ, sem_MinBranch n D b := by
  classical
  have h : ∀ v : Fin n, ∃ b, v ∈ eligSet n D →
      2 ≤ fanout D b ∧ supp n D b = {v} ∧ sem_Chain n D v.val b ∧
        ∀ w, 2 ≤ fanout D w → v ∈ supp n D w → b ≤ w := by
    intro v
    by_cases hv : v ∈ eligSet n D
    · have hex : ∃ w, 2 ≤ fanout D w ∧ v ∈ supp n D w := mem_eligSet.mp hv
      obtain ⟨h1, h2⟩ := Nat.find_spec hex
      have hch : sem_Chain n D v.val (Nat.find hex) :=
        sem_carrier_chain hS v _ h2 (fun u hu huv => by
          have := Nat.find_min hex hu
          by_contra hc
          exact this ⟨by omega, huv⟩)
      exact ⟨Nat.find hex, fun _ => ⟨h1, Finset.Subset.antisymm
        (sem_dom_pure hG hS hC v _ (sem_chain_dom hS hch)) (Finset.singleton_subset_iff.mpr h2),
        hch, fun w hw1 hw2 => Nat.find_min' hex ⟨hw1, hw2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose b hb using h
  exact ⟨b, fun v hv => hb v hv⟩

theorem sem_minBranch_first {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : sem_FirstBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1, (hb v hv).2.2.1⟩

theorem sem_minBranch_pure {b : Fin n → ℕ} (hb : sem_MinBranch n D b) : PureBranch n D b :=
  fun v hv => ⟨(hb v hv).1, (hb v hv).2.1⟩

/-- With no internal merge in the carrier of `x`, a gate carrying `x` is an OR with exactly
one carrying operand. -/
theorem sem_zm_gate (hS : Strict n D) {x : Fin n} (hM : merges n D (carrierT n D {x}) = ∅)
    {j : ℕ} (hj : j < D.length) (hx : x ∈ supp n D (n + j)) :
    tag D j = false ∧ ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
  have hnot : ¬ (x ∈ supp n D (opA D j) ∧ x ∈ supp n D (opB D j)) := by
    intro hc
    have hm : j ∈ merges n D (carrierT n D {x}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hc.1, sem_mem_carrier1.mpr hc.2⟩
    rw [hM] at hm
    exact Finset.notMem_empty _ hm
  refine ⟨?_, hnot⟩
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx
  exact hnot hx

/-- The code count of one label: `|W_x| + M_x = 1 + [x eligible] +` residual units on `x`. -/
theorem sem_code_count (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) (x : Fin n) :
    (sem_W n D x).card + (merges n D (carrierT n D {x})).card =
      1 + (({x} : Finset (Fin n)) ∩ eligSet n D).card +
        ((residualUnits n D b).filter (fun u => x ∈ supp n D u.1)).card := by
  have h1 := sem_flow1 hG h hC x
  have h2 := surplus_carrierT_eq h.1 b hb {x}
  have h3 : (residualUnits n D b).filter (fun u => (supp n D u.1 ∩ {x}).Nonempty) =
      (residualUnits n D b).filter (fun u => x ∈ supp n D u.1) := by
    refine Finset.filter_congr (fun u _ => ?_)
    constructor
    · rintro ⟨y, hy⟩
      rw [Finset.mem_inter, Finset.mem_singleton] at hy
      exact hy.2 ▸ hy.1
    · intro hx
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_singleton_self x⟩⟩
  rw [h3] at h2
  omega

/-- Descent along single-reader carriers: from a wire `c` carrying all of `X`, when the
carriers of the labels of `X` have no merge and no branching from `c` on, an arm leads to
the source of a position consuming every label of `X`. -/
theorem sem_descent (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) :
    ∀ c, (∀ x ∈ X, x ∈ supp n D c) →
      (∀ x ∈ X, ∀ w, c ≤ w → x ∈ supp n D w → fanout D w ≤ 1) →
      ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
        Relation.ReflTransGen (sem_Arm n D X) c (src D e) := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  intro c
  generalize hk : n + D.length - c = k
  induction k using Nat.strong_induction_on generalizing c with
  | _ k ih =>
    intro hc hlow
    have hclt := sem_supp_lt (hc x0 hx0)
    have hcne : c ≠ outW n D := by
      intro he
      have := hc x0 hx0
      rw [he, sem_supp_out hG hC] at this
      exact Finset.notMem_empty _ this
    have hf1 : 1 ≤ fanout D c := h.2.1 c (by unfold outW at hcne; omega)
    have hf : fanout D c = 1 := le_antisymm (hlow x0 hx0 c (le_refl c) (hc x0 hx0)) hf1
    obtain ⟨j, hjr⟩ := Finset.card_pos.mp hf1
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hjr
    obtain ⟨hj, hop⟩ := hjr
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = c := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    have hcj : c < n + j := hs ▸ sem_src_lt hS hj s
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hj hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hj ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hc x hx
        · right; rw [h1]; exact hc x hx
      obtain ⟨e, he1, he2⟩ := ih (n + D.length - (n + j)) (by omega) (n + j) rfl hall
        (fun x hx w hw => hlow x hx w (by omega))
      refine ⟨e, he1, Relation.ReflTransGen.head ⟨?_, hf, fun x hx => ⟨hc x hx, hall x hx⟩⟩ he2⟩
      rw [← hs]
      exact sem_step_src hj s
    · refine ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hj, ?_, fun hc2 => hcar ⟨x, hx, hc2⟩⟩, ?_⟩
      · rw [hs]; exact hc x hx
      · rw [hs]

/-- Two arms: a wire with two readers carrying all of `X`, after which no carrier of a label
of `X` branches or merges, leads to two positions at different gates consuming all of `X`. -/
theorem sem_two_arms (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (X : Finset (Fin n)) (hX : X.Nonempty)
    (hM : ∀ x ∈ X, merges n D (carrierT n D {x}) = ∅) (r : ℕ)
    (hr : ∀ x ∈ X, x ∈ supp n D r) (hf : 2 ≤ fanout D r)
    (hlow : ∀ x ∈ X, ∀ w, r < w → x ∈ supp n D w → fanout D w ≤ 1) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  classical
  have hS := h.1
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨j1, hj1, j2, hj2, hne⟩ := Finset.one_lt_card.mp (show 1 < (readers D r).card from hf)
  have hread : ∀ j ∈ readers D r, j < D.length ∧ r < n + j ∧ (opA D j = r ∨ opB D j = r) := by
    intro j hj
    simp only [readers, Finset.mem_filter, Finset.mem_range] at hj
    have := hS j hj.1
    exact ⟨hj.1, by omega, hj.2⟩
  have hterm : ∀ j ∈ readers D r, ∃ e : ℕ × Bool, (∀ x ∈ X, e ∈ sem_W n D x) ∧
      ((e.1 = j ∧ src D e = r) ∨ Relation.ReflTransGen (sem_Arm n D X) (n + j) (src D e)) := by
    intro j hj
    obtain ⟨hjl, hrj, hop⟩ := hread j hj
    obtain ⟨s, hs⟩ : ∃ s : Bool, src D (j, s) = r := by
      rcases hop with h1 | h1
      · exact ⟨false, by rw [sb_src_false]; exact h1⟩
      · exact ⟨true, by rw [sb_src_true]; exact h1⟩
    by_cases hcar : ∃ x1 ∈ X, x1 ∈ supp n D (n + j)
    · obtain ⟨x1, hx1, hx1c⟩ := hcar
      have ht := (sem_zm_gate hS (hM x1 hx1) hjl hx1c).1
      have hall : ∀ x ∈ X, x ∈ supp n D (n + j) := by
        intro x hx
        rw [sem_supp_or hS hjl ht, Finset.mem_union]
        rcases hop with h1 | h1
        · left; rw [h1]; exact hr x hx
        · right; rw [h1]; exact hr x hx
      obtain ⟨e, he1, he2⟩ := sem_descent hG h hC X ⟨x0, hx0⟩ hM (n + j) hall
        (fun x hx w hw => hlow x hx w (by omega))
      exact ⟨e, he1, Or.inr he2⟩
    · exact ⟨(j, s), fun x hx => sem_mem_W.mpr ⟨hjl, by rw [hs]; exact hr x hx,
        fun hc2 => hcar ⟨x, hx, hc2⟩⟩, Or.inl ⟨rfl, hs⟩⟩
  have hRstep : ∀ a b, sem_Arm n D X a b → sem_step n D a b := fun _ _ hab => hab.1
  have hfun : ∀ a a' b, sem_Arm n D X a b → sem_Arm n D X a' b → a = a' := by
    intro a a' b h1 h2
    by_contra hne2
    obtain ⟨hb1, hb2, hba⟩ := h1.1
    obtain ⟨-, -, hba'⟩ := h2.1
    have hjb : b - n < D.length := by omega
    have hcarb : x0 ∈ supp n D (n + (b - n)) := by
      rw [Nat.add_sub_cancel' hb2]; exact (h1.2.2 x0 hx0).2
    apply (sem_zm_gate hS (hM x0 hx0) hjb hcarb).2
    have ha := (h1.2.2 x0 hx0).1
    have ha' := (h2.2.2 x0 hx0).1
    rcases hba with e1 | e1 <;> rcases hba' with e2 | e2
    · exact absurd (e1.symm.trans e2) hne2
    · rw [e1, e2]; exact ⟨ha, ha'⟩
    · rw [e1, e2]; exact ⟨ha', ha⟩
    · exact absurd (e1.symm.trans e2) hne2
  have hcross : ∀ ja ∈ readers D r, ∀ jb ∈ readers D r, ja ≠ jb →
      ¬ Relation.ReflTransGen (sem_Arm n D X) (n + ja) (n + jb) := by
    intro ja hja jb hjb hab hp
    obtain ⟨hjla, hrja, -⟩ := hread ja hja
    obtain ⟨hjlb, hrjb, hopb⟩ := hread jb hjb
    rcases Relation.ReflTransGen.cases_tail hp with heq | ⟨u, hu1, hu2⟩
    · exact hab (by omega)
    · have hle := sem_rtg_le hS hRstep hu1
      have hur : u = r := by
        by_contra hur
        obtain ⟨-, -, hbu⟩ := hu2.1
        rw [Nat.add_sub_cancel_left] at hbu
        apply (sem_zm_gate hS (hM x0 hx0) hjlb (hu2.2.2 x0 hx0).2).2
        have hu := (hu2.2.2 x0 hx0).1
        have hrr := hr x0 hx0
        rcases hbu with e1 | e1 <;> rcases hopb with e2 | e2
        · exact absurd (e1.symm.trans e2) hur
        · rw [e1, e2]; exact ⟨hu, hrr⟩
        · rw [e1, e2]; exact ⟨hrr, hu⟩
        · exact absurd (e1.symm.trans e2) hur
      omega
  obtain ⟨P, hP1, hP2⟩ := hterm j1 hj1
  obtain ⟨Q, hQ1, hQ2⟩ := hterm j2 hj2
  refine ⟨P, Q, fun hPQ => ?_, fun x hx => ⟨hP1 x hx, hQ1 x hx⟩⟩
  have hsame : Q = P := by
    rcases sem_same_gate hPQ with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨hjP, hxP, hnP⟩ := sem_mem_W.mp (hP1 x0 hx0)
      have hxQ := (sem_mem_W.mp (hQ1 x0 hx0)).2.1
      rw [h1] at hxQ
      apply hnP
      rw [sem_supp_and hS hjP (sem_W_and hS (hP1 x0 hx0)), Finset.mem_inter]
      obtain ⟨j, s⟩ := P
      cases s
      · exact ⟨by simpa [src] using hxP, by simpa [src, sem_bar] using hxQ⟩
      · exact ⟨by simpa [src, sem_bar] using hxQ, by simpa [src] using hxP⟩
  rw [hsame] at hQ2
  obtain ⟨-, hrj1, -⟩ := hread j1 hj1
  obtain ⟨-, hrj2, -⟩ := hread j2 hj2
  rcases hP2 with ⟨hPa, hPb⟩ | hPp <;> rcases hQ2 with ⟨hQa, hQb⟩ | hQp
  · exact hne (hPa.symm.trans hQa)
  · have := sem_rtg_le hS hRstep hQp
    omega
  · have := sem_rtg_le hS hRstep hPp
    omega
  · rcases sem_rtg_comparable hfun hPp hQp with h1 | h1
    · exact hcross j1 hj1 j2 hj2 hne h1
    · exact hcross j2 hj2 j1 hj1 (Ne.symm hne) h1

/-- With exactly one residual unit, a label with three consumption positions is eligible,
has no carrier merge and no further consumption, and is carried by the residual wire. -/
theorem sem_saturated (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {u0 : Σ _ : ℕ, ℕ}
    (hres : residualUnits n D b = {u0}) {x : Fin n} (hsat : 3 ≤ (sem_W n D x).card) :
    (sem_W n D x).card = 3 ∧ merges n D (carrierT n D {x}) = ∅ ∧ x ∈ eligSet n D ∧
      x ∈ supp n D u0.1 := by
  have h1 := sem_code_count hG h hC b hb x
  have h2 : (({x} : Finset (Fin n)) ∩ eligSet n D).card ≤ 1 :=
    (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  have h3 := Finset.card_filter_le (residualUnits n D b) (fun u => x ∈ supp n D u.1)
  rw [hres, Finset.card_singleton] at h3
  rw [hres] at h1
  refine ⟨by omega, Finset.card_eq_zero.mp (by omega), ?_, ?_⟩
  · by_contra hx
    have h4 : ({x} : Finset (Fin n)) ∩ eligSet n D = ∅ := by
      rw [Finset.singleton_inter_of_notMem hx]
    rw [h4, Finset.card_empty] at h1
    omega
  · have h4 : 0 < (({u0} : Finset (Σ _ : ℕ, ℕ)).filter (fun u => x ∈ supp n D u.1)).card := by
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h4
    rw [Finset.mem_filter, Finset.mem_singleton] at hu
    exact hu.1 ▸ hu.2

/-- Common terminals: with exactly one residual unit, the labels having three consumption
positions share two positions at different gates. -/
theorem sem_common_terminals (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : sem_MinBranch n D b) (hone : Bplus n D = (eligSet n D).card + 1)
    (X : Finset (Fin n)) (hX : X.Nonempty) (hsat : ∀ x ∈ X, 3 ≤ (sem_W n D x).card) :
    ∃ P Q : ℕ × Bool, P.1 ≠ Q.1 ∧ ∀ x ∈ X, P ∈ sem_W n D x ∧ Q ∈ sem_W n D x := by
  have hS := h.1
  have hbp := sem_minBranch_pure hb
  have hcard : (residualUnits n D b).card = 1 := by
    have := card_residual hS b hbp
    omega
  obtain ⟨u0, hres⟩ := Finset.card_eq_one.mp hcard
  have hu0 : u0 ∈ residualUnits n D b := by rw [hres]; exact Finset.mem_singleton_self _
  have hu0u : u0 ∈ units n D :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hu0).1).1
  have hfr : 2 ≤ fanout D u0.1 := by
    have := (mem_units.mp hu0u).2
    omega
  refine sem_two_arms hG h hC X hX (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.1)
    u0.1 (fun x hx => (sem_saturated hG h hC b hbp hres (hsat x hx)).2.2.2) hfr ?_
  intro x hx w hrw hxw
  obtain ⟨-, -, hxe, hxr⟩ := sem_saturated hG h hC b hbp hres (hsat x hx)
  by_contra hc
  have hw2 : 2 ≤ fanout D w := by omega
  have hwu : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ unitsPlus n D := by
    rw [unitsPlus, Finset.mem_filter, mem_units]
    exact ⟨⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := w) (by omega)), by show 0 + 1 < fanout D w; omega⟩,
      ⟨x, hxw⟩⟩
  by_cases hwr : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ reservedUnits n D b
  · obtain ⟨v, hv, hveq⟩ := Finset.mem_image.mp hwr
    have hbv : b v = w := congrArg Sigma.fst hveq
    have hsv := (hb v hv).2.1
    rw [hbv] at hsv
    rw [hsv, Finset.mem_singleton] at hxw
    have hmin := (hb x hxe).2.2.2 u0.1 hfr hxr
    rw [hxw, hbv] at hmin
    omega
  · have hwres : (⟨w, 0⟩ : Σ _ : ℕ, ℕ) ∈ residualUnits n D b :=
      Finset.mem_sdiff.mpr ⟨hwu, hwr⟩
    rw [hres, Finset.mem_singleton] at hwres
    have : w = u0.1 := congrArg Sigma.fst hwres
    omega

end SemArms

/-! ### Unique paths, the factor lemma, exact neighbourhoods -/

theorem sem_all_but_one {α : Type} (J : Finset α) (P : α → Prop)
    (h : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → P i ∨ P j) :
    ∃ J' ⊆ J, J.card ≤ J'.card + 1 ∧ ∀ i ∈ J', P i := by
  classical
  refine ⟨J.filter P, Finset.filter_subset _ _, ?_, fun i hi => (Finset.mem_filter.mp hi).2⟩
  have h1 : (J.filter (fun i => ¬ P i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    rcases h a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab with h1 | h1
    · exact (Finset.mem_filter.mp ha).2 h1
    · exact (Finset.mem_filter.mp hb).2 h1
  have h2 := Finset.card_filter_add_card_filter_not (s := J) P
  omega

section SemPaths

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_ind_single (a : Fin n) : sem_ind ({a} : Finset (Fin n)) = single a := by
  funext k; simp [sem_ind, single]

theorem sem_val_gate_src (hS : Strict n D) (x : Fin n → Bool) {j : ℕ} (hj : j < D.length)
    (s : Bool) : val D x (n + j) =
      gop (tag D j) (val D x (src D (j, s))) (val D x (src D (j, !s))) := by
  rw [val_gate hS x j hj]
  cases s
  · simp [src]
  · cases tag D j <;> simp [src, Bool.and_comm, Bool.or_comm]

/-- An edge of `{i} ∪ S` uses `i` or lies inside `S`. -/
theorem sem_ins_ind_edge (hG : sem_Gr G) {i : Fin n} {S : Finset (Fin n)}
    (h : sem_Edge G (sem_ins i (sem_ind S))) :
    (∃ a ∈ S, G i a) ∨ ∃ a ∈ S, ∃ b ∈ S, G a b := by
  obtain ⟨u, v, huv, hu, hv⟩ := h
  simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · rw [hu, hv] at huv; exact absurd huv (hG.2.1 i)
  · rw [hu] at huv; exact Or.inl ⟨v, hv, huv⟩
  · rw [hv] at huv; exact Or.inl ⟨u, hu, hG.1 _ _ huv⟩
  · exact Or.inr ⟨u, hu, v, hv, huv⟩

/-- Dominance relative to a target wire `t` at or after the chain end. -/
theorem sem_chain_dom_at (hS : Strict n D) {v b t : ℕ} (h : sem_Chain n D v b) (hbt : b ≤ t) :
    b = v ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl rfl
  | @head a c hstep hrest ih =>
    by_cases hba : b = a
    · exact Or.inl hba
    · right
      intro hp
      rcases Relation.ReflTransGen.cases_head hp with heq | ⟨c', hs, hrest'⟩
      · have h1 := sem_step_lt hS hstep.1
        have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
        omega
      · have hcc : c = c' := sem_step_unique hstep.1 hs.1 hstep.2
        subst hcc
        rcases ih with rfl | ih
        · exact hs.2 rfl
        · exact ih hrest'

theorem sem_dom_eq_at (hS : Strict n D) (x y : Fin n → Bool) (v : Fin n)
    (hxy : ∀ k, k ≠ v → x k = y k) (b t : ℕ)
    (hdom : b = v.val ∨ ¬ Relation.ReflTransGen (fun a c => sem_step n D a c ∧ c ≠ b) v.val t)
    (hb : val D x b = val D y b) : val D x t = val D y t := by
  by_contra hne
  rcases hdom with rfl | hdom
  · rw [val_input D x _ v.isLt, val_input D y _ v.isLt] at hb
    have hxy2 : x = y := by
      funext k
      by_cases hk : k = v
      · rw [hk]; exact hb
      · exact hxy k hk
    exact hne (by rw [hxy2])
  · exact hdom (sem_rtg_mono
      (fun a c h => ⟨h.1, fun hc => h.2 (by rw [hc]; exact hb)⟩)
      (sem_changed_path hS x y v hxy _ hne))

/-- A reader path out of the start of a single-reader chain passes through its end, or ends
strictly inside the chain. -/
theorem sem_chain_fork (hS : Strict n D) {a c q : ℕ} (hc : sem_Chain n D a c)
    (hq : Relation.ReflTransGen (sem_step n D) a q) :
    Relation.ReflTransGen (sem_step n D) c q ∨ (sem_Chain n D q c ∧ q ≠ c) := by
  revert hq
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun hq => Or.inl hq
  | @head a a' hstep hrest ih =>
    intro hq
    rcases Relation.ReflTransGen.cases_head hq with heq | ⟨a'', hs, hrest'⟩
    · right
      have h1 := sem_step_lt hS hstep.1
      have h2 := sem_rtg_le hS (fun _ _ hab => hab.1) hrest
      refine ⟨?_, by omega⟩
      rw [← heq]
      exact Relation.ReflTransGen.head hstep hrest
    · have hcc : a' = a'' := sem_step_unique hstep.1 hs hstep.2
      subst hcc
      exact ih hrest'

/-- The other operand of the reader of a single-reader chain wire does not depend on the
input at the start of the chain. -/
theorem sem_sibling_indep (hS : Strict n D) (v : Fin n) {j : ℕ} (hj : j < D.length) (s : Bool)
    (hch : sem_Chain n D v.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
    val D x (src D (j, s)) = val D y (src D (j, s)) := by
  by_contra hne
  have hp : Relation.ReflTransGen (sem_step n D) v.val (src D (j, s)) :=
    sem_rtg_mono (fun _ _ h => h.1) (sem_changed_path hS x y v hxy _ hne)
  have hstepc : sem_step n D (src D (j, !s)) (n + j) := sem_step_src hj (!s)
  have hstepq : sem_step n D (src D (j, s)) (n + j) := sem_step_src hj s
  have hlt1 := sem_src_lt hS hj s
  have hlt2 := sem_src_lt hS hj (!s)
  rcases sem_chain_fork hS hch hp with h1 | ⟨h1, h2⟩
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨c', hs, hrest⟩
    · exact sem_src_ne hS hj s heq.symm
    · have hcc : n + j = c' := sem_step_unique hstepc hs hf
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h) hrest
      omega
  · rcases Relation.ReflTransGen.cases_head h1 with heq | ⟨q', hs, hrest⟩
    · exact h2 heq
    · have hcc : n + j = q' := sem_step_unique hstepq hs.1 hs.2
      subst hcc
      have := sem_rtg_le hS (fun _ _ h => h.1) hrest
      omega

/-- A dominating wire separates a non-edge assignment from its edge extension by `v`. -/
theorem sem_dom_split (hS : Strict n D) (hC : sem_Comp n G D) (x : Fin n → Bool) (v : Fin n)
    (b : ℕ) (hdom : sem_Dom n D b v.val) (h0 : ¬ sem_Edge G x) (h1 : sem_Edge G (sem_ins v x)) :
    val D x b = false ∧ val D (sem_ins v x) b = true := by
  have hne : val D x b ≠ val D (sem_ins v x) b := by
    intro heq
    have h2 := sem_dom_eq hS x _ v (sem_ins_agree v x) b hdom heq
    exact h0 ((hC x).mp (by rw [h2]; exact (hC _).mpr h1))
  have hmono := val_mono hS x (sem_ins v x) (sem_ins_ge v x) b
  cases hx : val D x b
  · refine ⟨rfl, ?_⟩
    cases hy : val D (sem_ins v x) b
    · exact absurd (hx.trans hy.symm) hne
    · rfl
  · exact absurd (hx.trans (hmono hx).symm) hne

/-- The unique-path factor lemma: if a single-reader chain leads from the input `i` to `w`,
and on the labels of `Bs` the wire `w` behaves like `i AND (OR N)`, then some AND gate on
the chain has an operand whose support projected to `Bs` is exactly `N`. -/
theorem sem_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind

/-- Exact neighbourhood at a wire `w`: the conditions of the factor lemma in graph form. -/
theorem sem_exact_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hsupp⟩ := sem_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

/-- The first branching wire reached from an ineligible input has empty support. -/
theorem sem_branch_empty (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D) {i : Fin n}
    (hi : i ∈ ineligSet n D) {b : ℕ} (hch : sem_Chain n D i.val b) (hf : 2 ≤ fanout D b) :
    supp n D b = ∅ := by
  have hsub := sem_dom_pure hG hS hC i b (sem_chain_dom hS hch)
  refine Finset.eq_empty_of_forall_notMem (fun x hx => ?_)
  have h1 := hsub hx
  rw [Finset.mem_singleton] at h1
  have h2 := mem_ineligSet.mp hi b (h1 ▸ hx)
  omega

/-- A reader path is a single-reader chain or meets a branching wire reached by one. -/
theorem sem_path_chain {a t : ℕ} (hp : Relation.ReflTransGen (sem_step n D) a t) :
    sem_Chain n D a t ∨ ∃ b, sem_Chain n D a b ∧ 2 ≤ fanout D b := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @head a a' hstep _ ih =>
    by_cases hf : fanout D a = 1
    · rcases ih with h1 | ⟨b, h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.head ⟨hstep, hf⟩ h1)
      · exact Or.inr ⟨b, Relation.ReflTransGen.head ⟨hstep, hf⟩ h1, h2⟩
    · have := sem_step_fanout hstep
      exact Or.inr ⟨a, Relation.ReflTransGen.refl, by omega⟩

/-- An ineligible input has a unique path to the output, or reaches an empty branch. -/
theorem sem_inelig_reach (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) ∨
      ∃ b, sem_Chain n D i.val b ∧ 2 ≤ fanout D b ∧ supp n D b = ∅ := by
  have hlt : i.val < n + D.length := by have := i.isLt; omega
  have hp : Relation.ReflTransGen (sem_step n D) i.val (outW n D) := live_reaches_out h i.val hlt
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨b, h1, h2, sem_branch_empty hG h.1 hC hi h1 h2⟩

theorem sem_bzero_mem (hS : Strict n D) {b : ℕ} (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) :
    b ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) :=
  Finset.mem_filter.mpr ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (w := b) (by omega)),
    by rw [he]; exact Finset.not_nonempty_empty⟩

/-- Without empty-support surplus, every branching wire has nonempty support. -/
theorem sem_bzero_branch (hS : Strict n D) (hB0 : Bzero n D = 0) {b : ℕ} (hf : 2 ≤ fanout D b) :
    (supp n D b).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have h1 : fanout D b - 1 ≤ ∑ w ∈ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty),
      (fanout D w - 1) :=
    Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _)
      (sem_bzero_mem hS hf hne)
  unfold Bzero surplusOn at hB0
  omega

/-- With at most one empty-support surplus unit there is at most one empty branch. -/
theorem sem_bzero_unique (hS : Strict n D) (hB0 : Bzero n D ≤ 1) {b b' : ℕ}
    (hf : 2 ≤ fanout D b) (he : supp n D b = ∅) (hf' : 2 ≤ fanout D b')
    (he' : supp n D b' = ∅) : b = b' := by
  by_contra hne
  have hsub : ({b, b'} : Finset ℕ) ⊆ (inner n D).filter (fun w => ¬ (supp n D w).Nonempty) := by
    intro c hc
    rw [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact sem_bzero_mem hS hf he
    · exact sem_bzero_mem hS hf' he'
  have h1 := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at h1
  unfold Bzero surplusOn at hB0
  omega

/-- No empty branch: every wire reached from an ineligible input lies on its single-reader
chain; in particular the path to the output is unique. -/
theorem sem_noempty_unique (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) {w : ℕ}
    (hp : Relation.ReflTransGen (sem_step n D) i.val w) : sem_Chain n D i.val w := by
  rcases sem_path_chain hp with h1 | ⟨b, h1, h2⟩
  · exact h1
  · have h3 := sem_bzero_branch h.1 hB0 h2
    rw [sem_branch_empty hG h.1 hC hi h1 h2] at h3
    exact absurd h3 Finset.not_nonempty_empty

theorem sem_noempty_chain_out (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D = 0) {i : Fin n} (hi : i ∈ ineligSet n D) :
    sem_Chain n D i.val (outW n D) :=
  sem_noempty_unique hG h hC hB0 hi
    (live_reaches_out h i.val (by have := i.isLt; omega))

/-- Exact neighbourhood from a unique path to the output: for an independent label set
`Bs`, some AND gate on the path of `i` has an operand whose support meets `Bs` exactly in
the neighbours of `i`. -/
theorem sem_exact_nbhd (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i : Fin n}
    (hch : sem_Chain n D i.val (outW n D)) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain n D i.val (src D (j, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  obtain ⟨j, s, hj, ht, -, hc, hsupp⟩ := sem_exact_at (G := G) hS i (outW n D) hch Bs
    (fun S hS1 hS2 => by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rcases sem_ins_ind_edge hG ((hC _).mp hc) with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
      · exact hS2 a ha hia
      · exact hBs a (hS1 ha) b (hS1 hb) hab)
    (fun a _ hia => by
      constructor
      · exact (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
      · by_contra hc
        rw [Bool.not_eq_false, sem_ind_single] at hc
        exact sem_single_no_edge hG a ((hC _).mp hc))
  exact ⟨j, s, hj, ht, hc, hsupp⟩

/-- Exact neighbourhood before a wire dominating two inputs: if the path from `i` to `w` is
unique, `w` also dominates `j`, and `j` has a neighbour in `Bs` that `i` lacks, then some
AND gate on the path of `i` has an operand meeting `Bs` exactly in the neighbours of `i`. -/
theorem sem_shared_exact (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine sem_exact_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩

/-- One empty branch loses at most one exact neighbourhood: of two ineligible inputs with
incomparable neighbourhoods inside an independent set `Bs`, at least one has an AND gate on
its path with an operand meeting `Bs` exactly in its neighbours. -/
theorem sem_shared_empty (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (hB0 : Bzero n D ≤ 1) (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b)
    {i j : Fin n} (hi : i ∈ ineligSet n D) (hj : j ∈ ineligSet n D)
    (hji : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D i.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a)) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain n D j.val (src D (k, !s)) ∧
        ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G j a)) := by
  have hS := h.1
  rcases sem_inelig_reach hG h hC hi with h1 | ⟨b, hb1, hb2, hb3⟩
  · exact Or.inl (sem_exact_nbhd hG hS hC Bs hBs h1)
  · rcases sem_inelig_reach hG h hC hj with h1 | ⟨b', hb1', hb2', hb3'⟩
    · exact Or.inr (sem_exact_nbhd hG hS hC Bs hBs h1)
    · have hbb : b' = b := sem_bzero_unique hS hB0 hb2' hb3' hb2 hb3
      rw [hbb] at hb1'
      obtain ⟨k, s, hk, ht, -, hc, hsupp⟩ := sem_shared_exact hG hS hC Bs hBs hb1
        (sem_chain_dom hS hb1') hji
      exact Or.inl ⟨k, s, hk, ht, hc, hsupp⟩

/-- Full support of the assigned operand: if every gate reached from the consumer of an
ineligible `i` is an OR, the operand opposite the pure one carries exactly the neighbours. -/
theorem sem_full_support (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool} (he : sem_W n D i = {e})
    (hor : ∀ j, Relation.ReflTransGen (sem_step n D) (n + e.1) (n + j) → j ≠ e.1 →
      tag D j = false) :
    ∀ t, t ∈ supp n D (src D (sem_bar e)) ↔ G i t := by
  have hS := h.1
  obtain ⟨e0, hj0, ht0, hsrc0, hemp0, hnb0, hx0, -⟩ := sem_inelig_consumer hG h hC hi
  have hee : e = e0 := Finset.singleton_injective (he.symm.trans hx0)
  subst hee
  obtain ⟨g, s⟩ := e
  intro t
  refine ⟨fun ht => ?_, fun ht => hnb0 t ht⟩
  by_contra hnt
  have hgate : val D (sem_two i t) (n + g) = true := by
    rw [sem_val_gate_src hS _ hj0 s, ht0, gop_true, Bool.and_eq_true]
    exact ⟨sem_val_of_supp hS (by rw [hsrc0]; exact Finset.mem_singleton_self i)
      (by simp [sem_two]), sem_val_of_supp hS ht (by simp [sem_two])⟩
  have hall : ∀ c, Relation.ReflTransGen (sem_step n D) (n + g) c →
      val D (sem_two i t) c = true := by
    intro c hc
    induction hc with
    | refl => exact hgate
    | tail hab hbc ih =>
      obtain ⟨j, s', hj, rfl, rfl⟩ := sem_step_iff.mp hbc
      have hne : j ≠ g := by
        have := sem_rtg_le hS (fun _ _ h => h) hab
        have := sem_src_lt hS hj s'
        omega
      rw [sem_val_gate_src hS _ hj s', hor j (Relation.ReflTransGen.tail hab hbc) hne,
        gop_false, ih]
      rfl
  have hout := hall _ (live_reaches_out h (n + g) (by omega))
  obtain ⟨u, v, huv, hu, hv⟩ := (hC _).mp hout
  simp only [sem_two, Bool.or_eq_true, decide_eq_true_eq] at hu hv
  rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv] at huv
  · exact hG.2.1 _ huv
  · exact hnt huv
  · exact hnt (hG.1 _ _ huv)
  · exact hG.2.1 _ huv

end SemPaths

/-! ### Heawood forms of the exact-neighbourhood lemmas -/

/-- The side of the bipartition opposite to `i`. -/
def sem_hw_opp (i : Fin 14) : Finset (Fin 14) :=
  Finset.univ.filter (fun a => decide (a.val < 7) ≠ decide (i.val < 7))

/-- The neighbourhood of `i`. -/
def sem_hw_nb (i : Fin 14) : Finset (Fin 14) := Finset.univ.filter (fun a => Adj i a)

theorem sem_hw_sides : ∀ a b : Fin 14, hc_adjB a b = true →
    decide (a.val < 7) ≠ decide (b.val < 7) := by decide +kernel

theorem sem_hw_opp_indep (i : Fin 14) : ∀ a ∈ sem_hw_opp i, ∀ b ∈ sem_hw_opp i, ¬ Adj a b := by
  intro a ha b hb hab
  simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 := sem_hw_sides a b ((hc_adjB_iff a b).mpr hab)
  cases h2 : decide (a.val < 7) <;> cases h3 : decide (b.val < 7) <;>
    cases h4 : decide (i.val < 7) <;> simp_all

theorem sem_hw_nb_opp {i a : Fin 14} (h : Adj i a) : a ∈ sem_hw_opp i := by
  simp only [sem_hw_opp, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (sem_hw_sides i a ((hc_adjB_iff i a).mpr h)).symm

theorem sem_hw_mask {D : Dag} {i : Fin 14} {q : ℕ}
    (h : ∀ a ∈ sem_hw_opp i, (a ∈ supp 14 D q ↔ Adj i a)) :
    supp 14 D q ∩ sem_hw_opp i = sem_hw_nb i := by
  ext a
  simp only [Finset.mem_inter, sem_hw_nb, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact (h a h2).mp h1
  · intro h1; exact ⟨(h a (sem_hw_nb_opp h1)).mpr h1, sem_hw_nb_opp h1⟩

/-- No empty branch: every ineligible Heawood input has an AND gate on its unique path with
an operand whose support on the opposite side is exactly its neighbourhood. -/
theorem sem_hw_exact_nbhd {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D = 0) {i : Fin 14} (hi : i ∈ ineligSet 14 D) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ sem_Chain 14 D i.val (src D (j, !s)) ∧
      supp 14 D (src D (j, s)) ∩ sem_hw_opp i = sem_hw_nb i := by
  obtain ⟨j, s, hj, ht, hc, hsupp⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD)
    (sem_hw_opp i) (sem_hw_opp_indep i)
    (sem_noempty_chain_out sem_heawood_gr h (sem_heawood_comp hD) hB0 hi)
  exact ⟨j, s, hj, ht, hc, sem_hw_mask hsupp⟩

/-- At most one empty-support surplus unit: of two distinct ineligible Heawood inputs on
the same side, at least one has its exact neighbourhood on an operand of its path. -/
theorem sem_hw_shared_empty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hB0 : Bzero 14 D ≤ 1) {i j : Fin 14} (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hside : decide (i.val < 7) = decide (j.val < 7)) :
    (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain 14 D i.val (src D (k, !s)) ∧
        supp 14 D (src D (k, s)) ∩ sem_hw_opp i = sem_hw_nb i) ∨
      (∃ k s, k < D.length ∧ tag D k = true ∧ sem_Chain 14 D j.val (src D (k, !s)) ∧
        supp 14 D (src D (k, s)) ∩ sem_hw_opp j = sem_hw_nb j) := by
  have hopp : sem_hw_opp j = sem_hw_opp i := by unfold sem_hw_opp; rw [hside]
  obtain ⟨a, hja, hia⟩ := nbr_diff_exists j i (Ne.symm hij)
  rcases sem_shared_empty sem_heawood_gr h (sem_heawood_comp hD) hB0 (sem_hw_opp i)
    (sem_hw_opp_indep i) hi hj ⟨a, hopp ▸ sem_hw_nb_opp hja, hja, hia⟩ with
    ⟨k, s, hk, ht, hc, hsupp⟩ | ⟨k, s, hk, ht, hc, hsupp⟩
  · exact Or.inl ⟨k, s, hk, ht, hc, sem_hw_mask hsupp⟩
  · exact Or.inr ⟨k, s, hk, ht, hc,
      sem_hw_mask (fun a ha => hsupp a (by rw [← hopp]; exact ha))⟩

/-! ### Difference carriers: surplus, the first joint carrier, two exits -/

section SemDiff

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem sem_mem_diff {x y : Fin n} {w : ℕ} :
    w ∈ carrierDiff n D x y ↔ x ∈ supp n D w ∧ y ∉ supp n D w := by
  simp only [carrierDiff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨sem_supp_lt h.1, h⟩⟩

theorem sem_mem_exit_diff {x y : Fin n} {e : ℕ × Bool} :
    e ∈ exitArcs n D (carrierDiff n D x y) ↔ e.1 < D.length ∧
      (x ∈ supp n D (src D e) ∧ y ∉ supp n D (src D e)) ∧
      ¬ (x ∈ supp n D (n + e.1) ∧ y ∉ supp n D (n + e.1)) := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, sem_mem_diff]

/-- `B_K = 1 +` the residual units carrying `x` without `y`, for the carrier of an eligible
`x` without `y`. -/
theorem sem_surplus_diff (hS : Strict n D) (b : Fin n → ℕ) (hb : PureBranch n D b)
    {x y : Fin n} (hxy : x ≠ y) (hx : x ∈ eligSet n D) :
    surplusOn D (carrierDiff n D x y) = 1 + ((residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
  have h1 : surplusOn D (carrierDiff n D x y) =
      ((units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1)).card := by
    rw [sb_card_units_filter n D (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)]
    symm
    refine Finset.sum_subset (fun w hw => ?_) (fun w hw hnot => ?_)
    · rw [Finset.mem_filter] at hw
      exact sem_mem_diff.mpr hw.2
    · have hni : w ∉ inner n D := fun hc => hnot (Finset.mem_filter.mpr ⟨hc, sem_mem_diff.mp hw⟩)
      rw [sb_mem_inner] at hni
      simp [fanout_eq_zero_of_ge hS w (by omega)]
  have h2 : (units n D).filter (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) =
      {(⟨b x, 0⟩ : Σ _ : ℕ, ℕ)} ∪ (residualUnits n D b).filter
        (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    ext u
    have hsub := reserved_subset hS b hb
    simp only [residualUnits, unitsPlus, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_singleton]
    constructor
    · intro hu
      by_cases hr : u ∈ reservedUnits n D b
      · left
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
        have hxv := hu.2.1
        rw [(hb v hv).2, Finset.mem_singleton] at hxv
        rw [hxv]
      · exact Or.inr ⟨⟨⟨hu.1, ⟨x, hu.2.1⟩⟩, hr⟩, hu.2⟩
    · rintro (rfl | hu)
      · have hbx := hb x hx
        refine ⟨(Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨x, hx, rfl⟩))).1, ?_, ?_⟩
        · rw [hbx.2]; exact Finset.mem_singleton_self x
        · rw [hbx.2, Finset.mem_singleton]; exact fun hc => hxy hc.symm
      · exact ⟨hu.1.1.1, hu.2⟩
  have h3 : (⟨b x, 0⟩ : Σ _ : ℕ, ℕ) ∉ (residualUnits n D b).filter
      (fun u => x ∈ supp n D u.1 ∧ y ∉ supp n D u.1) := by
    intro hc
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h1, h2, Finset.singleton_union, Finset.card_insert_of_notMem h3]
  omega

/-- The first joint carrier of two labels is an OR whose operands carry one label each. -/
theorem sem_first_joint (hS : Strict n D) {x y : Fin n} (hxy : x ≠ y) {w : ℕ}
    (hw : x ∈ supp n D w ∧ y ∈ supp n D w) :
    ∃ j s, j < D.length ∧ tag D j = false ∧ x ∈ supp n D (n + j) ∧ y ∈ supp n D (n + j) ∧
      x ∈ supp n D (src D (j, s)) ∧ y ∉ supp n D (src D (j, s)) ∧
      y ∈ supp n D (src D (j, !s)) ∧ x ∉ supp n D (src D (j, !s)) := by
  classical
  have hex : ∃ u, x ∈ supp n D u ∧ y ∈ supp n D u := ⟨w, hw⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have hmin : ∀ u, u < Nat.find hex → ¬ (x ∈ supp n D u ∧ y ∈ supp n D u) :=
    fun u hu => Nat.find_min hex hu
  generalize Nat.find hex = f at h1 h2 hmin
  have hlt := sem_supp_lt h1
  have hn : n ≤ f := by
    by_contra hc
    have hs : supp n D f = {⟨f, by omega⟩} := supp_input D ⟨f, by omega⟩
    rw [hs, Finset.mem_singleton] at h1 h2
    exact hxy (h1.trans h2.symm)
  obtain ⟨j, rfl⟩ : ∃ j, f = n + j := ⟨f - n, by omega⟩
  have hj : j < D.length := by omega
  obtain ⟨ha, hb, -⟩ := hS j hj
  have hna := hmin _ ha
  have hnb := hmin _ hb
  cases ht : tag D j
  · have h1' := h1
    have h2' := h2
    rw [sem_supp_or hS hj ht, Finset.mem_union] at h1' h2'
    refine ⟨j, ?_⟩
    rcases h1' with hxa | hxb
    · have hya : y ∉ supp n D (opA D j) := fun hc => hna ⟨hxa, hc⟩
      have hyb : y ∈ supp n D (opB D j) := h2'.resolve_left hya
      exact ⟨false, hj, ht, h1, h2, by simpa [src] using hxa, by simpa [src] using hya,
        by simpa [src] using hyb, by simpa [src] using fun hc => hnb ⟨hc, hyb⟩⟩
    · have hyb : y ∉ supp n D (opB D j) := fun hc => hnb ⟨hxb, hc⟩
      have hya : y ∈ supp n D (opA D j) := h2'.resolve_right hyb
      exact ⟨true, hj, ht, h1, h2, by simpa [src] using hxb, by simpa [src] using hyb,
        by simpa [src] using hya, by simpa [src] using fun hc => hna ⟨hc, hya⟩⟩
  · exfalso
    rw [sem_supp_and hS hj ht, Finset.mem_inter] at h1 h2
    exact hna ⟨h1.1, h2.1⟩

/-- Depletion set-up: if every residual unit carrying the eligible `x` also carries `c`, a
joint carrier of `x` and `c` exists, and `x` has a neighbour `z` not adjacent to `c`, then
the carrier of `x` without `c` has surplus one, no merge, exactly two exits, and one of the
exits enters an OR gate carrying `c`. -/
theorem sem_diff_two_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (b : Fin n → ℕ) (hb : PureBranch n D b) {x c z : Fin n} (hxc : x ≠ c)
    (hx : x ∈ eligSet n D)
    (hres : ∀ u ∈ residualUnits n D b, x ∈ supp n D u.1 → c ∈ supp n D u.1)
    {w : ℕ} (hw : x ∈ supp n D w ∧ c ∈ supp n D w) (hxz : G x z) (hcz : ¬ G c z) :
    surplusOn D (carrierDiff n D x c) = 1 ∧ merges n D (carrierDiff n D x c) = ∅ ∧
      (exitArcs n D (carrierDiff n D x c)).card = 2 ∧
      ∃ e ∈ exitArcs n D (carrierDiff n D x c), tag D e.1 = false ∧ c ∈ supp n D (n + e.1) := by
  have hS := h.1
  have hsur : surplusOn D (carrierDiff n D x c) = 1 := by
    rw [sem_surplus_diff hS b hb hxc hx, Finset.filter_eq_empty_iff.mpr
      (fun u hu hc => hc.2 (hres u hu hc.1)), Finset.card_empty]
  have hfl := carrier_flow_diff h x c hxc
    (by rw [sem_supp_out hG hC]; exact Finset.notMem_empty x)
  rw [hsur] at hfl
  obtain ⟨j1, s1, hj1, ht1, hx1, hc1, hxs1, hcs1, -, -⟩ := sem_first_joint hS hxc hw
  have he1 : (j1, s1) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj1, ⟨hxs1, hcs1⟩, fun hc => hc.2 hc1⟩
  have hA : ∀ u ∈ ({c, z} : Finset (Fin n)), ∀ v ∈ ({c, z} : Finset (Fin n)), ¬ G u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
    · exact hG.2.1 c
    · exact hcz
    · exact fun hc => hcz (hG.1 _ _ hc)
    · exact hG.2.1 z
  obtain ⟨j2, s2, hj2, -, hx2, hn2, hd2⟩ := sem_exposure hG hS hC {c, z} hA x ⟨z, by simp, hxz⟩
  have he2 : (j2, s2) ∈ exitArcs n D (carrierDiff n D x c) :=
    sem_mem_exit_diff.mpr ⟨hj2, ⟨hx2, fun hc => Finset.disjoint_left.mp hd2 hc (by simp)⟩,
      fun hc => hn2 hc.1⟩
  have hne : (j1, s1) ≠ (j2, s2) := by
    intro heq
    rw [Prod.mk.injEq] at heq
    exact hn2 (heq.1 ▸ hx1)
  have h2 : 2 ≤ (exitArcs n D (carrierDiff n D x c)).card :=
    Finset.one_lt_card.mpr ⟨_, he1, _, he2, hne⟩
  exact ⟨hsur, Finset.card_eq_zero.mp (by omega), by omega, (j1, s1), he1, ht1, hc1⟩

/-- On the unique path of an input, every AND sibling carries every neighbour. -/
theorem sem_and_sibling_nbrs (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {i : Fin n} {j : ℕ} (hj : j < D.length) (s : Bool) (ht : tag D j = true)
    (hch : sem_Chain n D i.val (src D (j, !s))) (hf : fanout D (src D (j, !s)) = 1)
    (hout : n + j ≤ outW n D) {a : Fin n} (hia : G i a) : a ∈ supp n D (src D (j, s)) := by
  have hchg : sem_Chain n D i.val (n + j) :=
    Relation.ReflTransGen.tail hch ⟨sem_step_src hj (!s), hf⟩
  have hx0 : val D (single a) (outW n D) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact sem_single_no_edge hG a ((hC _).mp hc)
  have hy1 : val D (sem_ins i (single a)) (outW n D) = true :=
    (hC _).mpr ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, single]⟩
  have hgy : val D (sem_ins i (single a)) (n + j) = true := by
    by_contra hc2
    rw [Bool.not_eq_true] at hc2
    have hgx : val D (single a) (n + j) = false := by
      by_contra hc3
      rw [Bool.not_eq_false] at hc3
      rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
      exact Bool.noConfusion hc2
    have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (single a)) (n + j) (outW n D)
      (sem_chain_dom_at hS hchg hout) (hgx.trans hc2.symm)
    rw [hx0, hy1] at h2
    exact Bool.false_ne_true h2
  rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
  have hind := sem_sibling_indep hS i hj s hch hf _ _ (sem_ins_agree i (single a))
  rw [hgy.1] at hind
  exact mem_supp.mpr hind

end SemDiff

/-! ## Block F: support-mask charging and witness costs -/

/-- `M` occurs as the exact mask, projected onto `P`, of some wire. -/
def sup_Occ (n : ℕ) (D : Dag) (P M : Finset (Fin n)) : Prop := ∃ w, supp n D w ∩ P = M

/-- Internal merges of the union carrier of `P` whose output mask has at least two labels. -/
def sup_big (n : ℕ) (D : Dag) (P : Finset (Fin n)) : Finset ℕ :=
  (merges n D (carrierT n D P)).filter (fun j => 2 ≤ (supp n D (n + j) ∩ P).card)

/-- Witness position for the loss of `f`: an AND position consuming `f` whose operand mask
lies inside `U` and has at most two labels. -/
def sup_Wit (n : ℕ) (D : Dag) (P U : Finset (Fin n)) (f : Fin n) (e : ℕ × Bool) : Prop :=
  e.1 < D.length ∧ tag D e.1 = true ∧ f ∈ P ∧ f ∈ supp n D (src D e) ∧
    f ∉ supp n D (n + e.1) ∧ supp n D (src D e) ∩ P ⊆ U ∧ (supp n D (src D e) ∩ P).card ≤ 2

/-- The cost unit of a witness position: its boundary arc when the output mask is empty,
its gate otherwise. -/
def sup_cost (n : ℕ) (D : Dag) (P : Finset (Fin n)) (e : ℕ × Bool) : (ℕ × Bool) ⊕ ℕ :=
  if supp n D (n + e.1) ∩ P = ∅ then Sum.inl e else Sum.inr e.1

/-- Admissible witness costs: exits whose operand mask has at most two labels, or merges
with a singleton output mask. -/
def sup_CostOK (n : ℕ) (D : Dag) (P : Finset (Fin n)) (c : (ℕ × Bool) ⊕ ℕ) : Prop :=
  Sum.elim (fun e => e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2)
    (fun j => j ∈ merges n D (carrierT n D P) ∧ (supp n D (n + j) ∩ P).card = 1) c

section SupMask

variable {n : ℕ} {D : Dag}

theorem sup_occ_wire (P : Finset (Fin n)) (w : ℕ) : sup_Occ n D P (supp n D w ∩ P) := ⟨w, rfl⟩

theorem sup_occ_sub {P M : Finset (Fin n)} (h : sup_Occ n D P M) : M ⊆ P := by
  obtain ⟨w, rfl⟩ := h
  exact Finset.inter_subset_right

theorem sup_mem_carrier {P : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D P ↔ (supp n D w ∩ P).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv⟩ := h
    exact ⟨sem_supp_lt (Finset.mem_inter.mp hv).1, v, hv⟩

/-! ### First productions are big merges -/

/-- Every occurring mask with at least two labels is the output mask of a big merge. -/
theorem sup_occ_big (hS : Strict n D) {P M : Finset (Fin n)} (hM : 2 ≤ M.card)
    (h : sup_Occ n D P M) : ∃ j ∈ sup_big n D P, supp n D (n + j) ∩ P = M := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, -, -, hj, hmer, -, -⟩ := sem_first_mask hS P M hM w hw
  exact ⟨j, Finset.mem_filter.mpr ⟨hmer, by rw [hj]; exact hM⟩, hj⟩

/-- A finite family of occurring masks with at least two labels needs as many big merges. -/
theorem sup_card_le_big (hS : Strict n D) (P : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ n D P M) : F.card ≤ (sup_big n D P).card := by
  have hsub : F ⊆ (sup_big n D P).image (fun j => supp n D (n + j) ∩ P) := by
    intro M hM
    obtain ⟨j, hj, hjM⟩ := sup_occ_big hS (hF M hM).1 (hF M hM).2
    exact Finset.mem_image.mpr ⟨j, hj, hjM⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-! ### The charging theorem for triples meeting in at most one label -/

/-- First production of an occurring triple: an occurring pair inside it, an occurring
four-set around it, or two different occurring five-sets around it. -/
theorem sup_triple_parent (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 7)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) ∨
      (∃ A B, A ≠ B ∧ sup_Occ n D P A ∧ sup_Occ n D P B ∧ A.card = 5 ∧ B.card = 5 ∧
        T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨j, hj, -, hjT, -, -, hpar⟩ := sem_first_mask hS P T (by omega) w hw
  have hoA : sup_Occ n D P (supp n D (opA D j) ∩ P) := sup_occ_wire P _
  have hoB : sup_Occ n D P (supp n D (opB D j) ∩ P) := sup_occ_wire P _
  rcases hpar with ⟨ht, hA, hB⟩ | ⟨-, hA, hB, hun, -, -⟩
  · have hAB : (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) = T := by
      rw [← hjT, sem_supp_and hS hj ht]
      ext v
      simp only [Finset.mem_inter]
      tauto
    generalize supp n D (opA D j) ∩ P = A at hoA hA hAB
    generalize supp n D (opB D j) ∩ P = B at hoB hB hAB
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hu : (A ∪ B).card ≤ 7 :=
      (Finset.card_le_card (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    by_cases h4 : A.card = 4
    · exact Or.inr (Or.inl ⟨A, hoA, h4, hA.subset⟩)
    by_cases h4' : B.card = 4
    · exact Or.inr (Or.inl ⟨B, hoB, h4', hB.subset⟩)
    refine Or.inr (Or.inr ⟨A, B, ?_, hoA, hoB, by omega, by omega, hA.subset, hB.subset, hAB⟩)
    intro hEq
    rw [hEq, Finset.inter_self] at hAB
    rw [hAB] at hcB
    omega
  · generalize supp n D (opA D j) ∩ P = A at hoA hA hun
    generalize supp n D (opB D j) ∩ P = B at hoB hB hun
    have hcA := Finset.card_lt_card hA
    have hcB := Finset.card_lt_card hB
    have hc := Finset.card_union_le A B
    rw [hun] at hc
    by_cases h2 : A.card = 2
    · exact Or.inl ⟨A, hoA, h2, hA.subset⟩
    · exact Or.inl ⟨B, hoB, by omega, hB.subset⟩

/-- Six-label form (stars of a K4 on six secant labels): the first production of an
occurring triple has an occurring pair inside it or an occurring four-set around it. -/
theorem sup_triple_parent_six (hS : Strict n D) {P T : Finset (Fin n)} (hP : P.card ≤ 6)
    (hT : T.card = 3) (h : sup_Occ n D P T) :
    (∃ A, sup_Occ n D P A ∧ A.card = 2 ∧ A ⊆ T) ∨
      (∃ A, sup_Occ n D P A ∧ A.card = 4 ∧ T ⊆ A) := by
  rcases sup_triple_parent hS (by omega) hT h with h2 | h4 |
    ⟨A, B, -, hoA, hoB, hcA, hcB, -, -, hAB⟩
  · exact Or.inl h2
  · exact Or.inr h4
  · exfalso
    have hu := (Finset.card_le_card
      (Finset.union_subset (sup_occ_sub hoA) (sup_occ_sub hoB))).trans hP
    have hie := Finset.card_union_add_card_inter A B
    rw [hAB] at hie
    omega

theorem sup_pair_unique {T T' A : Finset (Fin n)} (hA : A.card = 2) (h1 : A ⊆ T)
    (h2 : A ⊆ T') (hint : T ≠ T' → (T ∩ T').card ≤ 1) : T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.subset_inter h1 h2)
  have h4 := hint hne
  omega

theorem sup_four_unique {T T' A : Finset (Fin n)} (hT : T.card = 3) (hT' : T'.card = 3)
    (hA : A.card = 4) (h1 : T ⊆ A) (h2 : T' ⊆ A) (hint : T ≠ T' → (T ∩ T').card ≤ 1) :
    T = T' := by
  by_contra hne
  have h3 := Finset.card_le_card (Finset.union_subset h1 h2)
  have h4 := Finset.card_union_add_card_inter T T'
  have h5 := hint hne
  omega

theorem sup_five_cap {T1 T2 T3 A : Finset (Fin n)} (h1 : T1.card = 3) (h2 : T2.card = 3)
    (h3 : T3.card = 3) (hA : A.card ≤ 5) (s1 : T1 ⊆ A) (s2 : T2 ⊆ A) (s3 : T3 ⊆ A)
    (i12 : (T1 ∩ T2).card ≤ 1) (i13 : (T1 ∩ T3).card ≤ 1) (i23 : (T2 ∩ T3).card ≤ 1) :
    False := by
  have hu := Finset.card_le_card (Finset.union_subset (Finset.union_subset s1 s2) s3)
  have e1 := Finset.card_union_add_card_inter T1 T2
  have e2 := Finset.card_union_add_card_inter (T1 ∪ T2) T3
  have e3 : ((T1 ∪ T2) ∩ T3).card ≤ (T1 ∩ T3).card + (T2 ∩ T3).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

/-- Auxiliary masks: a family `L` of occurring triples pairwise meeting in at most one label,
on at most seven labels, has at least as many occurring auxiliary masks, each a pair inside
a target or a set of four or five labels. Doubled integer charges: two per pair or four-set,
one per five-set. -/
theorem sup_aux_exists (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1) :
    ∃ Aux : Finset (Finset (Fin n)), L.card ≤ Aux.card ∧ ∀ A ∈ Aux, sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) := by
  classical
  refine ⟨P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)), ?_,
    fun A hA => (Finset.mem_filter.mp hA).2⟩
  generalize hAux : P.powerset.filter (fun A => sup_Occ n D P A ∧
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5)) = Aux
  have hmem : ∀ A, sup_Occ n D P A →
      ((A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5) → A ∈ Aux := by
    intro A h1 h2
    rw [← hAux]
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (sup_occ_sub h1), h1, h2⟩
  have hprop : ∀ A ∈ Aux, (A.card = 2 ∧ ∃ T ∈ L, A ⊆ T) ∨ A.card = 4 ∨ A.card = 5 := by
    intro A hA
    rw [← hAux] at hA
    exact (Finset.mem_filter.mp hA).2.2
  have hrow : ∀ T ∈ L, 2 ≤ ∑ A ∈ Aux,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) := by
    intro T hT
    rcases sup_triple_parent hS hP (h3 T hT).1 (h3 T hT).2 with
      ⟨A, ho, hc, hs⟩ | ⟨A, ho, hc, hs⟩ | ⟨A, B, hne, hoA, hoB, hcA, hcB, hsA, hsB, -⟩
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inl ⟨hc, T, hT, hs⟩)))
      simp [hc, hs]
    · refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (hmem A ho (Or.inr (Or.inl hc))))
      simp [hc, hs]
    · have hsub : ({A, B} : Finset (Finset (Fin n))) ⊆ Aux := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hmem _ hoA (Or.inr (Or.inr hcA))
        · exact hmem _ hoB (Or.inr (Or.inr hcB))
      refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
      rw [Finset.sum_pair hne]
      simp [hcA, hcB, hsA, hsB]
  have hcol : ∀ A ∈ Aux, ∑ T ∈ L,
      (if A.card = 5 then (if T ⊆ A then 1 else 0) else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) ≤ 2 := by
    intro A hA
    by_cases h5 : A.card = 5
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) = (L.filter (fun T => T ⊆ A)).card := by
        rw [Finset.card_filter]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      by_contra hgt
      obtain ⟨T1, T2, T3, m1, m2, m3, n12, n13, n23⟩ :=
        Finset.two_lt_card_iff.mp (show 2 < (L.filter (fun T => T ⊆ A)).card by omega)
      rw [Finset.mem_filter] at m1 m2 m3
      exact sup_five_cap (h3 _ m1.1).1 (h3 _ m2.1).1 (h3 _ m3.1).1 h5.le m1.2 m2.2 m3.2
        (hint _ m1.1 _ m2.1 n12) (hint _ m1.1 _ m3.1 n13) (hint _ m2.1 _ m3.1 n23)
    · have hsum : ∑ T ∈ L, (if A.card = 5 then (if T ⊆ A then 1 else 0)
          else (if A ⊆ T ∨ T ⊆ A then 2 else 0)) =
          2 * (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card := by
        rw [Finset.card_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun T _ => by simp [h5])
      rw [hsum]
      have hle : (L.filter (fun T => A ⊆ T ∨ T ⊆ A)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro T hT T' hT'
        rw [Finset.mem_filter] at hT hT'
        have c3 := (h3 T hT.1).1
        have c3' := (h3 T' hT'.1).1
        rcases hprop A hA with ⟨h2, -⟩ | h4 | h5'
        · have e1 : A ⊆ T := hT.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : A ⊆ T' := hT'.2.resolve_right (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_pair_unique h2 e1 e2 (hint T hT.1 T' hT'.1)
        · have e1 : T ⊆ A := hT.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          have e2 : T' ⊆ A := hT'.2.resolve_left (fun h => by
            have := Finset.card_le_card h; omega)
          exact sup_four_unique c3 c3' h4 e1 e2 (hint T hT.1 T' hT'.1)
        · exact absurd h5' h5
      omega
  have h1 := Finset.card_nsmul_le_sum L _ 2 hrow
  have h2 := Finset.sum_le_card_nsmul Aux _ 2 hcol
  rw [Finset.sum_comm] at h1
  simp only [smul_eq_mul] at h1 h2
  omega

/-- The charging theorem: `m` occurring triples pairwise meeting in at most one label, on at
most seven labels, give `2 * m` big merges; further occurring masks outside the charged
classes (not a target, not of size four or five, and if a pair then inside no target) are
counted on top. -/
theorem sup_charge (hS : Strict n D) {P : Finset (Fin n)} (hP : P.card ≤ 7)
    (L : Finset (Finset (Fin n))) (h3 : ∀ T ∈ L, T.card = 3 ∧ sup_Occ n D P T)
    (hint : ∀ T ∈ L, ∀ T' ∈ L, T ≠ T' → (T ∩ T').card ≤ 1)
    (X : Finset (Finset (Fin n)))
    (hX : ∀ M ∈ X, sup_Occ n D P M ∧ 2 ≤ M.card ∧ M ∉ L ∧ M.card ≠ 4 ∧ M.card ≠ 5 ∧
      (M.card = 2 → ∀ T ∈ L, ¬ M ⊆ T)) :
    2 * L.card + X.card ≤ (sup_big n D P).card := by
  classical
  obtain ⟨Aux, hcard, hAux⟩ := sup_aux_exists hS hP L h3 hint
  have hd1 : Disjoint L Aux := by
    rw [Finset.disjoint_left]
    intro T hT hTA
    have := (h3 T hT).1
    rcases (hAux T hTA).2 with ⟨h, -⟩ | h | h <;> omega
  have hd2 : Disjoint (L ∪ Aux) X := by
    rw [Finset.disjoint_left]
    intro M hM hMX
    obtain ⟨-, -, hnL, hn4, hn5, hno⟩ := hX M hMX
    rcases Finset.mem_union.mp hM with h | h
    · exact hnL h
    · rcases (hAux M h).2 with ⟨h2, T, hT, hs⟩ | h4 | h5
      · exact hno h2 T hT hs
      · exact hn4 h4
      · exact hn5 h5
  have hle := sup_card_le_big hS P ((L ∪ Aux) ∪ X) (by
    intro M hM
    rcases Finset.mem_union.mp hM with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ⟨by have := (h3 M h).1; omega, (h3 M h).2⟩
      · refine ⟨?_, (hAux M h).1⟩
        rcases (hAux M h).2 with ⟨h, -⟩ | h | h <;> omega
    · exact ⟨(hX M h).2.1, (hX M h).1⟩)
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hle
  omega

/-! ### Witness positions for missing masks -/

/-- A witness for the loss of `f ∈ U`, from exposure on an independent set containing
`P \ U`: `U` has at most two labels, or is a triple that occurs on no wire. -/
theorem sup_wit_exists {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (hS : Strict n D)
    (hC : sem_Comp n G D) {P U X : Finset (Fin n)} (hUP : U ⊆ P)
    (hU : U.card ≤ 2 ∨ (U.card = 3 ∧ ¬ sup_Occ n D P U))
    (hX : ∀ a ∈ X, ∀ b ∈ X, ¬ G a b) (hPX : P \ U ⊆ X) {f : Fin n} (hf : f ∈ U)
    (hnb : ∃ a ∈ X, G f a) : ∃ e, sup_Wit n D P U f e := by
  obtain ⟨j, s, hj, ht, h1, h2, hd⟩ := sem_exposure hG hS hC X hX f hnb
  have hsub : supp n D (src D (j, s)) ∩ P ⊆ U := by
    intro v hv
    rw [Finset.mem_inter] at hv
    by_contra hvU
    exact Finset.disjoint_left.mp hd hv.1 (hPX (Finset.mem_sdiff.mpr ⟨hv.2, hvU⟩))
  refine ⟨(j, s), hj, ht, hUP hf, h1, h2, hsub, ?_⟩
  rcases hU with hU | ⟨hU3, hmiss⟩
  · exact (Finset.card_le_card hsub).trans hU
  · have hne : supp n D (src D (j, s)) ∩ P ≠ U := fun h => hmiss ⟨_, h⟩
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    omega

/-- The output mask of a witness gate lies in the operand mask without the lost label. -/
theorem sup_wit_out (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) :
    supp n D (n + e.1) ∩ P ⊆ (supp n D (src D e) ∩ P).erase f := by
  obtain ⟨hj, ht, -, -, h2, -, -⟩ := h
  intro v hv
  rw [Finset.mem_inter] at hv
  rw [Finset.mem_erase, Finset.mem_inter]
  exact ⟨fun hvf => h2 (hvf ▸ hv.1), sem_supp_and_sub hS hj ht e.2 hv.1, hv.2⟩

/-- When no pair inside `U` containing `f` occurs, the witness operand mask is `{f}`. -/
theorem sup_wit_single {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e)
    (hno : ∀ M, M ⊆ U → M.card = 2 → f ∈ M → ¬ sup_Occ n D P M) :
    supp n D (src D e) ∩ P = {f} := by
  obtain ⟨-, -, hfP, h1, -, hsub, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  have hc2 : (supp n D (src D e) ∩ P).card ≠ 2 :=
    fun h2 => hno _ hsub h2 hfm (sup_occ_wire P _)
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hfm)
    (by rw [Finset.card_singleton]; omega)).symm

theorem sup_cost_inl {P : Finset (Fin n)} {e e0 : ℕ × Bool}
    (h : sup_cost n D P e = Sum.inl e0) : e = e0 ∧ supp n D (n + e.1) ∩ P = ∅ := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inl.inj h, h0⟩

theorem sup_cost_inr {P : Finset (Fin n)} {e : ℕ × Bool} {j : ℕ}
    (h : sup_cost n D P e = Sum.inr j) : e.1 = j ∧ (supp n D (n + e.1) ∩ P).Nonempty := by
  unfold sup_cost at h
  split_ifs at h with h0
  exact ⟨Sum.inr.inj h, Finset.nonempty_iff_ne_empty.mpr h0⟩

/-- The cost of a witness is admissible: an exit of the carrier of `P` with operand mask of
at most two labels, or a merge of that carrier with a singleton output mask. -/
theorem sup_cost_ok (hS : Strict n D) {P U : Finset (Fin n)} {f : Fin n} {e : ℕ × Bool}
    (h : sup_Wit n D P U f e) : sup_CostOK n D P (sup_cost n D P e) := by
  have hout := sup_wit_out hS h
  obtain ⟨hj, ht, hfP, h1, -, -, hc⟩ := h
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h1, hfP⟩
  unfold sup_cost
  split_ifs with h0
  · show e ∈ exitArcs n D (carrierT n D P) ∧ (supp n D (src D e) ∩ P).card ≤ 2
    refine ⟨?_, hc⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr ⟨f, hfm⟩, ?_⟩
    rw [sup_mem_carrier, h0]
    exact Finset.not_nonempty_empty
  · show e.1 ∈ merges n D (carrierT n D P) ∧ (supp n D (n + e.1) ∩ P).card = 1
    have hne : (supp n D (n + e.1) ∩ P).Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
    have hle := Finset.card_le_card hout
    rw [Finset.card_erase_of_mem hfm] at hle
    have hpos := Finset.card_pos.mpr hne
    refine ⟨?_, by omega⟩
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_inter] at hv
    have hA := sem_supp_and_sub hS hj ht false hv.1
    have hB := sem_supp_and_sub hS hj ht true hv.1
    rw [sb_src_false] at hA
    rw [sb_src_true] at hB
    rw [merges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr hv⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hA, hv.2⟩⟩,
      sup_mem_carrier.mpr ⟨v, Finset.mem_inter.mpr ⟨hB, hv.2⟩⟩⟩

/-- Two witnesses at the same position with nonempty output mask lose the same label. -/
theorem sup_wit_same_pos (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e)
    (hne : (supp n D (n + e.1) ∩ P).Nonempty) : f = f' := by
  by_contra hff
  obtain ⟨q, hq⟩ := hne
  have h1 := sup_wit_out hS h hq
  have h2 := sup_wit_out hS h' hq
  rw [Finset.mem_erase] at h1 h2
  have hsub : ({q, f, f'} : Finset (Fin n)) ⊆ supp n D (src D e) ∩ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact h1.2
    · exact Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
    · exact Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  have hc := Finset.card_le_card hsub
  have h3 : ({q, f, f'} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hff]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h1.1, h2.1⟩
  have := h.2.2.2.2.2.2
  omega

/-- Witnesses confined to disjoint label sets have different costs. -/
theorem sup_cost_ne_of_disjoint (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hd : Disjoint U U') : sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have hfm : f ∈ supp n D (src D e) ∩ P := Finset.mem_inter.mpr ⟨h.2.2.2.1, h.2.2.1⟩
  by_cases h0 : supp n D (n + e.1) ∩ P = ∅
  · have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inl heq.symm).1
    subst he
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 hfm) (h'.2.2.2.2.2.1 hfm)
  · have hc : sup_cost n D P e = Sum.inr e.1 := by simp [sup_cost, h0]
    rw [hc] at heq
    have he := (sup_cost_inr heq.symm).1
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have q1 := Finset.mem_of_mem_erase (sup_wit_out hS h hq)
    rw [← he] at hq
    have q2 := Finset.mem_of_mem_erase (sup_wit_out hS h' hq)
    exact Finset.disjoint_left.mp hd (h.2.2.2.2.2.1 q1) (h'.2.2.2.2.2.1 q2)

/-- A witness whose operand mask is the singleton of its label shares its cost with no
witness of another label. -/
theorem sup_cost_ne_of_single (hS : Strict n D) {P U U' : Finset (Fin n)} {f f' : Fin n}
    {e e' : ℕ × Bool} (h : sup_Wit n D P U f e) (h' : sup_Wit n D P U' f' e')
    (hs : supp n D (src D e) ∩ P = {f}) (hff : f ≠ f') :
    sup_cost n D P e ≠ sup_cost n D P e' := by
  intro heq
  have h0 : supp n D (n + e.1) ∩ P = ∅ := by
    have hout := sup_wit_out hS h
    rw [hs, Finset.erase_singleton] at hout
    exact Finset.subset_empty.mp hout
  have hc : sup_cost n D P e = Sum.inl e := by simp [sup_cost, h0]
  rw [hc] at heq
  have he := (sup_cost_inl heq.symm).1
  subst he
  have hm : f' ∈ supp n D (src D e') ∩ P := Finset.mem_inter.mpr ⟨h'.2.2.2.1, h'.2.2.1⟩
  rw [hs, Finset.mem_singleton] at hm
  exact hff hm.symm

/-- Fibre bound: one cost unit witnesses at most two labels, also across different sets. -/
theorem sup_fibre_le (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (c : (ℕ × Bool) ⊕ ℕ) :
    (Lab.filter (fun f => sup_cost n D P (wit f) = c)).card ≤ 2 := by
  rcases c with e0 | j0
  · by_cases hne : (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inl e0)).Nonempty
    · obtain ⟨f0, hf0⟩ := hne
      rw [Finset.mem_filter] at hf0
      have hcard := (hwit f0 hf0.1).2.2.2.2.2.2
      rw [(sup_cost_inl hf0.2).1] at hcard
      refine le_trans (Finset.card_le_card ?_) hcard
      intro f hf
      rw [Finset.mem_filter] at hf
      have hw := hwit f hf.1
      rw [(sup_cost_inl hf.2).1] at hw
      exact Finset.mem_inter.mpr ⟨hw.2.2.2.1, hw.2.2.1⟩
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  · have hinj : Set.InjOn (fun f => (wit f).2)
        (Lab.filter (fun f => sup_cost n D P (wit f) = Sum.inr j0) : Set (Fin n)) := by
      intro f hf f' hf' hs
      rw [Finset.mem_coe, Finset.mem_filter] at hf hf'
      obtain ⟨h1, hn1⟩ := sup_cost_inr hf.2
      obtain ⟨h1', -⟩ := sup_cost_inr hf'.2
      have hee : wit f = wit f' := Prod.ext (h1.trans h1'.symm) hs
      have hw' := hwit f' hf'.1
      rw [← hee] at hw'
      exact sup_wit_same_pos hS (hwit f hf.1) hw' hn1
    have hle := Finset.card_le_card_of_injOn (t := (Finset.univ : Finset Bool))
      (fun f => (wit f).2) (fun _ _ => Finset.mem_univ _) hinj
    simpa using hle

/-- `k` witnessed labels need at least `k / 2` distinct cost units, in doubled form. -/
theorem sup_wit_card (hS : Strict n D) {P : Finset (Fin n)} (Lab : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) :
    Lab.card ≤ 2 * (Lab.image (fun f => sup_cost n D P (wit f))).card :=
  Finset.card_le_mul_card_image Lab 2 (fun c _ => sup_fibre_le hS Lab U wit hwit c)

/-- Sharpened form: labels whose witness operand mask is their own singleton need one cost
unit each, shared with no other label. -/
theorem sup_wit_card_single (hS : Strict n D) {P : Finset (Fin n)} (Lab S : Finset (Fin n))
    (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * S.card + (Lab \ S).card ≤
      2 * (Lab.image (fun f => sup_cost n D P (wit f))).card := by
  have h1 : (S.image (fun f => sup_cost n D P (wit f))).card = S.card :=
    Finset.card_image_of_injOn (fun f hf f' hf' heq => by
      by_contra hne
      exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' (hSL hf')) (hsing f hf) hne heq)
  have h2 := sup_wit_card hS (Lab \ S) U wit (fun f hf => hwit f (Finset.mem_sdiff.mp hf).1)
  have hd : Disjoint (S.image (fun f => sup_cost n D P (wit f)))
      ((Lab \ S).image (fun f => sup_cost n D P (wit f))) := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc1
    obtain ⟨f', hf', heq⟩ := Finset.mem_image.mp hc2
    rw [Finset.mem_sdiff] at hf'
    exact sup_cost_ne_of_single hS (hwit f (hSL hf)) (hwit f' hf'.1) (hsing f hf)
      (fun h => hf'.2 (h ▸ hf)) heq.symm
  have h3 : (S.image (fun f => sup_cost n D P (wit f)) ∪
      (Lab \ S).image (fun f => sup_cost n D P (wit f))).card ≤
      (Lab.image (fun f => sup_cost n D P (wit f))).card :=
    Finset.card_le_card (Finset.union_subset (Finset.image_subset_image hSL)
      (Finset.image_subset_image Finset.sdiff_subset))
  rw [Finset.card_union_of_disjoint hd, h1] at h3
  omega

/-! ### The three disjoint charge classes -/

/-- Big merges, exits with operand mask of at least three labels, and admissible witness
costs are pairwise disjoint charges against `e_P + M_P`. -/
theorem sup_master (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (C : Finset ((ℕ × Bool) ⊕ ℕ)) (hC : ∀ c ∈ C, sup_CostOK n D P c) :
    (sup_big n D P).card + E.card + C.card ≤
      (exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card := by
  have hl : ∀ e ∈ C.toLeft, e ∈ exitArcs n D (carrierT n D P) ∧
      (supp n D (src D e) ∩ P).card ≤ 2 := fun e he => hC _ (Finset.mem_toLeft.mp he)
  have hr : ∀ j ∈ C.toRight, j ∈ merges n D (carrierT n D P) ∧
      (supp n D (n + j) ∩ P).card = 1 := fun j hj => hC _ (Finset.mem_toRight.mp hj)
  have h1 : E.card + C.toLeft.card ≤ (exitArcs n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun e he => ?_)
      rcases Finset.mem_union.mp he with h | h
      · exact (hE e h).1
      · exact (hl e h).1
    · rw [Finset.disjoint_left]
      intro e h1 h2
      have a := (hE e h1).2
      have b := (hl e h2).2
      omega
  have h2 : (sup_big n D P).card + C.toRight.card ≤ (merges n D (carrierT n D P)).card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card (fun j hj => ?_)
      rcases Finset.mem_union.mp hj with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (hr j h).1
    · rw [Finset.disjoint_left]
      intro j h1 h2
      have a := (Finset.mem_filter.mp h1).2
      have b := (hr j h2).2
      omega
  have h3 := Finset.card_toLeft_add_card_toRight (u := C)
  omega

/-- Counting form: big merges and large-mask exits, doubled, plus two for every label of
`S` (singleton witness masks) and one for every other witnessed label, against twice
`e_P + M_P`. Take `S = ∅` when no singleton witness is known. -/
theorem sup_count (hS : Strict n D) (P : Finset (Fin n)) (E : Finset (ℕ × Bool))
    (hE : ∀ e ∈ E, e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card)
    (Lab S : Finset (Fin n)) (U : Fin n → Finset (Fin n)) (wit : Fin n → ℕ × Bool)
    (hwit : ∀ f ∈ Lab, sup_Wit n D P (U f) f (wit f)) (hSL : S ⊆ Lab)
    (hsing : ∀ f ∈ S, supp n D (src D (wit f)) ∩ P = {f}) :
    2 * ((sup_big n D P).card + E.card) + 2 * S.card + (Lab \ S).card ≤
      2 * ((exitArcs n D (carrierT n D P)).card + (merges n D (carrierT n D P)).card) := by
  have h1 := sup_wit_card_single hS Lab S U wit hwit hSL hsing
  have h2 := sup_master P E hE (Lab.image (fun f => sup_cost n D P (wit f))) (by
    intro c hc
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
    exact sup_cost_ok hS (hwit f hf))
  omega

/-- Assigned exits: ineligible labels with at least three neighbours in `P` give distinct
boundary arcs of the carrier of `P` whose operand masks have at least three labels. -/
theorem sup_assigned_exits {G : Fin n → Fin n → Prop} (hG : sem_Gr G) (h : StrictLive n D)
    (hC : sem_Comp n G D) (P I : Finset (Fin n))
    (hI : ∀ i ∈ I, i ∈ ineligSet n D ∧
      ∃ N : Finset (Fin n), N ⊆ P ∧ 3 ≤ N.card ∧ ∀ a ∈ N, G i a) :
    ∃ E : Finset (ℕ × Bool), E.card = I.card ∧ ∀ e ∈ E,
      e ∈ exitArcs n D (carrierT n D P) ∧ 3 ≤ (supp n D (src D e) ∩ P).card := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ I → e.1 < D.length ∧
      supp n D (src D e) = {i} ∧ supp n D (n + e.1) = ∅ ∧
      ∀ a, G i a → a ∈ supp n D (src D (e.1, !e.2)) := by
    intro i
    by_cases hi : i ∈ I
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC (hI i hi).1
      exact ⟨e, fun _ => ⟨h1, h3, h4, h5⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose g hg using hex
  refine ⟨I.image (fun i => ((g i).1, !(g i).2)), ?_, ?_⟩
  · refine Finset.card_image_of_injOn (fun i hi i' hi' heq => ?_)
    rw [Prod.mk.injEq, Bool.not_inj_iff] at heq
    have he : g i = g i' := Prod.ext heq.1 heq.2
    have h1 := (hg i hi).2.1
    rw [he, (hg i' hi').2.1] at h1
    exact (Finset.singleton_injective h1).symm
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hj, -, hout, hnb⟩ := hg i hi
    obtain ⟨N, hNP, hN3, hNG⟩ := (hI i hi).2
    have hsub : N ⊆ supp n D (src D ((g i).1, !(g i).2)) ∩ P :=
      fun a ha => Finset.mem_inter.mpr ⟨hnb a (hNG a ha), hNP ha⟩
    have hc := Finset.card_le_card hsub
    refine ⟨?_, by omega⟩
    rw [exitArcs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_univ _⟩,
      sup_mem_carrier.mpr (Finset.card_pos.mp (by omega)), ?_⟩
    rw [sup_mem_carrier, hout, Finset.empty_inter]
    exact Finset.not_nonempty_empty

end SupMask

/-- Heawood: projected neighbourhoods of two distinct vertices share at most one label. -/
theorem sup_hw_inter (u v : Fin 14) (h : u ≠ v) (P : Finset (Fin 14)) :
    ((Finset.univ.filter (fun z => Adj u z) ∩ P) ∩
      (Finset.univ.filter (fun z => Adj v z) ∩ P)).card ≤ 1 := by
  refine le_trans (Finset.card_le_card (fun z hz => ?_)) (common_nbr_le_one u v h)
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz.1.1, hz.2.1⟩

/-! ## Block E (part): the subdivided K4 and its two surplus bounds -/

/-- Boolean adjacency of the subdivided K4: original vertices 0..3, and the edge-vertices
4..9 for the pairs 01, 02, 03, 12, 13, 23. -/
def k4_adjB (u v : Fin 10) : Bool :=
  (([112, 400, 672, 832, 3, 5, 9, 6, 10, 12] : List ℕ).getD u.val 0).testBit v.val

/-- Adjacency of the subdivided K4. -/
abbrev k4_Adj (u v : Fin 10) : Prop := k4_adjB u v = true

theorem k4_gr : sem_Gr k4_Adj :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

section K4Generic

variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}

theorem k4_mem_carrier {T : Finset (Fin n)} {w : ℕ} :
    w ∈ carrierT n D T ↔ (supp n D w ∩ T).Nonempty := by
  simp only [carrierT, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨v, hv⟩
  exact sem_supp_lt (Finset.mem_inter.mp hv).1

theorem k4_mem_exit {T : Finset (Fin n)} {e : ℕ × Bool} : e ∈ exitArcs n D (carrierT n D T) ↔
    e.1 < D.length ∧ (supp n D (src D e) ∩ T).Nonempty ∧
      ¬ (supp n D (n + e.1) ∩ T).Nonempty := by
  simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_univ, and_true, k4_mem_carrier]

/-- A system of assigned positions: for every ineligible label `i` an operand position of
a gate with empty support whose operand carries every neighbour of `i` and whose opposite
operand is `i`-pure; distinct ineligible labels get distinct positions. -/
def k4_Pos (n : ℕ) (G : Fin n → Fin n → Prop) (D : Dag) (pos : Fin n → ℕ × Bool) : Prop :=
  (∀ i ∈ ineligSet n D, (pos i).1 < D.length ∧ supp n D (n + (pos i).1) = ∅ ∧
    (∀ a, G i a → a ∈ supp n D (src D (pos i))) ∧
    supp n D (src D ((pos i).1, !(pos i).2)) = {i}) ∧
  ∀ i ∈ ineligSet n D, ∀ i' ∈ ineligSet n D, pos i = pos i' → i = i'

theorem k4_assigned (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) :
    ∃ pos : Fin n → ℕ × Bool, k4_Pos n G D pos := by
  classical
  have hex : ∀ i : Fin n, ∃ e : ℕ × Bool, i ∈ ineligSet n D → (e.1 < D.length ∧
      supp n D (n + e.1) = ∅ ∧ (∀ a, G i a → a ∈ supp n D (src D e)) ∧
      supp n D (src D (e.1, !e.2)) = {i}) := by
    intro i
    by_cases hi : i ∈ ineligSet n D
    · obtain ⟨e, h1, -, h3, h4, h5, -, -⟩ := sem_inelig_consumer hG h hC hi
      exact ⟨(e.1, !e.2), fun _ => ⟨h1, h4, h5, by simpa using h3⟩⟩
    · exact ⟨(0, false), fun hc => absurd hc hi⟩
  choose pos hpos using hex
  refine ⟨pos, hpos, fun i hi i' hi' he => ?_⟩
  have h1 := (hpos i hi).2.2.2
  rw [he, (hpos i' hi').2.2.2] at h1
  exact (Finset.singleton_injective h1).symm

/-- The assigned position of `i` is an exit of every union carrier meeting a neighbour. -/
theorem k4_pos_exit {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {i a : Fin n}
    {T : Finset (Fin n)} (hi : i ∈ ineligSet n D) (hia : G i a) (haT : a ∈ T) :
    pos i ∈ exitArcs n D (carrierT n D T) := by
  obtain ⟨h1, h2, h3, -⟩ := hpos.1 i hi
  rw [k4_mem_exit]
  refine ⟨h1, ⟨a, Finset.mem_inter.mpr ⟨h3 a hia, haT⟩⟩, ?_⟩
  rw [h2, Finset.empty_inter]
  exact Finset.not_nonempty_empty

theorem k4_exits_ge {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J : Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ ∃ a ∈ T, G i a) :
    J.image pos ⊆ exitArcs n D (carrierT n D T) ∧ (J.image pos).card = J.card := by
  constructor
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hi1, a, haT, hia⟩ := hJ i hi
    exact k4_pos_exit hpos hi1 hia haT
  · exact Finset.card_image_of_injOn
      (fun i hi i' hi' he => hpos.2 i (hJ i hi).1 i' (hJ i' hi').1 he)

/-- Flow budget of a union carrier: exits plus merges plus `p` is at most `2|T| + B_+`. -/
theorem k4_budget (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D) (b : Fin n → ℕ)
    (hb : PureBranch n D b) (T : Finset (Fin n)) :
    (exitArcs n D (carrierT n D T)).card + (merges n D (carrierT n D T)).card +
      (eligSet n D).card ≤ 2 * T.card + Bplus n D := by
  have h1 := carrier_flow_union h T (by rw [sem_supp_out hG hC, Finset.empty_inter])
  have h2 := surplus_carrierT_le h.1 b hb T
  have h3 := Finset.card_le_card (Finset.inter_subset_left : T ∩ eligSet n D ⊆ T)
  omega

/-- A projected mask with two labels is produced at an internal merge. -/
theorem k4_mask_gate (hS : Strict n D) (T : Finset (Fin n)) (w : ℕ)
    (h2 : 2 ≤ (supp n D w ∩ T).card) :
    ∃ j ∈ merges n D (carrierT n D T), supp n D (n + j) ∩ T = supp n D w ∩ T := by
  obtain ⟨j, -, -, h3, h4, -, -⟩ := sem_first_mask hS T _ h2 w rfl
  exact ⟨j, h4, h3⟩

/-- Two wires carrying two different pairs of a three-label set force two merges. -/
theorem k4_pair_merges (hS : Strict n D) {T : Finset (Fin n)} (hT : T.card = 3)
    {a b c : Fin n} (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) {w1 w2 : ℕ} (h1a : a ∈ supp n D w1) (h1b : b ∈ supp n D w1)
    (h2a : a ∈ supp n D w2) (h2c : c ∈ supp n D w2) :
    2 ≤ (merges n D (carrierT n D T)).card := by
  have m1a : a ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1a, ha⟩
  have m1b : b ∈ supp n D w1 ∩ T := Finset.mem_inter.mpr ⟨h1b, hb⟩
  have m2a : a ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2a, ha⟩
  have m2c : c ∈ supp n D w2 ∩ T := Finset.mem_inter.mpr ⟨h2c, hc⟩
  have c1 : 2 ≤ (supp n D w1 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m1a, b, m1b, hab⟩
  have c2 : 2 ≤ (supp n D w2 ∩ T).card := Finset.one_lt_card.mpr ⟨a, m2a, c, m2c, hac⟩
  obtain ⟨j1, hj1, e1⟩ := k4_mask_gate hS T w1 c1
  by_cases heq : supp n D w1 ∩ T = supp n D w2 ∩ T
  · have hfull : supp n D w1 ∩ T = T := by
      refine Finset.eq_of_subset_of_card_le Finset.inter_subset_right ?_
      rw [hT]
      exact Finset.two_lt_card.mpr
        ⟨a, m1a, b, m1b, c, by rw [heq]; exact m2c, hab, hac, hbc⟩
    obtain ⟨j, -, -, h3, h4, -, hcase⟩ := sem_first_mask hS T T (by omega) w1 hfull
    rcases hcase with ⟨-, hA, -⟩ | ⟨-, hA, hB, hU, -, -⟩
    · exact absurd rfl (Finset.ssubset_of_ssubset_of_subset hA Finset.inter_subset_right).ne
    · have hcard : 3 ≤ (supp n D (opA D j) ∩ T).card + (supp n D (opB D j) ∩ T).card := by
        have := Finset.card_union_le (supp n D (opA D j) ∩ T) (supp n D (opB D j) ∩ T)
        rw [hU, hT] at this
        exact this
      have key : ∀ w, supp n D w ∩ T ⊂ T → 2 ≤ (supp n D w ∩ T).card →
          2 ≤ (merges n D (carrierT n D T)).card := by
        intro w hss hc2
        obtain ⟨j', hj', e'⟩ := k4_mask_gate hS T w hc2
        refine Finset.one_lt_card.mpr ⟨j, h4, j', hj', fun hjj => ?_⟩
        rw [hjj, e'] at h3
        exact hss.ne h3
      by_cases hc2 : 2 ≤ (supp n D (opA D j) ∩ T).card
      · exact key _ hA hc2
      · exact key _ hB (by omega)
  · obtain ⟨j2, hj2, e2⟩ := k4_mask_gate hS T w2 c2
    exact Finset.one_lt_card.mpr ⟨j1, hj1, j2, hj2, fun hjj => heq (by rw [← e1, ← e2, hjj])⟩

/-- A label with two ineligible neighbours and a third neighbour is consumed at three
positions. -/
theorem k4_three_cons (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) {u i1 i2 i3 : Fin n}
    (h1 : i1 ∈ ineligSet n D) (h2 : i2 ∈ ineligSet n D) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3)
    (h23 : i2 ≠ i3) (a1 : G u i1) (a2 : G u i2) (a3 : G u i3) :
    3 ≤ (exitArcs n D (carrierT n D {u})).card := by
  have hu := Finset.mem_singleton_self u
  have m1 := k4_pos_exit hpos h1 (hG.1 _ _ a1) hu
  have m2 := k4_pos_exit hpos h2 (hG.1 _ _ a2) hu
  have hne12 : pos i1 ≠ pos i2 := fun he => h12 (hpos.2 i1 h1 i2 h2 he)
  by_cases h3 : i3 ∈ ineligSet n D
  · exact Finset.two_lt_card.mpr ⟨_, m1, _, m2, _, k4_pos_exit hpos h3 (hG.1 _ _ a3) hu, hne12,
      fun he => h13 (hpos.2 i1 h1 i3 h3 he), fun he => h23 (hpos.2 i2 h2 i3 h3 he)⟩
  · obtain ⟨j, hj, -, -, hju, -, s, s1, -, s3, -⟩ := sem_joint_meeting hG h.1 hC a3
    have m3 : (j, s) ∈ exitArcs n D (carrierT n D {u}) := sem_mem_exit1.mpr ⟨hj, s1, hju⟩
    have key : ∀ i ∈ ineligSet n D, i ≠ i3 → pos i ≠ (j, s) := by
      intro i hi hne he
      have h4 : supp n D (src D (j, !s)) = {i} := by
        have := (hpos.1 i hi).2.2.2
        rw [he] at this
        exact this
      rw [h4, Finset.mem_singleton] at s3
      exact hne s3.symm
    exact Finset.two_lt_card.mpr ⟨_, m1, _, m2, _, m3, hne12, key i1 h1 h13, key i2 h2 h23⟩

/-- Flow for an arbitrary wire set below the output: exits plus merges equal roots plus
surplus, a root being an input or a gate without an operand in the set. -/
theorem k4_flow (h : StrictLive n D) (K : Finset ℕ) (hK : K ⊆ inner n D) :
    (exitArcs n D K).card + (merges n D K).card =
      (K.filter (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))).card +
        surplusOn D K := by
  obtain ⟨hS, hL, -⟩ := h
  have hKlt : ∀ w ∈ K, w + 1 < n + D.length := fun w hw => sb_mem_inner.mp (hK hw)
  have h1 : surplusOn D K + K.card = ((arcs D).filter (fun e => src D e ∈ K)).card := by
    rw [← sb_sum_fanout_eq hS, sb_surplus_add_card (fun w hw => hL w (hKlt w hw))]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (arcs D).filter (fun e => src D e ∈ K)) (fun e : ℕ × Bool => n + e.1 ∈ K)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have h3 : ((arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∈ K)).card =
      ((Finset.range D.length).filter
        (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).card + (merges n D K).card := by
    rw [sb_card_arcs_filter, merges, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [sb_src_false, sb_src_true]
    by_cases hj2 : n + j ∈ K <;> by_cases ha : opA D j ∈ K <;> by_cases hb : opB D j ∈ K <;>
      simp_all
  have h4 : K.card =
      (K.filter (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))).card +
      ((Finset.range D.length).filter
        (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := K)
      (fun w => w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))]
    congr 1
    have himg : K.filter (fun w => ¬ (w < n ∨ (opA D (w - n) ∉ K ∧ opB D (w - n) ∉ K))) =
        ((Finset.range D.length).filter
          (fun j => n + j ∈ K ∧ (opA D j ∈ K ∨ opB D j ∈ K))).image (fun j => n + j) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨hw, hn⟩
        have := hKlt w hw
        rw [not_or] at hn
        exact ⟨w - n, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)], by tauto⟩, by omega⟩
      · rintro ⟨j, ⟨-, hj, hop⟩, rfl⟩
        refine ⟨hj, ?_⟩
        rw [Nat.add_sub_cancel_left]
        intro hc
        rcases hc with hc | hc
        · omega
        · tauto
    rw [himg, Finset.card_image_of_injective _ (add_right_injective n)]
  unfold exitArcs
  omega

/-- Wires carrying both `u` and `t`. -/
def k4_joint (n : ℕ) (D : Dag) (u t : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => u ∈ supp n D w ∧ t ∈ supp n D w)

theorem k4_mem_joint {u t : Fin n} {w : ℕ} :
    w ∈ k4_joint n D u t ↔ u ∈ supp n D w ∧ t ∈ supp n D w := by
  simp only [k4_joint, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  exact fun h => sem_supp_lt h.1

theorem k4_or_sub (hS : Strict n D) {j : ℕ} (hj : j < D.length) (ht : tag D j = false)
    (s : Bool) : supp n D (src D (j, s)) ⊆ supp n D (n + j) := by
  rw [sem_supp_or hS hj ht]
  cases s
  · rw [sb_src_false]; exact Finset.subset_union_left
  · rw [sb_src_true]; exact Finset.subset_union_right

/-- Common terminals: two labels whose carriers have no internal merge and which share a
branching carrier wire are consumed together at two distinct positions. -/
theorem k4_joint_exits (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {u t : Fin n} (mu : merges n D (carrierT n D {u}) = ∅)
    (mt : merges n D (carrierT n D {t}) = ∅) {r : ℕ} (hru : u ∈ supp n D r)
    (hrt : t ∈ supp n D r) (hfan : 2 ≤ fanout D r) :
    ∃ e1 e2 : ℕ × Bool, e1 ≠ e2 ∧ e1 ∈ exitArcs n D (carrierT n D {u}) ∧
      e1 ∈ exitArcs n D (carrierT n D {t}) ∧ e2 ∈ exitArcs n D (carrierT n D {u}) ∧
      e2 ∈ exitArcs n D (carrierT n D {t}) := by
  have hS := h.1
  have hsub : k4_joint n D u t ⊆ inner n D := by
    intro w hw
    rw [k4_mem_joint] at hw
    rw [sb_mem_inner]
    have hlt := sem_supp_lt hw.1
    by_contra hc
    have hw2 : w = outW n D := by unfold outW; omega
    rw [hw2, sem_supp_out hG hC] at hw
    exact Finset.notMem_empty u hw.1
  have hrJ : r ∈ k4_joint n D u t := k4_mem_joint.mpr ⟨hru, hrt⟩
  have hfl := k4_flow h _ hsub
  have hM : merges n D (k4_joint n D u t) = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun j hj => ?_)
    rw [merges, Finset.mem_filter, Finset.mem_range] at hj
    have : j ∈ merges n D (carrierT n D {u}) := by
      rw [merges, Finset.mem_filter, Finset.mem_range]
      exact ⟨hj.1, sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.1).1,
        sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.2.1).1,
        sem_mem_carrier1.mpr (k4_mem_joint.mp hj.2.2.2).1⟩
    rw [mu] at this
    exact Finset.notMem_empty _ this
  have hroot : 1 ≤ ((k4_joint n D u t).filter (fun w => w < n ∨
      (opA D (w - n) ∉ k4_joint n D u t ∧ opB D (w - n) ∉ k4_joint n D u t))).card := by
    have hne : (k4_joint n D u t).Nonempty := ⟨r, hrJ⟩
    have hm := Finset.min'_mem _ hne
    refine Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨hm, ?_⟩⟩
    by_cases hmn : (k4_joint n D u t).min' hne < n
    · exact Or.inl hmn
    · right
      have hlt := sem_supp_lt (k4_mem_joint.mp hm).1
      have hs := hS ((k4_joint n D u t).min' hne - n) (by omega)
      constructor
      · intro hc
        have := Finset.min'_le _ _ hc
        omega
      · intro hc
        have := Finset.min'_le _ _ hc
        omega
  have hsur : 1 ≤ surplusOn D (k4_joint n D u t) := by
    have := Finset.single_le_sum (f := fun w => fanout D w - 1) (fun _ _ => Nat.zero_le _) hrJ
    unfold surplusOn
    have h2 : 1 ≤ fanout D r - 1 := by omega
    exact h2.trans this
  rw [hM, Finset.card_empty] at hfl
  obtain ⟨e1, he1, e2, he2, hne⟩ := Finset.one_lt_card.mp (by omega :
    1 < (exitArcs n D (k4_joint n D u t)).card)
  have hexit : ∀ e ∈ exitArcs n D (k4_joint n D u t),
      e ∈ exitArcs n D (carrierT n D {u}) ∧ e ∈ exitArcs n D (carrierT n D {t}) := by
    intro e he
    simp only [exitArcs, arcs, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, k4_mem_joint] at he
    obtain ⟨hj, ⟨hsu, hst⟩, hnot⟩ := he
    have aux : ∀ x y : Fin n, merges n D (carrierT n D {x}) = ∅ → y ∈ supp n D (src D e) →
        y ∉ supp n D (n + e.1) → x ∉ supp n D (n + e.1) := by
      intro x y mx hy hyn hx
      cases ht : tag D e.1
      · exact hyn (k4_or_sub hS hj ht e.2 hy)
      · have hx2 := hx
        rw [sem_supp_and hS hj ht, Finset.mem_inter] at hx2
        have : e.1 ∈ merges n D (carrierT n D {x}) := by
          rw [merges, Finset.mem_filter, Finset.mem_range]
          exact ⟨hj, sem_mem_carrier1.mpr hx, sem_mem_carrier1.mpr hx2.1,
            sem_mem_carrier1.mpr hx2.2⟩
        rw [mx] at this
        exact Finset.notMem_empty _ this
    have hu : u ∉ supp n D (n + e.1) := fun hx => aux u t mu hst (fun hy => hnot ⟨hx, hy⟩) hx
    have ht : t ∉ supp n D (n + e.1) := fun hx => aux t u mt hsu (fun hy => hnot ⟨hy, hx⟩) hx
    exact ⟨sem_mem_exit1.mpr ⟨hj, hsu, hu⟩, sem_mem_exit1.mpr ⟨hj, hst, ht⟩⟩
  exact ⟨e1, e2, hne, (hexit e1 he1).1, (hexit e1 he1).2, (hexit e2 he2).1, (hexit e2 he2).2⟩

end K4Generic
end PEqualNP.Outside.L_meta_971_aux

namespace Geometry9798
set_option maxRecDepth 20000
set_option maxHeartbeats 0
abbrev V := Fin 40
abbrev R := Fin 113
abbrev L := Fin 19
abbrev K := Fin 576
abbrev J := Fin 6

def adj : Array Nat := #[0x9005000000,0x200a000000,0x4014200000,0x8028600000,0x50c00000,0xa1800000,0x143200000,0x286400000,0x50c800000,0xa19000000,0x1432000000,0x2864000000,0x50c8000000,0xa190000000,0x4320000000,0x8640000000,0xc80200000,0x1900400000,0x3200a00000,0x6401400000,0xc802800000,0x5004c,0xa0098,0x140130,0x80261,0x1004c2,0x985,0x130a,0x2614,0x4c28,0x9850,0x130a0,0x26140,0x4c280,0x98500,0x130a00,0x61401,0xc2802,0x185004,0x10a009]
def G (u v : V) := ((adj[u.val]?).getD 0).testBit v.val = true
instance (u v : V) : Decidable (G u v) := by unfold G; infer_instance
def left (u : V) := u.val < 21
instance (v : V) : Decidable (left v) := by unfold left; infer_instance

structure Valid (f : V → V) : Prop where
  inj : Function.Injective f
  side : ∀ v, left (f v) ↔ left v
  adj : ∀ u v, G (f u) (f v) ↔ G u v

theorem validId : Valid id := ⟨fun _ _ h => h,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩
theorem validComp {f g : V → V} (hf : Valid f) (hg : Valid g) : Valid (g ∘ f) :=
  ⟨hg.inj.comp hf.inj,fun v => (hg.side (f v)).trans (hf.side v),
   fun u v => (hg.adj (f u) (f v)).trans (hf.adj u v)⟩
def maps : Array Nat := #[0x9e69648e28607de75c6da6585d65544d24503ce34c2ca2481c61440c2040,0x9dc6587e27978e15a66da96481d54d2861503c45091d33082d244e0c2040,0x6266e789f7618d781c65a96459e5533033d014e25420d2872d2444182040,0x6159677977e259d8e66da66482170648d3c41504c32d43081ca44e242040,0x9df6648218a399e5576d895a71674d1ca44e3d050c1922094cb0840c5040,0x5a665e8a38217e475a6dc9576275535063d044e1cc28b2093521400c2044,0x5646668628e079f5986da95c5dd9d229438f41118c1d32482cd1050c0042,0x61c9648df5d689d7a665a6e78605493524501444ca2cc5072033ce182040,0x62666459776079f8556da9678a371350a44414e18c1d20c82cd3d0242040,0x9d795a9a179c82259f6d86648d575448b08e3c43484c730918a4500c5040,0x59a9577e39188a09e66dc65e85d5472d21504404c83543092863ce0c2044,0x55895c7a27d78637646da6668169c64cd10f4054892ca3081d43910c0042,0x91c6e78a359e7e05e695a65876154a2433d044430d2144cb1c614e482040,0x9266587e381d89685c95a6e779754c50615044e2931c934b2033c4482040,0x9156d85d68df7a08a665a96785d7120c91444503062135072cd3ce282040,0x69f6e786656281c8d795866459e7473033ce09020d25449318a4442c5040,0x5e66d68df76089885a95c65e9e455430345014e2132472cd2863c0482044,0x7246d589e5a385781895a66675f9ca30340f1112522064cb1d4385340042,0x9156678608e27567dc6da9585de9921943ce4502831cd2482d3144302040,0x91c9587605978637956da66789f98a35314e4444892c60c81d43d0302040,0x69d66779c9a159581f6d89648e25cb2943c408e1c318d3094d2450205040,0x5d56569187e39dd8a66dc95e86069218744015050329330934b3ce202044,0x7276557d77a27568646da96682360d50640510f2831d23082d3391240042,0x9e39585de89f7215606e465a99d5942d31443d034948620c28708e0d1040,0x62396785d7e29975566646da71e8092cd3ce1504d44831ca308084191040,0x61666789f5de55d7206e495a9a18d31d43d014418328d20c48b08e251040,0x59f95e8608e29a45586d765c6a774734b3ce4504cc48624850a0800c5044,0x55e9668238a191f9d76dc65a61d5862d339140f48c3542092870050c4042,0x75c96189f5de8d859a6e666092754a3523d01442c94c720c5064400c204e,0x7a69577e285d8e781a65c6d691854c4d21503ce2d43481ca243440182044,0x85565d5de89f5a78da6e696091871218a1443d01c350b20c4cd44024204e,0x76495f8a18237a659a6d86577159ca48d40f3912cc4c72091941020c0045,0x56796675f8a15e37a465a6dc5a060335338540f4942cc287209111180042,0x9269677968215e375565a6d87e270c4cd3c444e4942c3187209150282040,0x69766482671685579f9586e78a374850a44e0841d218c3532433d02c5040,0x5da65e89f6278dd92695c6d68215481c63d014050b28c4cd24344e482044,0x71866685e5dd8967e495a6d58e09c919438f1052931cc48b203411340042,0x69f96459c5637a689d6d86678605c73524440902cc4ca0c91943ce205040,0x5e695e9d876191f8156dc6568e26944cb3c014e48c3460c9287450202044,0x7249667575a07de8e76da6558a160a49338511134c2d40c81c640f240042,0x9e065a71e8665e27636e49587d558d1870843ce50828b24c4931500d1040,0x6166da99d5dc85f7a36649678958130c808e14424730b50a48d3d0191040,0x62095a55f7668978566e466779c8c634b09014e4c84870cc2943c4251040,0x59865c9a091a8639df6d795e89575318a08e4401c950d30848b3d00c5044,0x55765a9237d882275e6dc96686759250701140518828b30935338f0c4042,0x75a6608df6248979dc6e696179654b1c645014028850d24c4d23c40c204e,0x79a6d68e29e47e162665c95776054b2034503c030725350a35214e182044,0x85a96059e9e45e26156e665d7e37072cd4443c04884c60cc50a15024204e,0x75a6577a199c8a05646d895f8d69cb1d410f3822881923094cd4110c0045,0x5646dc5df8d676282765a96685e6123091054110ca20d5072d338f180042,0x9e66d85de85d5a281595a6648df7143091443ce0d320648b1ca450342040,0x9176e786059e9a371f65895a5627522033ce44431424d1c64cb090285040,0x9986d58a175f7a05e465a95c5a39d324340f3853062122872cd111500042,0x9d566459e8a35e17e695a6d876070318a4443d05121cc4cb20914e342040,0x91f95a9a08d58568976586e779c74c34b08e4504874c85062433c4285040,0x9a495c7a181689d8d865a6d57d79cc48d10f3914ca2c9187203405500042,0x6156e481d7e385789c95a6677969860cc44e15025220a34b1d43c44c2040,0x9dc6e48217967625d565a9587e398d24c44e3c40ca2121872d3150502040,0x91d6da7168267a385f9586678955ca0c808444e30b2473531943d0485040,0x7956d762789f9218e695c65681d6860c81403d03122544cd28744e2c2044,0x9a76dc5dd85e7e08a495a6558d66140c910538f30d20a48b1c64114c0042,0x6a36e779c5625e67e066495876158b2433c409021430d18a49314e1d1040,0x6a365876655f85c8966e496779780b50614e0901c92930cc48d3c4211040,0x6966d87d57178a67a096466785d8c70c91500842133063522943ce2d1040,0x71f6d682656385a89865795e9e474d30344e09024721319448b3c0285044,0x69e6d58e49e281885765c96675f58b30341100f20625250a3533851c4042,0x81c6dd7e35978a479a6669619d854d24315044420a30b1d44d23c018204e,0x8156e17968e25e47da96665d6277060c93c44502123072d350a14034204e,0x5e46dd85e5a089c8da65895f5669d230338f11120a24b1c64cd402500045,0x9d595876189f81e8dc65a6e459798349314e3d03462c928720c444502040,0x91d9678a38215569976d865a71e7ca2cd3d044e4834d4209187084305040,0x7959568218a37677da6dc65762498649344e3d02c3347209294140302044,0x9a79558e086259d7986da65c5df91435241138f4c32c62481ca105300042,0x91765a56359c8a079d6d89678667d250709044428818b0c94cd3ce305040,0x79a6577619d88229156dc9568df98b1d414e3c01882920c9353450302044,0x99865c5a07578e17e76da95589e91318a1113855091cd0c82d240f300042,0x69696786671e7555e36e46587e28074cd3ce0842c349424c286150211040,0x6a09585dc99d7958636646e789f58835314408e2c648950a3033d01d1040,0x71d95691a9a09d585f6d765e8a360a2d344008e3434873085063d0245044,0x6969557d892376781e6dc6668625c74d24050112c334630929438f204042,0x81595d6248df9d689c6e666179768648b1404503434ca24c5073c420204e,0x59595e9e48e26207e665c6d776168348b3c04504c634c50a24814e1c2044,0x81c6619e459e6235d56e695d7e268d2873c04441895120cc4cb15020204e,0x5e795d99c7a15568a46d865f8e069434b38210f4834ca309187411200045,0x7189558d65df81e76765a6e68629094d24111053462c350720c38f280042,0x6226e45977e371d56166795a9a079320c44415024a0d21d434b08e18f040,0x61e96481d5d699f7226e765a5638462d244e1444cc34a20350709024f040,0x5a26576248df6a05616de95c99d9d32941404501c819224c2cd08e0cf044,0x56165c5df89e6239e06e695a9167521ca10540f18950d20c4cb0110ce042,0x91f6677968e272055d9586da9a15cc1d43c445028d1832d324808e485040,0x9226d87608df99655e96765a71784a20914e4503130c62cd50708448f040,0x91e9587e35975607216676da99d88c2d31504444863491d40c808e28f040,0x6a06678959a17dc7569646d85de8c81943d008e1cd2834d23091442d1040,0x5e265681d7e399856795e6dc6a484828744e15051318334b30908048f044,0x7216558d67a29179dd9666da61f8091c641110f2925032d330800534e042,0x9216585d681d7239a26e795a55f7921c614444e28951320334b09030f040,0x5e79568df62455d6a16de65c9a08943534501404832c724c18a08e20f044,0x71d95589e5df9d66206e665a92384a2d240f1053434c620c50701124e042,0x7636617977e27185646e09666a758b5073c41502891923083530800d104e,0x7a36d776189f9a756465695c69880b24814e3d03140d22874cd080191044,0x85695d7e27975677246e06666988c74cb1503c448334a30819408025104e,0x75e65f8e08629269dc6d795869558b18741138f28c50d2484930020c4045,0x5576e68627dd9e361665c95a92079220c38f4050d42531ca34b011184042,0x8e695f5d681d7a485a6d56629d87144cd14444e2cc48720318a3c0242050,0x55766286671e81a5986df96392775250a3ce0841881d324c34b4400c5050,0x59866389e5df85c75a6e49609959d319440f1051c928b20c48d3820c0051,0x85c6608e27967e75da9666dd6245492864503c41cd5082d330314048204e,0x7559605977e379889a6666e19e470348d4441502c64c81d43093c028204e,0x79f65c9a18958278d89576d691a74c1ca08e3d018d5094d22034402c5044,0x7e46577a28d685581a9586dd99c9cc29410f4111d21882d3243382340045,0x7dc66381d5d685879a6d59629e498d29444e1441c918b2034933c0302050,0x89d95571e8665a78186df66391a5ca2d20843ce4c334624c1d4440205050,0x8e79565df89e75585a6e466099c61435310540f2c348720c286382240051,0x8276e37dd8625e679a66495671560d0c940538f21430b1ca493102180051,0x56765c5a389e81f85895a6e675790350a11140f18d1c94cb20c385480042,0x5586e68237dd5a25e795a65c7a190624c3914050d321434b1ca10f480042,0x76765f5668627207a49586d75a368350740238f28d18c4932481112c0045,0x55666675f8e062291e95c6da9e15c31d438541119328c2cd24800f484042,0x61c66785d5de81f59595a6e48e29892943ce14418d1c348b20c4504c2040,0x7a665692786062275595c6d77e368c5074403ce19328348d2481502c2044,0x9a46557dd8235e15a795a6dc7a260c2864053915121c334b20910f4c0042,0x71895e8666a781591f6576d68e27494cb3ce08034648c1d4203450285044,0x69796682461d8e77de65c6d58a15884933910052d434c18a24340f1c4042,0x81a9618a39277d661c6666dd5de5482d23d04403474c929430314418204e,0x81a65d5d69187a39d59666e189f7081ca14444018b5034933093d034204e,0x5da95f89e7158569a46586dd8239c82cd40f1024874cc286243391500045,0x71f65e9da5629268dd6d795682160d1c63c009028c50b0c849344e245044,0x69e6667589e17e48966dc9558e05cb19438500f1cc2930c9352411204042,0x5a66d762481d9e385565c95e89f69330814044e0d425218a34b3d01c2044,0x5e465f55c5a399e8276d895d86269228740211150c18d0c94cb38f200045,0x7276e68167a18d789865a9557dd90d0cc39110f2542131872d2405280042,0x62195a71776659f8226676e48d578948b08414e4c73482940cc45018f040,0x62265a99d7d58178de6e796459c85328708e15018850b30335244424f040,0x5a195c6a48266237626de6577d59c748d08044e4c92ca20c1941500cf044,0x56095a61f8e45e25a16e665c7a774634b0054114884c724c50a10f0ce042,0x91e65a9a059c7635e29676d87d584c18708e44428b5084cd0c915048f040,0x9216da5638267d675e6679585dc89224809044e3070cb19435314428f040,0x5e76dc99d61a81f92295e6568d58540c908e14020d30a4cb18745048f044,0x71d6da9165d88de7e19666558a780a0c801110524b30749350640f34e042,0x92295a7168d55e07e16e765876678a4cb08445048834724350614e30f040,0x5e165c55f7668d88276de95691a8921ca09014e50918d0cc2d344020f044,0x72065a9de5a48978dd6e69557d884d18700f11128850b0cc4d240524e042,0x76496671761a79f9e36e066189558a4930841402cc3542481873d00d104e,0x7a495c9a19da7626236566d77d580c48d08e3c02ca4c95070c8150191044,0x8646665629da7de6166e095d5dc8d22940903c01cc1930c834b14425104e,0x75c95892099a8e155e6d765f8a758a3530113822c948630850740f0c4045,0x55695a9e28e485f81765c6e67587834cb00f41148734850a24c385184042,0x8da6627969275e06266d595f76170b1ca3c444050819330348d14e242050,0x5589638266a485c9d76df6627967464cb44e08048935420c1ca3c40c5050,0x59a96085e7268975586e46637dd9c72cd38f1024c848624c2944050c0051,0x85a6dd7e29d88de91c9666605975472031503c024b30a35350644448204e,0x75a6e179762759f9156669608e270b2093c41400c73121944cd45028204e,0x7986d68219e49a269f95765c56374624344e3c031320735250a0902c5044,0x7da6dd8625667a37249586575a09c720338f40230b24a493194111340045,0x7da96285d62781791c6d566359e9872d33ce14034848a243194444302050,0x89866359e9e472169d6df9559a05d31944443c02891cb0cc35208e205050,0x8da66075f5665e27276e49567a160b1c638540250828d0cc49310f240051,0x81a9565dd99c7e15676646e389e6082d310538234748350a30940f180051,0x7646d77268165618e795865f89e68a3081023910d225435318740f2c0045,0x55e6da61f8a776385695c6668245c630800540f0cb2474cd294391484042,0x9df6da71e8955a18dd6589648265cd3080843d00c724b2864d244e505040,0x6206e779776171f9a396465a5625862033c414e24d3142d22870904d1040,0x9d66587617979a27239646da55f8031c614e3c45132892d2308090351040,0x9e06d87e285d55e99666495a7178cd2091503ce0c63131ca48b084511040,0x9976d58e075f92161e95c65a9e25942034113853122462cd28700f4c4042,0x9dd96459e86072299f6586da5635c32d24443ce34a4cc1c6248090505040,0x62365a7177d579d8a09646e786658950708415018b2883523033ce4d1040,0x9e36da9a189575e7d69646585dc81424808e3d00cb3074d2286144351040,0x9d695a56279c7e15e06646d87668c34cb0903c434748818a30914e511040,0x99e65a9208678dd89795c6d57d858c18701138f50b28848d2434054c4042,0x69d6e48d59a089c8576589677967cb0cc45008e20a2525064cd3c41c5040,0x5d56de85d7e28188da65c9569279920cc3ce15020624b1ca353440502044,0x9d76e48e279656171d95865a9a07d420c4503c40d224a2d318708e345040,0x59a6de86092776361595c6577e298720c3ce4400cb24648d2941504c2044,0x79d6dc6a786692281f6579568d560b0c90803ce30a20d1d4493450185044,0x9966da61d8247e18de65c9558a75d30c800539130724b18a35240f504042,0x8556e09278a361e7dc66695d5d66920c84403d024630d2944cb1441c204e,0x75c6e09185d69df7959666618a368a2484401440cd3064935073d02c204e,0x7e76d771589e9a386465895d81668d0c810240f3142522864cb3911c0045,0x6a26585dc55f5a68e19676e481d7882861440901d350948d0cc44e2cf040,0x69e6d87667178155a26679648df84b30914e0842060d32943524501cf040,0x7226d691a5636267e195e6577609ca20344009025330748b19414e34f044,0x6a16d57d89e25e47a096665c5a374724340500f21230635350a1112ce042,0x6a296482656375c7de6676d85d68484d244e0902ca34c1940c91441cf040,0x69e6648d57167e65e16e795876088b18a4500841cc51224335314e20f040,0x72295776655f81a8e76de65691884a4d214e0903482d40cc18744024f044,0x6a195c5a49de8d889d6e66557d780748d11100f2c94ca0cc50640520e042,0x6a16e459c9a05d57629676587e378724c44408e2120ca4cd5061502cf040,0x7276d77d56988e692165e95681d88d0c81500802543121c62d344e28f044,0x69d6dc7a76178a47e06669558d684b0c910f00520a30d1944d24111ce042,0x9a36dd5dc55f79a8a49606619d859424314409030b20a48d1873c04d104e,0x72365e86656275a7e49566d76278095063ce09028b1cc4930c8140351044,0x9966e189571e7da5e466095d6278d30c93d008430721228634b14051104e,0x61e6dd8249e18da89c95765f56658630339100f24b20a3525074024c4045,0x6976558a761f86475695c6e682378850640f0051d22834cd24c3912c4042,0x8a66e359e8605e775a65595f6247133094443ce2140cb1c648d140282050,0x8d76d59a059c86479895f6629da75420308e4442523064cd1ca3c02c5050,0x8186d67a17578a67da96466355c9c624310f3852133072d2294402340051,0x89c6df76179782759a95566391898a24c14e3c420d0c72d21944404c2050,0x8dd6e279682172499865f9556a75cb0c83c444e24a313187352080505050,0x5a76607577a17dc89a9646e356660350638510f1cd2882d23094024c0051,0x9dd65a5628668de8179586e459c7c32870903ce50b18849324c444345040,0x5956577608df86489a95c6de9d898319414e4501d22882cd24c3c04c2044,0x79d6568e28605679986d795c6a47cb2874503ce18351324848d080305044,0x9966558a18239dd9176dc95a61f7931c640f39150329220934b005304042,0x7e765d8238a159579a6d895772690d50a39140f1c318b2094d2102300045,0x79895c5629da8e191d6d76568267c64cd0903c02c948a0c850744e305044,0x99795a9e17588a07d66dc6558e479448b00f3854c83470c9286411304042,0x5da95681d62485f9d565c6de8a39882d344e14048734318a24c3d0502044,0x7da9575a355c8229a76d865d85e9072d21114023484d40c918a38f300045,0x6a19587d599d8dc81e6e766459788749315008e2c934630350a44420f040,0x7276568266a47556226de9577e384d50744e08028319320c2d215024f044,0x69d6558e461f5a75e16e695c7a280b2864110051c351224c4cd10f20e042,0x72165761a99d91582295e6d68df9c91d414008e2921884cb30345034f044,0x6a065c5d89167e78e19666d589e74818a1050111cd50949330340f2ce042,0x99665d61a7179d57a36e096189f9131ca14008450318b2483523d031104e,0x7206de9da9a16157636569577e290d20c3c008e2460cb5074d2150291044,0x9a39619da56261c7d66e065d5de9142d23c00904c93470c818a14431104e,0x61665d99a9205678de6d795f8a17131ca38201118350b30848d40f244045,0x89c9639277966215e66d565f76068a34b4403c44c949430318714e202050,0x8dd6556a48269d68576df96279c60b28608044e5031d220c3533c4245050,0x82765672685e55d8986e49637d768d50710238f18329324c48b405200051,0x7556619d87e29178dc9666e059e6831873c01502925093533084442c204e,0x85c95d6277979225956666e08df68934b1403c448a4c31943084501c204e,0x59d65e9e48216a399f9576dc5626032863c044e1cb50c3522090904c5044,0x8a665f62785d91e81c6d59635976935071403ce28c18d24348b444202050,0x8d79629e459e6a071d6df6559a16144933c04442c834a0cc1c608e245050,0x81896356675f7215e76e46567a26864cb4023853494940cc28710f200051,0x5986e099c5dd55e7e76649638a16932483821050c630d50a48b40f1c0051,0x5da65d8167268de5679586df8a19081ca39110250b18335324c40f480045,0x5e36de9d87e269d56095665c9a191424c3c015020b0c63531ca08e491044,0x7226e67577a16169e395565a9207ca20c38510f2530d42d2187011350042,0x5e465e85d62799f6a36d695c5628122863ce14050c1cb2434cd090211044,0x71f6668165dd91e6226d595a9e18cd1d439110528c19320348b00f250042,0x7629609187e369755e6e16667169ca4cd4401502c84863091d40840cf04e,0x79f9569278a36a155d6576dc9a060c3534403d02c748329420908e185044,0x8576609277966a271f6dd9665636125064403c41c828d3032d309024504e,0x76295772685e6a09e36df65891654a4d210238f2c835424c1c60110d0045,0x55d95c5a37d79226216666da9de8032cd11140548a4c91d430800f18e042,0x99e9557dd8626209d665c6da9235cc2d240538f4c63431ca248011504042,0x9a26dc5a085e91d9df65595a6178d320911138f30a0cd1c648b005510042,0x6216648df76055799e9676da7168891ca45014e19250c2cd0c80844cf040,0x7a46577e29d85616a09566dc99d8cc2941503c01921c83530c908e2d1044,0x99f65c7a17579e06239556da91688c1ca10f38550d1892d20c80114d0042,0x69796789571e8e659d6586e48217c848d3d00842d44c328624c44e1c5040,0x7219568d59a07da76765e6d762488949345008e3472c350630814028f044,0x6a09558a792379859d6666dc5df84835240f0112c64c32943091051ce042,0x82295d5d68df7245676616e66987884cb14445034a48350724c08018f04e,0x8176618a359e56471895d6e66a77c85073d04441922894cb0cc08034504e,0x5e295d8167a191c9d565f6d86a68c84cb39110f48a343187309002510045,0x7a095762785d6a29a36d665c55f9063521403ce2c84d42431ca090311044,0x9a395c5dd8166219226d565a9de7d42cd1053914c948a20318700f310042,0x82765d7e391855669e6e196671788d50a1504401831cb30949308420f04e,0x5986de8a392756069d65795c9a17d324c3d04400c620b29448d08e1c5044,0x81896179692772369f6dd6665625c64d23c44403492c730329409020504e,0x5d565d85e7269d66a36df95892089218a38f1025031cb24c353011210045,0x7206d57d75a361e92166695a9e274d2034051112463121d44cb00f28e042,0x8de65f7605979a47276e295569884b18714e44450c28d0c84d208024f050,0x56096279c9a15da7646e365f6275863533c408e4882ca3095071400d1050,0x5a19637d77a261c9e66e066469574748b40510f4c935430818a0020ce051,0x85f6e059e8a372755895d6666a45c73084443d024d0c64cb29408048504e,0x75e6e08df5d65587276619666a488b3084501440c624d50749308028f04e,0x7a06dc5628667e776495665761a8c62090903ce30d0ca4931d41402d1044,0x7e16d75a389e9159e695d65869c80724811140f3120d44cb28600234e045,0x7e19635977607189a76e26556a478748b44414e3494d40c828608030f050,0x8966559a179c7675e46e395f61a8131c608e3c42835123092cd140211050,0x8dd6567a27d79d56266e096469c84b28710f40550319330835200224e051,0x8179638a175f9e661c6566e469578848b40f3853544c92870cc002184051,0x5606dc7a28d69df91d96665a61784620910f4110cd30a2d350700548e042,0x75c6df8a19959e069695765892378a24c40f3820cd2074d25060112c4045,0x81f6667168d57a48986dd9619da5cd1d408445018c2932432d23c020504e,0x86465e5dd8167e68da6e796255c6122861053911cc50b20335340224004f,0x55695f76671785a7a46636e29d88034cd14e0844872cc2942483c0191050,0x7206577d599d89a8646d695e9d88cd19415008e2881d23034cb3c0251044,0x9d79628e461f81a75c6de6619955944934110053482ca24c1873820c404f,0x7a49627d75a375c81a6676e199560c4934051112ca3481d40c938218004f,0x7e666279776159881a9556e392770c50a3c414e1d31882d20c9440342050,0x8979638217969a771865f6d56a474848b44e3c44d4349187303080285050,0x8d89608627dd7955da6646d67269c94cd38f4052c64881ca303102500051,0x8dc96286059e7645da6556df6279893533ce4442ca4881c60cc140502050,0x55d66359c9a079a85895f6e29e45c329444408e18b1c94cd3083c0485050,0x86396671e8955e77e46606dd61a5892d30843d049434c2862031401d104e,0x5e395c99d7d58588a46d665e9da8142cd08e1504894ca3031c63c0211044,0x75666655f5dc8987a49606e19da8c31d409014429318c48d2093c02d104e,0x7de9589238a781585c6576dd99a58c2d301140f3464892942033821c4045,0x9979608d571689a7986dd6619e47d448d4500844c82c62432873c030504e,0x7989618165dd8dc7da6e76625669064d23911052c934720350a40230004f,0x7e06d57177667988646639629da58d20308414e3062522942d33c01d1050,0x89666761f8e475581c6de96199a5d31d400541128318d24c2d238220404f,0x8986de5a37d781575a66796199c91324c1114052060cb1d435238228004f,0x5e76df8d67a281c85a95865d9959140cc41110f20d2472d318a382480045,0x8586628e075f5a65da9676de71590918a4113851d35082cd0cc10248004f,0x8e76e09958a171f7989646565dd6940c838240f24d3064d22871052c0051,0x8566e27dd82362691c95e6676955c70c840539125330a34b19400248404f,0x7679575a085e8e689a6586df55c90335211138f2d44c81c624c402280045,0x75a6df8e09955a17276589577a290b20c4113820c724d5064d210f280045,0x5a796355c7a29978586646e075f68334b40210f4d448918a3083851c0051,0x8d86567157d79a27679646e085e68918710240551328335230838f2c0051,0x75695f5668236a191e6576d89e27034cd4023912c748c19420900f284045,0x7e495d9958e07225a76586d77a168c48b38241134a4c350624810f1c0045,0x9a466179c6a75d56239606dd7e258c2873c40805121892cd2031504d104e,0x7246d77666988559e395665e89f80a30814e0802520d42d31c63d0351044,0x9a495d7d569889c9d66606e17978cc48b1500804ca3431c62093c451104e,0x61c65f8e469582799e9576dd86258928741100218d50c2d220338f4c4045,0x6966e68679208988d795c6557dd7870cc38f01121325448d2864052c4042,0x89a95f5de9d85a19266556e381d7082cd1443c04c748c5060c944e282050,0x8d866286092799669795f6d571e74918a3ce4405131c848d3030842c5050,0x81a6638a199579d7189646d65df9c81d440f38218b2894d2303105340051,0x89a6638219e475e61c9556df5d69881d444e3c028b1893520cc1444c2050,0x8d895571691a7a09dd65f6e28665c94d20844402c63432873083ce505050,0x59a6e37d771575e9a79646608626072094051020cb31435228638f4c0051,0x72395761a55f9e68a06566de85d9092d21400903544c81870cc3ce291044,0x61e95f55a9e29a48566d765d8237062cd40200f4cc4870c850a391244045,0x59f6dc6a48d59e089d95765e8666073090804500cd20a2d25063ce4c5044,0x5e065c6987669df8639566de89590818a08014e50d1c92d30cc3d0491044,0x72365a6175a475e8229556e68677c950700511128b1884d20cc38f350042,0x72295a9167a781785f6d56667588ca4cb01110f348487303194385250042,0x75e6666985dc91f5a26e19608d59cb19408014428c1d320948d4500cf04e,0x85f9666a789591e8d76dd66059c6073530803d048c2d420328644424504e,0x7636586a68247215a26df9577a754b5060023912891d320c35210f0d0045,0x5616da9238a759f79d66695c5d881224801140f0c730b2944cd10518e042,0x99f95a9207585a15e26556dc7a78cc34b0113854c74882860c910f510042,0x61e6da55f5dc8dd5a196766482688630809014424b0c748d50a44e4cf040,0x9a36da9e182479d59f95565c5d889424800f39130b0c735218a1054d0042,0x8276e671691a5e362266195d7d578d0cc08444021425328748b15018f04e,0x8186e656391a8969d795d66179c7c624c0904402130d448b2873c434504e,0x5d56d891671a81e9a265f95d8678d20c901110220631328734b38f510045,0x7a365c6a78956217e06d695776690b50a0803d01891cd2034d214e311044,0x9a265a61d8675e07a36d595c5a47d328700538f50818b24348d111310042,0x81e96656359c7e45e76e165d61a8862d309044434c4940c91ca14020f04e,0x59d95c5638268a48586576de9da7c32cd09044e4ca48919420c3c01c5044,0x5e39589de5a485c8156df65d99a8942d300f1114893460cc1ca382210045,0x72195a6177a77d68a06666d58e474948b00510f3474c819430341128e042,0x8e79559a091a75661e6e265f5dc85435208e4402c34c630828714424f050,0x56465f5dc6987a69e06e396285d59228714408018c50d2092d33ce0d1050,0x5a666461771a7de5616e09638a775350a0051021cc19224834b40f0ce051,0x85866671e9da5a291f95d6e08d55c91940843c01d328c34b0c845048504e,0x76796655f61a8d791e6616e059c8833530901402d448c18724844428f04e,0x7e665892355a5a272195d6d77a780c5060114021d328948b0c810f34e045,0x7e765571761a59d9216e296382678d5060841401c32922484cb44e30f050,0x8a495f7619d899e6966e365571780a48d14e3c04cc2c70c9506084211050,0x8e69649e255a79f71d6e06565d88544d200f4022cc34a0c818710524e051,0x81c6e49e199a89d5576569637d878d24c00f38220a0d25074cb405184051,0x55d65a9e27d87a35e09666dc5a484328700f40518b50835330911148e042,0x7566589e18248a68dc9576df55a7831c600f39129350935220c4022c4045,0x85a9627dd9955e07246e765e5a36072d340538248834a30350611124004f,0x5646e28666a775c61666395f5de8123083ce0800ca2531d42cd144191050,0x72495e8956a77e66206d66577618ca48b3d008034c4c62031d414e251044,0x9dc6618246a68d85576de9627dd58d28739100250919220c2d34050c404f,0x79a6e17577267d65646679628e060b2093851023070d229435341118004f,0x7da6e359762479d9e695566286070720944414030b0d44d218a3ce342050,0x8986d59a19da81e91765f96359c75324308e3c020631250734b444285050,0x8da6d67a255c85f9986649607579cb20310f40224731318a48d385500051,0x8da6df7609188569dc65596279798b20c14e4402470cd2864933c4502050,0x5586e279c6a75a691d95f6638215c62483c40800d330a2cd1d444e485050,0x8646dd5de9d87226a366096655f5923031443c024a20b5063530901d104e,0x7646e189f62755769696066671e8ca3093d01400d22074cd1940842d104e,0x7dc6dd82356692269e6579589e158d24339140230a20b19449300f1c4045,0x9986618956a78dc9176dd96059e7d31873d00805092922032cd44430504e,0x79a6628d67158179986e796175f90b1ca41110218851324335238530004f,0x7e496279762771d6a06636d59a158c4933c414034a2c819424308e1d1050,0x89c96175f5666236966de6679205ca3523854024c92c70cc19401120404f,0x89a96182356659f7186676de5dd9082d23914024c73491940cc10528004f,0x85a6de5a099c8dd5589676627d790720c11138224b0c64cd50a40548004f,0x85c66761d99a7e055695e6e28e45c92940053821cd1834cb30841148404f,0x75e6d86a686756089665795f8e470b30900238f0c62131d448d411284045,0x5e16d691876069f9a265e95c5639d224344014e2073132862cd09050f044,0x5a79577609189a36a265e6dc55f84335214e4404d42c82863090901cf044,0x5a16d77e381d5649a795e65c69888724815044e0d231434b18a0804cf044,0x5e295c6987d591d8e165e6d68269c84cd08015048a2c91c630344e50f044,0x5a26dc9a08d57647e765e95761a85320908e4500ca30d5062d21401cf044,0x5a765c56391a7e062195e6d776688350a0904401cd18948b30814e4cf044,0x71d6de8959a18da8189576569277ca0cc3d008e24b2064d2507440345044,0x8566e66a779c6225e396065d7d59070cc0803c42532142cd18a15049104e,0x7636e66987d59d789666096179c90b24c0801500d42131c63523c429104e,0x7d66d86958e49a281e95765d8677070c90024113132062d250a38f344045,0x7dc6e29d85de91d5a665596382168d2483c014430a0d350648b44e1c2050,0x89d6e392786069e99795f65571660a0c94403ce20b31448d1c60844c5050,0x8e66e29e482161675c95565f5de6943083c044e2530ca3521871442c2050,0x5576e391a7169e679d65f9628606122094400840d430b2873533ce185050,0x6a295c5d89de7648636556e68167c84cd10500f2ca4895060cc3911d0042,0x69f6dc5a461782776295566685e8c730911100520d0ca4d219438f2d0042,0x9a26dd61a55f91c8de6619605979d320314009030a24b18748d44450f04e,0x9976e19da71e91559f95d6608e26142093c00843120c734b2864504c504e,0x6226dd99a9e17247a365f9575a055320338200f24a30b507352111190045,0x6a26668249e159879f9556dc5dd8c829439100f1d318c3520c91052d0042,0x69f96686761d7a45e36d565c5a088735338f0052cc49424318a111210042,0x9a266059c5635da7e76e195d6247932864440905081cd0c948b14030f04e,0x6226575a49de81a8556df95d99c8d329411100f1881d20cc34b382250045,0x6a36e67589205e75a265595c7a17cb24c3850112140d328648d10f1d0042,0x9a76e08d56a47dc61e96165d5d68940c845008030d2462d21ca1444cf04e,0x7186568d56a48a69dd9576de8607c91874500802935032d220c3ce345044,0x9986e059c6a47959df65d9618a35d32484440803060cd1ca2d23d050504e,0x6156d77a769c8649a395f65d8168860c810f0022523142cd1ca3914d0045,0x55e6e382671675a5e796265f62484630944e0840cb21435328714048f050,0x9216d65d89de7da8a666096355c75224310500f30721350634b40228e051,0x99f96179c56259a8d865d6e09275cc3523c40904c72c918a0c844050504e,0x99e65d7d57178da5a79616e091888c18a15008450b1c33522484404cf04e,0x5e095e89f7615589a46566dc6a78c834b3d014e4864cc2870c9080511044,0x62195f8e49e259a7a665d6d771580948d41100f4c72cc50a0c810218e045,0x5616df5dc99d59a82766296391879224c14408e0c720d50a4cb44018f050,0x7d66e285d5de9987249636556a78070c83ce14431324a48b506080351050,0x91d6e38a761f79a5e696065671584a0c940f00530b2144cd18710248e051,0x91766086761d89a7dc6d696356679250638f0052881cd2434cb402304051,0x61c95d8676a68a45566576df8e078934b38f0024ca4831d420c411184045,0x8a46e175f8e05d559a96765e72660a3093854112120c72cd5061024c004f,0x8576e79207588e67dc65e96255a59220301138525430d2862d34021c404f,0x8576e656279c8e759865d96091a7d220c0903c42540d318a2cd4401c504e,0x8a065f5de85d7279a49636d56985881871443ce28d50c48b2430804d1050,0x9d69617589207da8dc65e6e25665c34d23850113472c928630840250404f,0x7d695d8628e09d591c6d76586a67874cb38f41134348a248506002304045,0x5e46dc55f61a89d9e065695e8668d230909014020a0cd1874cb3ce511044,0x7dc6589e255a8639966d795d82478d28600f4021c95130c848b391304045,0x6a365c7a791685881f6d596675788b50a10f0111c918d303493385210042,0x9a795d5dc6985959226e16608df79434b1440804c348a2091c645030f04e,0x61595d8246a65a77226df6577a18c648b3910024c334a20c1d410f250045,0x99e96091a7166155e26616dd7e39cc2cd4400844c648828724315050f04e,0x99f66091a5639dc89795d6e179660c1c644009050d28848b0c93c44c504e,0x62395771a9169a782265f6dd85e5492d21020114d434828730338f190045,0x56166391a9a061c75e6e295f5d69d21d444008e18928b3084cd1440cf050,0x7d69556985dc9dd7a06e36628669074d20801443432c620950a3ce311050,0x91d95671a6175677e16e066389e98a2d310200548334724819440f30e051,0x6206df55a9237275a195d6577a298620c40201124d0c748b29410f4ce045,0x55e95f61a7179265a16e266381d9c62cd14008448c4c724829444e0cf050,0x7e06629d87616979966e395571e90d18a3c014e1c85130c92d2084311050,0x92166355a9e271879d6e09565df9921d440200f28918b0c835310530e051,0x91e96099a9e15588976566e37dd70c2cd38200f4864c85070c9405284051,0x8986619957dd7235e46e795e5a069318738240528951230334b11120004f,0x8a09556a786661e7566636df5dc9083520803ce4c62c31d424c144291050,0x8569676a682455d8d76de6627d87074cd0023914832d420c18a40524404f,0x85895e7267575607e46676e28d66894cb10238548634c2940c84111c004f,0x8dc65f6245979e07a69556e285d68928714044450d18c4d20c83ce2c2050,0x55d9629da9a191c81765f6e359e6032d33c008e48a348507309444185050,0x7e69639187609d785c6556e279668c4cb44014e3544892860c83c41c2050,0x8976556a779c92159d95f6e38266085060803c42921c32cd30944e4c5050,0x7569619d85de69f7236606e65629034d23c01442c734950620c09029104e,0x86365d62789f69e5569606e671790950a1403d01cb1834cd20c08449104e,0x8a495e7158d699f8186e766175768a48b1024114cc34624350738520004f,0x8966df6277976a172066395599d9130cc1403c420724d1942d208e291050,0x85766256675f6a06166de96792371250a4023851c81930cc2cd01124404f,0x8646e256682371d59866795e5df69230840239124a0d319434b1051c004f,0x7a466199c5a05578d89676e27dd68c2873821111925094cd0c84052c004f,0x9d76e199a61d5647d695e6628e07142093820050d23074cb18a41134404f,0x81f6e19e48e269655765d96671e60d3093c04502070d250a2d308418504e,0x81e6dd6245976a372296166655f9c630314044420b24a4d21d409034f04e,0x5e16df55c7a26969e065d95892399224c40210f2070cd18a2d301150e045,0x5e695f8d671591e6a16dd6589e28144cd41110248c2c724328600f20e045,0x72396685e5a09d791f6556da61d8892d338f11135448c1c60c8005290042,0x5a266099c7a16979df6e396461d55328638210f1c850d3092d20050d0051,0x7de65d9958a16a39d69576d892070c18a38240f1cb5034d2209011344045,0x8d79609957dd6a261e6d66649e171448d3824052c84c63031ca00f244051,0x81f6d67267576a16226639649de54d3031023852072532942d200f190051,0x7556575a099c9216a295f6d89de8c31941113822921c84cd30900f2d0045,0x8589608e29e455e69765d6e67167c94cd4503c04862c850a0cc0841c504e,0x76766059762471f6a29616e656378350644414028d1c84d224c0902cf04e,0x7e69577a255c9e36a065d6d891684c4d210f4023542c818a0c90111ce045,0x62365d86792079a59595f6d772688950a38f01118b1c348d3081024d0045,0x8e16557168265e47679626df61a7891c608444e51228335320c1402cf050,0x8226565dd85e6269d59636e469c7c828710538f19350348b24c002350051,0x59f6e085e5dd9dc6159636646a688730838f1050cd24648b50a0024d0051,0x7e06577158d66a29216dd9589de98d1941024111c82922432d300f30e045,0x8159567a199c9dd69f6e366461788649310f3823432c730950a005210051,0x81c6637dd99562169e6d69649e25cd2944053821891cb3034d200f204051,0x59596075772661e6a26636e49e17c348d3851024c62c829424c00f1d0051,0x5e36dd99c5a069e92295f6589e155424338211120b30a4cd1c600f490045,0x85f95e5a07579266156e266769c8c734b11138548c4c60c829400225004f,0x9e06627d89235da5a66e195e71574d18a4050115081d330948b1020ce04f,0x79d6e28d65df91c62666196769580b0c841110530a25350748d00218e04f,0x8de6e075f8a16159dc6569646a65cb30838540f2460cd2874d2002504051,0x7626e67177d55988e796166091a78a20c0841500d32543521c64402cf04e,0x7e06d89e28e47955a665d95771a84d20900f4113060d350a2d21021ce045,0x7a36617575a061c9156e29676a67cb5073851111892920c84cd00231004f,0x7de95599d5dc8185a76626e391a84c2d208e1443464c350a2094401cf050,0x89d9679237d85955e66e165e71a80a2cd0114054c34943091c610220e04f,0x8a095e5df8d66159266616e769c74834b1054114c648c50724300228e04f,0x5e065f89e5a39dc92695d6d869584818740f11150d28c4cb0c900248e045,0x8dc6608625669df6979566e461d78928638f40250d1c84930cc0052c4051,0x7636d77a18169e691565f95869c88b24810f3910d4312187353002290045,0x5a66e389e7159d769d66096461f85330940f1020d420b2863520051ce051,0x8e66d65df55c6226a19606649de75430310540225320748d18a00f2ce051,0x81e96461d8677e689c6d666355a5c62d200538f34c4ca2431d4402204051,0x56765f76669881c91e9626e359784350714e08018d28c2d320944448f050,0x9dd65e5a46178da7e69616e255c80328611100550b1cc4d224840234e04f,0x6209577a791689a8e66dd65f55c84635210f0114c82d430328740224e045,0x6166df8a792385a81c65795d9957930cc40f01124720d29448b382184045,0x91e6637d89e275a85c9566e09955cc19440500f28b1c93530c8382484051,0x8976618237dd91561c95e6e76a658850739140529218934b3030024c404f,0x8226666a48d56167de9616dd5dc9c82940804501931cc2d224314434f04e,0x8e166461f8a75d57a69606d671a7491ca00540f51218c4cd2031022ce051,0x5e16589167a78dc8a66dd95f55a8121c601110f5092933032cd40220e045,0x59d9649de5d889c7e66606e355a8432d200f1054ca34c5062094021ce051,0x8d76e49e27d885575c95666099a79420c00f4052520ca3531c63822c4051,0x7e16d569876691781e96266359c9c724308014e3122062d329444434f050,0x7a06e76175a47dc8e696166255a74620300511130d2544d21ca4022ce04f,0x7986e255c5df9967649676618236862484021053130ca48d5073912c004f,0x8966e19958e069f91765e96761d7130c93824112073125062cd00528404f,0x9d666255a92399881795e6e175f7031ca40201151318848b30938534404f,0x8979676957d89a375665e6e182470848d0024054d42c31c630939128404f,0x59d66355c5df69e6219606e49e29832944021051cb18948d20c00f4ce051,0x81e6e356686269d9d795666461f70630940238f20b0d44931ca005344051,0x8e195671589e69f9dd6606e461798949310240f2c734328620c00550e051,0x9269637d86955e77216606d67a274c4cb4050024943491c620310f28e051,0x6266d75a469c8e756165d95f89e8133081110022540d21ca2cd40f18e045,0x56796359c6a45e66216626df76078334b4440804944c91ca20c14e18f050,0x7e465599d61a8579d69636e279c80c28608e1401d25034cb2483c4351050,0x9266567a769c89855d9606e37d784c50710f0022931832cd20940548e051,0x91c9638a76958589976d666075f78a34b40f0024894d42031c6385304051,0x89a65e5df55c7639a49676e18166081c610540228b50c48d0c93914c004f,0x85c9628e099591d69765e6e761f58935341138248a2c85063030051c404f,0x8a46d571e9da5e162096365f76658a3030843c021224634b50714e4d1050,0x9dc6e27d869576499665e9618235cd2484050020ca3131c62d239150404f,0x62165771a9de5648a095d6df8d69891d410200f19228834b0cc4114ce045,0x9176e355a61f9a775e6569608627122094020053140cb1874cd38f284051,0x8179666a459c9e379f65d6e18956084930804443542cc1ca0c93d018504e,0x5e095869c5a455e8e165d6df8a79883530021114862c91ca0cc40f50e045,0x71f6da9de5d885676365596682488d30800f1052470cb506493391290042,0x59f96469c5d899e7626e36608675473520021054cc2ca20950638f0d0051,0x8de6646958a799f8576d696075870b18a00240f50c1d22034cd385244051,0x8229646a686771d79f6636d65d85484d200238f34a2cc1d4243105190051,0x7626d89208675a679595f65771a8ca20901138f0d330648d1d41022d0045,0x8e76df5d69187206a196265599d7940cc14444024d20749328608e2cf050,0x8156e461d99a5e17229636567a77c60cc00538221224a4cb50710f350051,0x5956649de71a85799f9636e075888318a00f1021d250c34b2483854d0051,0x7e19586958a77237a06dd6575a498749300240f3492c620329411130e045,0x81f6649e17587a65d56e395671a88d1ca00f38518c5120c92d3102210051,0x5a26e46177a775c85566396099a7d320c00510f0ca2521942cd3821d0051,0x5e265869c7a799686395f6dd82454828600210f5131c92cd303391490045,0x85566792099a59d71f6e295e5d88d21940113821c328d3084cb10525004f,0x9e695e5d869c7e45606e16628d67544cb10500234c4862091ca4110ce04f,0x7a696791671a8d755d6616e27d880c4cd0111022d448328724840518e04f,0x8dc96461f55a76299e6566e08675c93520054022ca4cc1870c838f504051,0x79596761771a7569a36e26618247c648d0051022c34d424828739131004f,0x7e76e381d62499769e66295571684d0c944e14031420b18a4d20841cf050,0x8a665e5a355c91f69d6e196761781350611140228c1cb0c948d00520e04f,0x8a66e761f55a5e372066195e5a475330300540221424d18748b11128e04f,0x5e66d89de71a89656095d65f8e485430900f1022130c634b28741148e045,0x7559589e199a7a072365f6d75a488349300f3822c6349507308111290045,0x9e66e28e469559871d96165e5df8143084110020d324a2d21c610534e04f,0x62665f8a76957a47206dd9575a385350740f00218c28d2032d211124e045,0x91c6e07586a67e755e9566638a15ca24838500230d0c62d31d440f484051,0x89c6e792355a81f99795e66175858a24301140220d31448b1873854c404f,0x7de6639185d669d7219626d59a09cc1944401441cb28949320308e34f050,0x7a66627d77156166a09616e792374c50a4051021931c83522430112ce04f,0x5a16e469c7a755789d9606637d898724c00210f0d220a2cd1944054ce051,0x8176646a67585617de9566e38a770850a0023851921cc2d30c940f344051,0x8dd6e46957d87225e16609567a798b0cc00240524a2121c635310f50e051,0x8de6d56a459c6205e166295f7669cb3030804442462121ca4cd14e50f050,0x5606df61a99d9dc85696366279790620c14008e0cd2474cb50a3c4491050,0x5566629da71e6265e09636df7619031ca3c008419350834b24c14e491050,0x9226d671a9de99885f96366075754a20310200f31324734b506385490051,0x91f66099a61d7275e29636d67a154c1c638200528d5084cb24310f490051,0x9229607589e15da7956e36567267ca4cd38500f4882c60c9507102310051,0x91f9567a761785a7556636e099c88c35310f0054872c3194248382290051,0x9156e08676a679871f6639565dd8920c838f00230624d1d42d3105290051,0x9156565d869c7679a26e396085e7d21871050022835132092cd38f310051,0x9df6e182461d59a5d566295e7268cd3093910050c721218a4cb10251004f,0x9e36de5d891675a81596266199c7d424c1050110cb20649328738235004f,0x8e195f62481d69699e6626d57179c948d14044e2c74cc18a20308450f050,0x9e396199a92071859f6e265e5dd5542d23820113494c73082861050d004f,0x79d66769c5d85567e06e19628e498b2940021051831cd20949341130e04f,0x9e06de71a9165588dd6619627d798d20c1020110c624b28749340550e04f,0x9df65e71a6179a47636e296181654d1c610200550c28b2484d23910d004f,0x7a096255c5a369791d6e166761f9863534021112c848a0c91d400530e04f,0x9dd96255a61f7245e06616de5a39832d340200534a48818724c11150e04f,0x8a06676958e471f59d9616de5d898819400241128d1c32d224c1054ce04f,0x89d6de7157d76a362096166791698a0cc10240520b2463521d40114ce04f,0x79f96199c5dd6966236626e792054c3523821052c74c950a20301119004f,0x86365e72681669d91f9626e76175495061023911cb28c35320300549004f,0x85f6e76a67587205e396265e5a454730300238524d2142d328611149004f,0x86396761d8245e65956626de71a7c92cd0053914944c318a20c1021d004f,0x8556de5dd99c6206a36629679167d20cc10538224620b50a4cd0111d004f,0x7956e181672691769f96266761d8c60c93911023122073532940052d004f,0x9d56617586a65e47239626de5a07c31873850025122892d320c11135004f,0x79f6679165d881c7559626e199a8cc1d401110518d2834932093822d004f,0x9d595e5a469c81899f6626e17578c348b1110023464cc1ca20938551004f,0x7a36e769c5a499781f66296175854b24300211131420d1ca4d238519004f]
def gens : Array Nat := #[0x1,0x2,0x3,0x4,0x5,0x6]
def action (k : K) (v : V) : V := Fin.ofNat 40 ((((maps[k.val]?).getD 0) >>> (6*v.val)) % 64)
def generator (j : J) : V → V := action (Fin.ofNat 576 ((gens[j.val]?).getD 0))
theorem genInj : ∀ j : J, ∀ u v : V, generator j u = generator j v → u=v := by decide +kernel
theorem genSide : ∀ j : J, ∀ v : V, left (generator j v) ↔ left v := by decide +kernel
theorem genAdj : ∀ j : J, ∀ u v : V, G (generator j u) (generator j v) ↔ G u v := by decide +kernel
theorem genValid (j : J) : Valid (generator j) :=
  ⟨fun _ _ h => genInj j _ _ h,genSide j,genAdj j⟩

def walk : List J → (V → V)
  | [] => id
  | j::js => generator j ∘ walk js
theorem walkValid (w : List J) : Valid (walk w) := by
  induction w with
  | nil => exact validId
  | cons j js ih => exact validComp ih (genValid j)
def words : Array (List J) := #[[],[0],[1],[2],[3],[4],[5],[1,0],[2,0],[3,0],[4,0],[5,0],[0,1],[1,1],[2,1],[3,1],[4,1],[5,1],[0,2],[2,2],[3,2],[4,2],[5,2],[0,3],[1,3],[2,3],[4,3],[5,3],[0,4],[1,4],[2,4],[5,4],[1,5],[2,1,0],[3,1,0],[4,1,0],[5,1,0],[3,2,0],[4,2,0],[5,2,0],[0,3,0],[1,3,0],[2,3,0],[4,3,0],[5,3,0],[0,4,0],[1,4,0],[2,4,0],[5,4,0],[1,5,0],[2,0,1],[3,0,1],[5,0,1],[2,1,1],[3,1,1],[5,1,1],[0,2,1],[2,2,1],[3,2,1],[4,2,1],[5,2,1],[0,3,1],[1,3,1],[2,3,1],[4,3,1],[5,3,1],[0,4,1],[2,4,1],[5,4,1],[1,0,2],[3,0,2],[4,0,2],[5,0,2],[3,2,2],[4,2,2],[5,2,2],[0,3,2],[1,3,2],[4,3,2],[5,3,2],[0,4,2],[1,4,2],[2,4,2],[5,4,2],[1,5,2],[1,0,3],[2,0,3],[4,0,3],[5,0,3],[0,1,3],[1,1,3],[2,1,3],[3,1,3],[4,1,3],[5,1,3],[2,2,3],[4,2,3],[5,2,3],[0,4,3],[1,4,3],[2,4,3],[5,4,3],[1,5,3],[2,0,4],[3,0,4],[5,0,4],[0,1,4],[2,1,4],[3,1,4],[5,1,4],[2,2,4],[3,2,4],[5,2,4],[1,5,4],[0,1,5],[1,1,5],[3,1,5],[4,1,5],[0,2,1,0],[4,2,1,0],[5,2,1,0],[4,3,1,0],[5,3,1,0],[0,4,1,0],[2,4,1,0],[5,4,1,0],[4,3,2,0],[5,3,2,0],[1,4,2,0],[5,4,2,0],[1,5,2,0],[1,0,3,0],[2,0,3,0],[4,0,3,0],[5,0,3,0],[1,1,3,0],[2,1,3,0],[4,1,3,0],[5,1,3,0],[2,2,3,0],[4,2,3,0],[5,2,3,0],[0,4,3,0],[1,4,3,0],[2,4,3,0],[5,4,3,0],[1,5,3,0],[2,0,4,0],[3,0,4,0],[5,0,4,0],[0,1,4,0],[2,1,4,0],[3,1,4,0],[5,1,4,0],[2,2,4,0],[3,2,4,0],[5,2,4,0],[1,5,4,0],[3,1,5,0],[4,1,5,0],[3,2,0,1],[0,3,0,1],[1,3,0,1],[2,3,0,1],[5,3,0,1],[3,2,1,1],[0,3,1,1],[1,3,1,1],[2,3,1,1],[5,3,1,1],[3,0,2,1],[4,0,2,1],[3,2,2,1],[4,2,2,1],[4,3,2,1],[5,3,2,1],[0,4,2,1],[2,4,2,1],[5,4,2,1],[1,0,3,1],[2,0,3,1],[4,0,3,1],[5,0,3,1],[1,1,3,1],[2,1,3,1],[4,1,3,1],[5,1,3,1],[2,2,3,1],[4,2,3,1],[5,2,3,1],[0,4,3,1],[1,4,3,1],[2,4,3,1],[5,4,3,1],[1,5,3,1],[2,0,4,1],[3,0,4,1],[5,0,4,1],[2,2,4,1],[3,2,4,1],[1,5,4,1],[3,1,0,2],[4,1,0,2],[4,3,0,2],[5,3,0,2],[5,4,0,2],[4,3,2,2],[5,3,2,2],[1,4,2,2],[5,4,2,2],[2,0,3,2],[4,0,3,2],[5,0,3,2],[4,1,3,2],[5,1,3,2],[0,4,3,2],[1,4,3,2],[2,4,3,2],[5,4,3,2],[2,0,4,2],[3,0,4,2],[5,0,4,2],[0,1,4,2],[2,1,4,2],[3,1,4,2],[2,2,4,2],[3,2,4,2],[5,2,4,2],[1,5,4,2],[3,1,5,2],[4,1,0,3],[5,1,0,3],[4,2,0,3],[5,2,0,3],[0,4,0,3],[1,4,0,3],[2,4,0,3],[5,4,0,3],[1,5,0,3],[5,0,1,3],[5,1,1,3],[0,2,1,3],[4,2,1,3],[5,2,1,3],[0,3,1,3],[4,3,1,3],[5,3,1,3],[0,4,1,3],[2,4,1,3],[5,4,1,3],[4,2,2,3],[5,2,2,3],[0,4,2,3],[1,4,2,3],[2,4,2,3],[5,4,2,3],[1,5,2,3],[2,0,4,3],[3,0,4,3],[5,0,4,3],[0,1,4,3],[2,1,4,3],[3,1,4,3],[5,1,4,3],[2,2,4,3],[3,2,4,3],[5,2,4,3],[1,5,4,3],[0,1,5,3],[3,1,5,3],[3,2,0,4],[5,2,0,4],[1,3,0,4],[2,3,0,4],[5,3,0,4],[1,5,0,4],[2,0,1,4],[3,0,1,4],[5,0,1,4],[2,2,1,4],[3,2,1,4],[0,3,1,4],[1,3,1,4],[2,3,1,4],[5,3,1,4],[3,2,2,4],[5,2,2,4],[1,3,2,4],[5,3,2,4],[1,5,2,4],[0,1,5,4],[1,1,5,4],[3,1,5,4],[4,1,5,4],[3,0,1,5],[3,1,1,5],[0,3,1,5],[2,3,1,5],[4,3,1,5],[5,4,2,1,0],[0,4,3,1,0],[1,4,3,1,0],[2,4,3,1,0],[5,4,3,1,0],[1,5,3,1,0],[2,0,4,1,0],[3,0,4,1,0],[5,0,4,1,0],[2,2,4,1,0],[3,2,4,1,0],[1,5,4,1,0],[1,4,3,2,0],[5,4,3,2,0],[3,1,4,2,0],[4,1,0,3,0],[5,1,0,3,0],[5,2,0,3,0],[0,4,0,3,0],[2,4,0,3,0],[5,4,0,3,0],[1,5,0,3,0],[5,1,1,3,0],[0,2,1,3,0],[5,2,1,3,0],[0,4,1,3,0],[2,4,1,3,0],[5,4,1,3,0],[4,2,2,3,0],[5,2,2,3,0],[0,4,2,3,0],[1,4,2,3,0],[5,4,2,3,0],[1,5,2,3,0],[2,0,4,3,0],[3,0,4,3,0],[5,0,4,3,0],[0,1,4,3,0],[2,1,4,3,0],[5,1,4,3,0],[2,2,4,3,0],[3,2,4,3,0],[5,2,4,3,0],[1,5,4,3,0],[0,1,5,3,0],[3,1,5,3,0],[5,2,0,4,0],[1,3,0,4,0],[2,3,0,4,0],[5,3,0,4,0],[1,5,0,4,0],[2,0,1,4,0],[3,0,1,4,0],[5,0,1,4,0],[2,2,1,4,0],[3,2,1,4,0],[0,3,1,4,0],[2,3,1,4,0],[5,3,1,4,0],[3,2,2,4,0],[5,2,2,4,0],[1,3,2,4,0],[5,3,2,4,0],[1,5,2,4,0],[1,1,5,4,0],[4,1,5,4,0],[4,3,1,5,0],[4,0,3,0,1],[4,1,3,0,1],[4,2,3,0,1],[4,0,3,1,1],[4,1,3,1,1],[4,2,3,1,1],[4,3,0,2,1],[0,4,3,2,1],[2,4,3,2,1],[5,4,3,2,1],[2,0,4,2,1],[3,0,4,2,1],[2,2,4,2,1],[3,2,4,2,1],[5,1,0,3,1],[5,2,0,3,1],[0,4,0,3,1],[2,4,0,3,1],[5,4,0,3,1],[5,1,1,3,1],[5,2,1,3,1],[0,4,1,3,1],[5,4,1,3,1],[5,2,2,3,1],[0,4,2,3,1],[1,4,2,3,1],[2,4,2,3,1],[5,4,2,3,1],[2,0,4,3,1],[5,0,4,3,1],[0,1,4,3,1],[2,1,4,3,1],[3,1,4,3,1],[5,1,4,3,1],[2,2,4,3,1],[3,2,4,3,1],[5,2,4,3,1],[1,5,4,3,1],[3,1,5,3,1],[5,2,0,4,1],[5,3,0,4,1],[3,2,2,4,1],[1,3,2,4,1],[4,1,5,4,1],[5,4,3,0,2],[1,4,3,2,2],[5,4,3,2,2],[5,2,0,3,2],[0,4,0,3,2],[5,4,0,3,2],[0,4,1,3,2],[2,4,1,3,2],[5,4,1,3,2],[2,0,4,3,2],[3,0,4,3,2],[5,0,4,3,2],[5,1,4,3,2],[2,2,4,3,2],[3,2,4,3,2],[5,2,4,3,2],[1,5,4,3,2],[5,2,0,4,2],[1,3,0,4,2],[5,3,0,4,2],[1,5,0,4,2],[2,0,1,4,2],[3,0,1,4,2],[2,2,1,4,2],[3,2,1,4,2],[0,3,1,4,2],[2,3,1,4,2],[5,2,2,4,2],[1,3,2,4,2],[5,3,2,4,2],[1,5,2,4,2],[1,1,5,4,2],[4,1,5,4,2],[0,4,1,0,3],[2,4,1,0,3],[5,4,1,0,3],[5,4,2,0,3],[1,5,2,0,3],[5,0,4,0,3],[5,1,4,0,3],[5,2,4,0,3],[1,5,4,0,3],[3,1,5,0,3],[0,4,2,1,3],[2,4,2,1,3],[5,4,2,1,3],[5,4,3,1,3],[3,0,4,1,3],[5,0,4,1,3],[1,5,4,1,3],[5,4,2,2,3],[5,0,4,2,3],[5,2,4,2,3],[1,5,4,2,3],[3,1,5,2,3],[5,2,0,4,3],[5,3,0,4,3],[1,5,0,4,3],[5,0,1,4,3],[2,3,1,4,3],[5,3,1,4,3],[5,2,2,4,3],[1,3,2,4,3],[5,3,2,4,3],[1,5,2,4,3],[0,1,5,4,3],[3,1,5,4,3],[3,0,1,5,3],[0,3,1,5,3],[2,3,1,5,3],[5,3,2,0,4],[4,1,3,0,4],[5,1,3,0,4],[5,2,3,0,4],[1,5,3,0,4],[4,1,5,0,4],[5,3,0,1,4],[4,0,3,1,4],[5,0,3,1,4],[5,1,3,1,4],[5,2,3,1,4],[1,5,3,1,4],[4,1,3,2,4],[5,1,3,2,4],[2,3,1,5,4],[4,3,1,5,4],[4,0,3,1,5],[4,2,3,1,5],[0,4,3,1,5],[1,4,3,1,5],[2,4,3,1,5],[5,0,4,3,1,0],[5,1,4,3,1,0],[2,2,4,3,1,0],[3,2,4,3,1,0],[5,2,4,3,1,0],[1,5,4,3,1,0],[5,2,0,4,1,0],[5,3,0,4,1,0],[1,3,2,4,1,0],[4,1,5,4,1,0],[5,1,4,3,2,0],[1,5,4,3,2,0],[0,4,1,0,3,0],[5,4,1,0,3,0],[1,5,2,0,3,0],[5,0,4,0,3,0],[5,2,4,0,3,0],[1,5,4,0,3,0],[3,1,5,0,3,0],[3,0,4,1,3,0],[5,0,4,1,3,0],[1,5,4,1,3,0],[5,4,2,2,3,0],[5,0,4,2,3,0],[1,5,4,2,3,0],[3,1,5,2,3,0],[5,2,0,4,3,0],[5,3,0,4,3,0],[1,5,0,4,3,0],[5,0,1,4,3,0],[5,2,2,4,3,0],[1,3,2,4,3,0],[5,3,2,4,3,0],[1,5,2,4,3,0],[0,1,5,4,3,0],[3,0,1,5,3,0],[5,1,3,0,4,0],[5,2,3,0,4,0],[4,1,5,0,4,0],[5,3,0,1,4,0],[4,1,3,2,4,0],[5,1,3,2,4,0],[0,4,3,1,5,0],[1,4,3,1,5,0],[2,4,3,1,5,0],[2,2,4,3,2,1],[3,2,4,3,2,1],[1,3,2,4,2,1],[5,0,4,0,3,1],[1,5,4,0,3,1],[5,0,4,1,3,1],[1,5,4,1,3,1],[5,0,4,2,3,1],[1,5,4,2,3,1],[5,2,0,4,3,1],[5,2,2,4,3,1],[4,1,3,2,4,1],[5,2,0,4,3,2],[5,3,0,4,3,2],[1,5,0,4,3,2],[5,2,2,4,3,2],[5,3,2,4,3,2],[1,5,2,4,3,2],[5,1,3,0,4,2],[5,1,3,2,4,2],[1,5,0,4,0,3],[1,1,5,4,0,3],[4,1,5,4,0,3],[5,3,0,4,1,3],[1,5,0,4,2,3],[1,1,5,4,2,3],[4,1,5,4,2,3],[5,1,3,2,4,3],[5,4,1,3,0,4],[5,4,1,3,2,4]]
def word (k : K) := (words[k.val]?).getD []
def composeK (b : Fin 24) (i : Fin 24) : K := ⟨24*b.val+i.val,by omega⟩
theorem eqw0 : ∀ j : Fin 24, ∀ v : V, action (composeK 0 j) v = walk (word (composeK 0 j)) v := by decide +kernel
theorem eqw1 : ∀ j : Fin 24, ∀ v : V, action (composeK 1 j) v = walk (word (composeK 1 j)) v := by decide +kernel
theorem eqw2 : ∀ j : Fin 24, ∀ v : V, action (composeK 2 j) v = walk (word (composeK 2 j)) v := by decide +kernel
theorem eqw3 : ∀ j : Fin 24, ∀ v : V, action (composeK 3 j) v = walk (word (composeK 3 j)) v := by decide +kernel
theorem eqw4 : ∀ j : Fin 24, ∀ v : V, action (composeK 4 j) v = walk (word (composeK 4 j)) v := by decide +kernel
theorem eqw5 : ∀ j : Fin 24, ∀ v : V, action (composeK 5 j) v = walk (word (composeK 5 j)) v := by decide +kernel
theorem eqw6 : ∀ j : Fin 24, ∀ v : V, action (composeK 6 j) v = walk (word (composeK 6 j)) v := by decide +kernel
theorem eqw7 : ∀ j : Fin 24, ∀ v : V, action (composeK 7 j) v = walk (word (composeK 7 j)) v := by decide +kernel
theorem eqw8 : ∀ j : Fin 24, ∀ v : V, action (composeK 8 j) v = walk (word (composeK 8 j)) v := by decide +kernel
theorem eqw9 : ∀ j : Fin 24, ∀ v : V, action (composeK 9 j) v = walk (word (composeK 9 j)) v := by decide +kernel
theorem eqw10 : ∀ j : Fin 24, ∀ v : V, action (composeK 10 j) v = walk (word (composeK 10 j)) v := by decide +kernel
theorem eqw11 : ∀ j : Fin 24, ∀ v : V, action (composeK 11 j) v = walk (word (composeK 11 j)) v := by decide +kernel
theorem eqw12 : ∀ j : Fin 24, ∀ v : V, action (composeK 12 j) v = walk (word (composeK 12 j)) v := by decide +kernel
theorem eqw13 : ∀ j : Fin 24, ∀ v : V, action (composeK 13 j) v = walk (word (composeK 13 j)) v := by decide +kernel
theorem eqw14 : ∀ j : Fin 24, ∀ v : V, action (composeK 14 j) v = walk (word (composeK 14 j)) v := by decide +kernel
theorem eqw15 : ∀ j : Fin 24, ∀ v : V, action (composeK 15 j) v = walk (word (composeK 15 j)) v := by decide +kernel
theorem eqw16 : ∀ j : Fin 24, ∀ v : V, action (composeK 16 j) v = walk (word (composeK 16 j)) v := by decide +kernel
theorem eqw17 : ∀ j : Fin 24, ∀ v : V, action (composeK 17 j) v = walk (word (composeK 17 j)) v := by decide +kernel
theorem eqw18 : ∀ j : Fin 24, ∀ v : V, action (composeK 18 j) v = walk (word (composeK 18 j)) v := by decide +kernel
theorem eqw19 : ∀ j : Fin 24, ∀ v : V, action (composeK 19 j) v = walk (word (composeK 19 j)) v := by decide +kernel
theorem eqw20 : ∀ j : Fin 24, ∀ v : V, action (composeK 20 j) v = walk (word (composeK 20 j)) v := by decide +kernel
theorem eqw21 : ∀ j : Fin 24, ∀ v : V, action (composeK 21 j) v = walk (word (composeK 21 j)) v := by decide +kernel
theorem eqw22 : ∀ j : Fin 24, ∀ v : V, action (composeK 22 j) v = walk (word (composeK 22 j)) v := by decide +kernel
theorem eqw23 : ∀ j : Fin 24, ∀ v : V, action (composeK 23 j) v = walk (word (composeK 23 j)) v := by decide +kernel
theorem okPair (b i : Fin 24) (v : V) : action (composeK b i) v = walk (word (composeK b i)) v := by
  fin_cases b <;> first
    | exact eqw0 i v
    | exact eqw1 i v
    | exact eqw2 i v
    | exact eqw3 i v
    | exact eqw4 i v
    | exact eqw5 i v
    | exact eqw6 i v
    | exact eqw7 i v
    | exact eqw8 i v
    | exact eqw9 i v
    | exact eqw10 i v
    | exact eqw11 i v
    | exact eqw12 i v
    | exact eqw13 i v
    | exact eqw14 i v
    | exact eqw15 i v
    | exact eqw16 i v
    | exact eqw17 i v
    | exact eqw18 i v
    | exact eqw19 i v
    | exact eqw20 i v
    | exact eqw21 i v
    | exact eqw22 i v
    | exact eqw23 i v
theorem okWord (k : K) : action k = walk (word k) := by
  let b : Fin 24 := ⟨k.val / 24,by omega⟩
  let i : Fin 24 := ⟨k.val % 24,by omega⟩
  have hk : composeK b i = k := Fin.ext (by dsimp [composeK,b,i]; omega)
  funext v
  exact hk ▸ okPair b i v
theorem actionValid (k : K) : Valid (action k) := by rw [okWord k]; exact walkValid (word k)
noncomputable def perm (k : K) : V ≃ V :=
  Equiv.ofBijective (action k) ⟨(actionValid k).inj,Finite.injective_iff_surjective.mp (actionValid k).inj⟩
def zoneData : Array Nat := #[0x1fffff,0x3affb3,0x70ff23,0xc1fe47,0xe0fe03,0x170fd02,0x1c1fc06,0x1e0fc02,0x20ffb3d,0x22afb31,0x260fb21,0x2c1fa05,0x2e0fa01,0x322f910,0x360f900,0x3a2f800,0x3c1f804,0x3e0f800,0x4e0f602,0x5a2f402,0x6e0f200,0x722f010,0x7a2f000,0x7c1f000,0xa0fe835,0xa2ae831,0xa60e821,0xaaae801,0xac1e805,0xae0e801,0xf22e010,0xfa2e000,0x10c1d843,0x10e0d803,0x11e0d802,0x12c1d801,0x12e0d801,0x13e0d800,0x1583d00a,0x15a2d002,0x1ac1c801,0x2070b303,0x20e0b203,0x2170b102,0x21a2b082,0x2260b301,0x22e0b201,0x24aab202,0x24e0b202,0x2570b002,0x25a2b002,0x26aab200,0x26e0b200,0x27a2b000,0x2870a001,0x2eaaa000,0x35a29002,0x44e06602,0x45a26402,0x4da26400,0x4eaa6000,0x50c14003,0x6e0f2000,0x8570c402,0x95a2c002,0x9aaac801,0x9ae0c801,0xbeaa8000,0xc5704402,0xf1540102,0x111e09802,0x113e09800,0x135559002,0x135709002,0x135c19002,0x137459000,0x141300482,0x17d550000,0x19aa88801,0x1b0708003,0x1c41c060a,0x1c4380602,0x1c4700602,0x1c60c0208,0x1cd540400,0x26eaa2000,0x2faaa0001,0x3c5700402,0x44fa26000,0x535541002,0x5f5540002,0x5fd540000,0x6f5320002,0x86e0c2000,0xbfaa80001,0xcd0e04003,0xfe0c00007,0x17f5700002,0x1a6ea82000,0x200a03c035,0x200a22c031,0x200ac1c005,0x201ac1c001,0x201f83c000,0x205ac14001,0x209fa2c000,0x2cdae04001,0x2feac00005,0x37fd700000,0x4ff0e00003,0x6ffae00001,0xdff5e00002,0xffffe00000]
def TData : Array Nat := #[0x143200000,0x143000000,0x8028000000,0x50000000,0x3200000000,0x142000000,0x6400000000,0x20000000,0x141200000,0x141000000,0x141000000,0x284000000,0x40000000,0x140000040,0x140000040,0x140000040,0x40000000,0x40000040,0x8000000,0x100000000,0x200000080,0x140000040,0x100000040,0x80000080,0x141200000,0x141000000,0x8020000008,0x100000000,0x4000000,0x8000000008,0x100000040,0x100000140,0x40000010,0x40000010,0x40000010,0x40000010,0x40000010,0x40000050,0x8000000,0x4,0x10,0x8008000008,0x8008000008,0x8008000008,0x80000020,0x8008000008,0x8000000008,0x8000000,0x8000008,0x8000000008,0x20,0x0,0x8,0x20,0x8000000008,0x8,0x24,0x10000010,0x100000040,0x100000140,0x100000140,0x10,0x2000000800,0x2000080,0x24,0x0,0x8,0x24,0x20000c0,0x800030,0x40000050,0x40000050,0x0,0x4,0x10,0x40,0x2000040,0x48,0x40,0x8000002008,0x2000000,0x2000040,0x20000c0,0x40,0xc0,0x88,0x98,0x20000c0,0x100000140,0x100,0x130,0x130,0x4c0,0x2000000800,0x260,0x10010,0x980,0x4c0,0x40800,0x2,0x2,0x2,0x12,0x2,0x12,0x26,0x10012,0x980,0x4c0,0x14010,0x984,0x1308,0x985]
def UData : Array Nat := #[0x0,0x200000,0x600000,0xc14003,0xe00000,0x1600000,0x1c00000,0x1e0b002,0x2000000,0x2200000,0x2600000,0x2c00000,0x2e06201,0x0,0x400000,0x800000,0x3c16004,0xc06000,0x4e0e400,0x5a09402,0xa03000,0x4000000,0x4809000,0x180c000,0xa000000,0xa200000,0x2000000,0xaa88801,0xac1e000,0x2804800,0xc008010,0x8000,0x14003,0x204003,0x1204002,0x2014001,0x2204001,0x4000,0x1583c000,0x182d002,0xa01c801,0x0,0x800000,0x1000000,0x228002,0x2000000,0x2801200,0x24aaa000,0x480a000,0x5001002,0x422b002,0x26aab200,0x680b200,0x622b000,0x0,0x68aa000,0x29002,0x4204002,0x4800402,0x400,0x80000,0x14003,0xa030000,0x120c000,0x2c002,0x0,0x9280c801,0xa0a8000,0x4000,0x2,0x2,0x0,0x0,0x121509002,0x125019002,0x34459000,0x0,0x14150000,0x98888801,0x2,0x1c40c0208,0x84080200,0x200,0x840c0208,0x8140400,0x408a2000,0xa0001,0x0,0x0,0x31541002,0x140002,0x140000,0x120002,0xa000000,0x80001,0x4003,0x7,0x100002,0xa082000,0x3c035,0x22c031,0xc1c005,0x1c001,0x1583c000,0x14001,0x2c000,0x4001,0x5,0x2008100000,0x3,0x1,0x2,0x0]
def modeData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def uData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def aData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x19,0x0,0x0,0x0,0x0,0x0,0x0,0x18,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def bData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1b,0x0,0x0,0x0,0x0,0x0,0x0,0x1a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def cData : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x25,0x0,0x0,0x0,0x0,0x0,0x0,0x24,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def switches : Array Nat := #[0x47f,0x3d2,0x42a,0x2ca,0x1377,0x443,0x1421,0x44d,0x457,0x419,0x45f,0x459,0x456,0x461,0x473,0x2f6,0x142f,0x44a,0x397,0x47f,0x6b1,0x6b8,0x686,0x1678,0x8d2,0x167f,0x8dc,0x5bf,0x68e,0x8bd,0x622,0x6bf,0x7f5,0x848,0x6a5,0x164e,0x856,0x684,0x6b1,0x6b1,0x996,0xd46,0x1792,0xae5,0x1f7f,0xf9c,0x5e71,0x92d,0xa50,0xb31,0xd7f,0x98e,0xf7b,0xb25,0x18b1,0xa12,0x5d2d,0x996,0x83e,0x83e,0xf86,0x1a46,0x9e1,0x1a3e,0x49ac,0xfb4,0x49ec,0xf8f,0xfb7,0xa7e,0xa86,0xf95,0xf74,0x1a63,0x9b0,0xaa3,0x996,0x996,0x996,0x11c6,0x1b96,0x2a60,0x23c6,0x4ad6,0x60ae,0x653f,0x2cf7,0x11f7,0x62ff,0x6bad,0x2cc6,0x60a5,0x23f7,0x2a16,0x6280,0xd46,0xd46,0x11c6,0xd46,0x206d,0x1025,0x2186,0x1069,0x60e8,0x62c6,0x1031,0x6258,0xb558,0x6131,0xffc,0x10ad,0x2029,0x616e,0x61ad,0x11c6,0xf86,0xf86,0xf86,0x2555,0x2b25,0x2606,0x4bb9,0x4bd2,0x4c6d,0x4bcf,0x2c32,0x1115,0x5fa4,0x2bc6,0x5787,0x311b,0x60a9,0x2c9b,0x11c6,0x11c6,0x11c6,0x11c6,0x2640,0xa405,0x2846,0x4df9,0xa4a3,0xa628,0x4e86,0x6f59,0xb798,0x6d24,0xa405,0x8e69,0xaac5,0x6cb0,0x6ea5,0x1678,0x15d2,0x162d,0x14ca,0x1377,0x1583,0x37ad,0x1647,0x1657,0x1619,0x165f,0x1659,0x165c,0x15b7,0x15e6,0x14f6,0x3777,0x1649,0x14df,0x1678,0x1792,0x18b8,0x1f10,0x1678,0x1951,0x3a46,0x1adc,0x1711,0x1f65,0x1abd,0x1f78,0x189c,0x194e,0x197e,0x18a5,0x3a78,0x19d2,0x1884,0x1792,0x1792,0x1b96,0x206d,0x1792,0x21fa,0x3b92,0x261c,0x676e,0x23e5,0x22e5,0x2256,0x219c,0x1b8e,0x243c,0x1d25,0x3ee5,0x1c12,0x662d,0x1b96,0x1a46,0x1a46,0x2555,0x1a46,0x2303,0x3fd2,0x4ffe,0x2543,0x50ac,0x3065,0x250c,0x2315,0x1c86,0x312d,0x25cd,0x40e1,0x238d,0x22cc,0x1b96,0x1b96,0x1b96,0x2640,0x1b96,0x2ee0,0x4140,0x5196,0x69ae,0x7965,0x32a5,0x26d6,0x76ed,0x74ad,0x3360,0x69a5,0x41d6,0x2e25,0x7603,0x1f10,0x206d,0x21c0,0x1f10,0x1f10,0x2f7c,0x3c86,0x2339,0x21cc,0x7b8e,0x3110,0x7b22,0x2150,0x21e7,0x21fc,0x22ad,0x3b29,0x22a2,0x2390,0x206d,0x206d,0x2640,0x206d,0x206d,0xa9c7,0xb10f,0x27b9,0x7517,0xa1e5,0xa9e4,0xa0fe,0xbc99,0x7624,0x267c,0x272d,0xb1a5,0x753b,0x751b,0x21c0,0x2640,0x21c0,0x21c0,0x21c0,0x3180,0x4346,0x33db,0x774c,0xc82e,0x9686,0xa0fe,0x75a1,0x2e24,0xa9c7,0xb10f,0x9529,0x7c11,0xa9f8,0x2640,0x2555,0x2555,0x2555,0x2555,0x34c6,0x9423,0x5279,0x5292,0x96ad,0x960f,0x3515,0x2795,0x68a4,0x3286,0x9423,0x455b,0xb163,0x328c,0x2640,0x2640,0x2640,0x2640,0x2640,0xa9c7,0xb10f,0x54b9,0xaf28,0xd51e,0xc3ae,0xa0fe,0xbf3c,0x7624,0xa9c7,0xb10f,0xc370,0xbf91,0xae1e,0x2a60,0x2a60,0x2a60,0xa405,0x2ee0,0x2a60,0xa972,0xa885,0x6c00,0x81ba,0x83a5,0x6ce1,0xca45,0x6de0,0xa405,0x83d8,0x2d65,0x8198,0x6c65,0x2b65,0xa405,0x2b65,0x2b65,0x3180,0x2b65,0x3225,0x57c5,0x708c,0x841a,0x58a0,0xa57e,0x6e73,0x83ab,0xa405,0xa787,0x3425,0x7125,0x4d60,0x2ee0,0x2ee0,0x2ee0,0xa9c7,0x2ee0,0x2ee0,0xc322,0xc370,0x7500,0xaee1,0xc758,0xc0ba,0xcef9,0x76e0,0xa9c7,0x8618,0x8858,0xadd2,0xc098,0x2f7c,0xa9c7,0x3180,0x2f7c,0x2f7c,0x2f7c,0x43a7,0x9529,0x318c,0xc82e,0xe8ea,0xc838,0xaa7e,0x31a7,0x31bc,0x954e,0x43bc,0x9511,0x94a3,0x3180,0xa9c7,0x3180,0x3180,0x3180,0x3180,0x4665,0x9529,0x774c,0xc82e,0xed20,0xd570,0xaf35,0x85eb,0xa9c7,0xc322,0x9529,0x9711,0xc2f7,0xa9c7,0x34c6,0x34c6,0x34c6,0x34c6,0x34c6,0x957a,0x95f9,0x5483,0x98a3,0xf2fe,0xc399,0xa115,0xae59,0xa9c7,0x957a,0x95f9,0xc31f,0x9818,0x3a46,0x39cf,0x3a2a,0x390f,0x37ad,0x397c,0x37ad,0x3a79,0x3a51,0x3a19,0x39ed,0x3a3a,0x3995,0x3a31,0x3a73,0x388f,0xe0e1,0x3a58,0x38d2,0x3a46,0x3b92,0x3ec6,0x3c86,0x3a46,0x4112,0x3a46,0x4069,0x3b11,0x3b9c,0x3f6f,0x3c22,0x3ec4,0x4035,0x3f25,0x3e62,0xe33f,0x4099,0x3c84,0x3b92,0x3b92,0x4140,0xb10f,0x3b92,0x95fc,0x3b92,0x4493,0xc806,0x950e,0x9645,0x9592,0xb1b6,0x41ce,0x4586,0x422d,0xe96d,0x4252,0xc74b,0x3ec6,0x4140,0x3ec6,0x4346,0x3ec6,0x4320,0x3ec6,0x93ed,0x436e,0x41bb,0x93ed,0xb1ae,0x8d7a,0x423e,0x41e5,0x8c12,0xe9af,0x42d9,0xb186,0x4140,0x3fd2,0x3fd2,0x9423,0x3fd2,0x957a,0x3fd2,0x5bac,0x448b,0x5c2d,0x4483,0x456a,0x41f7,0x4212,0x4560,0x9423,0xe4be,0x4185,0x9505,0x4140,0x4140,0x4140,0xb10f,0x4140,0xc322,0x4140,0x9645,0xc806,0x989a,0x9645,0xc32a,0xc12a,0x7da0,0x47c6,0xb10f,0xeded,0x88e0,0xd4cd,0x43a7,0xc322,0x4665,0x43a7,0x43a7,0x43a7,0x43a7,0xed20,0x9511,0xc82e,0xe8ea,0xf2a2,0xc371,0x46eb,0x954e,0x954e,0xe8ea,0x9511,0xedc0,0x4665,0xc322,0x4665,0x4665,0x4665,0x4665,0x4665,0xed20,0x9711,0xc82e,0xed20,0xf9b3,0xd571,0xc82e,0xc322,0xc322,0xed20,0x9711,0xf2ca,0x4ad6,0x49ac,0x49ac,0x4bb9,0x4ffe,0x4b21,0x506c,0x49ac,0x4bf4,0x8b2c,0x4c05,0x4b7e,0x651c,0x6534,0x4ad0,0x4bec,0x5074,0x4af0,0x6392,0x4ad6,0x4ad6,0x4ad6,0x4df9,0x5196,0xa885,0x9645,0x4ad6,0xa895,0xd711,0x58e5,0x4dbe,0xa5d6,0x71a4,0x59a0,0xa7c0,0x9516,0xa89c,0xa4a5,0x4df9,0x4df9,0x4df9,0x4df9,0x54b9,0xa885,0xc3ae,0x4df9,0xd101,0xf691,0xa7c0,0x9ebe,0xcc8a,0xa4a5,0xa885,0xa7c0,0xc370,0xcfe0,0xa4a5,0x5196,0x4ffe,0x4ffe,0x5279,0x4ffe,0x95f9,0x5bac,0x4ffe,0x9634,0xebec,0x9645,0x523e,0x795c,0x7864,0x9516,0x962c,0x5b79,0x95be,0x784c,0x5196,0x5196,0x5196,0x54b9,0x5196,0xc370,0x9645,0x5196,0xc3a5,0xefd1,0x9645,0x547e,0xaef1,0x7864,0x9516,0xc3ae,0x9516,0xc32a,0xae1e,0x54b9,0x54b9,0x54b9,0x54b9,0x54b9,0xc370,0xc3ae,0x54b9,0xd570,0xf8d1,0xc3ae,0xa0fe,0xceca,0xae1e,0xc370,0xc3ae,0xc370,0xd52a,0xae1e,0x57c5,0x5825,0x571a,0x571a,0x9398,0x571a,0xe95a,0x571a,0x57da,0x595a,0x588b,0x8f9d,0x8f7f,0x8eb9,0x8eb0,0x588c,0x9398,0x5807,0x57db,0x57c5,0xa885,0x57c5,0x57c5,0x9529,0x57c5,0xed20,0x57c5,0x7e1a,0xda0a,0x90e0,0xd101,0xd07b,0xa7b8,0xa885,0xda3e,0x9529,0xd7f8,0xa7b8,0x9645,0x5bac,0x5bac,0x962c,0x5bac,0xed98,0x5bac,0x5bac,0xee4f,0xebec,0x9645,0x95be,0x98fe,0x98f9,0xeded,0x962c,0xe72c,0x95be,0x97b6,0x5e71,0x5e71,0x60ae,0x60e8,0x676e,0x60c9,0x7bb1,0x5fdc,0x5e71,0x62ee,0x6052,0x60b1,0x62f1,0x62d0,0x6090,0x60d7,0x6771,0x5f92,0xad3f,0x60ae,0x60ae,0x60ae,0xa4a3,0x69ae,0x6c00,0xc806,0xa895,0x60ae,0xa612,0xa859,0x8f56,0xa67f,0x6e2e,0x8486,0xa46e,0xb199,0x838b,0xc516,0x60e8,0x60e8,0xa4a3,0x60e8,0x7517,0x6e44,0xa06e,0x6c04,0x60e8,0xc98b,0xa52b,0xa45d,0xb836,0xca40,0x6c17,0x6e68,0x7504,0xa4ee,0xc5ff,0x632e,0xa4a3,0x632e,0x632e,0x774c,0x708c,0x776e,0x70ea,0x632e,0xa572,0xd7f8,0xa594,0xa528,0x81c0,0x8278,0xa4d8,0x77aa,0x70ae,0xa45a,0x676e,0x676e,0x69ae,0x7517,0x676e,0x7500,0xc806,0xb170,0x676e,0x7612,0xb13a,0xb199,0x7710,0x772e,0x6990,0x7509,0x8d6b,0x6892,0xd298,0x69ae,0x69ae,0x69ae,0xaf28,0x69ae,0x7500,0xc806,0xc3a5,0x69ae,0xaef0,0xc3a6,0xb199,0xaf37,0x772e,0x86c6,0xadd2,0xb199,0x85cb,0xde97,0x6b3a,0x6c00,0x6b3a,0x708c,0x743a,0x6b3a,0x7c9b,0x7184,0x6b3a,0x6d7a,0x71fa,0x6cdb,0x6c0c,0x6cfe,0x6d04,0x6c98,0x7d3a,0x7118,0x6c1a,0x6c00,0x6c00,0x6c00,0xa4a3,0x7500,0x6c00,0xd4b8,0xd101,0x6c00,0xcb12,0xd0bb,0x9a56,0xccb9,0xba16,0xa4a3,0xa46e,0xc0ba,0xa46e,0xc516,0x6e44,0x6e44,0xa4a3,0x6e44,0xaf28,0x6e44,0xa06e,0xa45d,0x6e44,0xcbcb,0xcfe2,0xa45d,0xca40,0xca40,0xa4a3,0x9e2e,0xaf2b,0xcfdc,0xdc7f,0x708c,0xa4a3,0x708c,0x708c,0x774c,0x708c,0x9711,0x7e1a,0x708c,0xd0a1,0xd7f8,0xd101,0xa528,0xa528,0xa4a3,0xcfdc,0x983a,0x7e98,0xd07b,0x743a,0x7500,0x743a,0x774c,0x743a,0x743a,0x7c9b,0x7844,0x743a,0x767a,0x78ba,0x75db,0x750c,0x75fe,0x7604,0x7598,0x7d3a,0x77d8,0x751a,0x7500,0x7500,0x7500,0xaf28,0x7500,0x7500,0xd4b8,0xd570,0x7500,0xcd52,0xd53a,0xc0ba,0xcef9,0xbefc,0xaf28,0xadd2,0xc0ba,0xadd2,0xde97,0x774c,0xaf28,0x774c,0x774c,0x774c,0x774c,0x9711,0x983a,0x774c,0xd571,0xf0b8,0xd570,0xaf35,0xaf35,0xaf28,0xd4b8,0x983a,0x9711,0xd4f7,0x7bb1,0x7bb1,0xc806,0xa06e,0xc806,0xa06e,0x7bb1,0xc756,0x7bb1,0xa1ff,0xc756,0xc756,0xa1ff,0xa1ff,0xc806,0xa06e,0xc756,0xc806,0xfe21,0x7c9b,0xd4b8,0x7c9b,0x9711,0x7c9b,0x7c9b,0x7c9b,0x97be,0x7c9b,0xc01b,0x97be,0xd575,0xc01b,0xd571,0xc0af,0xc0af,0xf0b8,0x9711,0xd52d,0x7e1a,0xd101,0x7e1a,0x7e1a,0x983a,0x7e1a,0xf0b8,0x7e1a,0x7e1a,0xf761,0xd7f8,0xd101,0xd07b,0xd07b,0xd101,0xf773,0x983a,0xd7f8,0xd07b,0x81ba,0x81ba,0x81ba,0xa628,0xaee1,0x81ba,0xae7e,0xf691,0xcb12,0x81ba,0xa5cf,0xcc9c,0xcc2d,0xa629,0xa628,0xa629,0xaefb,0x9ced,0xa5cf,0x841a,0xa628,0x841a,0x841a,0xc82e,0x841a,0x865a,0xda0a,0xd0a1,0x841a,0xa80f,0xdc78,0xa463,0xb3c5,0xa628,0xd0f0,0xc2bf,0xa463,0xa80f,0x865a,0xae7e,0x865a,0x865a,0xc82e,0x865a,0x865a,0xf2ca,0xd571,0x865a,0xc2bf,0xf538,0xaf3a,0xc82e,0xae7e,0xd51e,0xc2bf,0xaf3a,0xc2bf,0x8899,0xd51e,0x8899,0xc82e,0x8899,0x8899,0x8899,0xc32d,0xc01b,0x8899,0xc32d,0xf520,0xc01b,0xc82e,0xc0d9,0xc0d9,0xf2ca,0xd571,0xc32d,0xd711,0x8b2c,0x8b2c,0xd66e,0xebec,0xd66e,0xebec,0x8b2c,0xd735,0x8b2c,0xd711,0xd735,0xd735,0xd711,0xd711,0xd66e,0xebec,0xd735,0xd66e,0xc01b,0xc119,0xb0d5,0xb198,0x8d0f,0x8d0f,0x8d0f,0xb0cb,0x8d0f,0x8d0f,0xc02b,0xc151,0xb0d5,0xbf8e,0xd2ed,0xc07c,0xf2e1,0xb198,0xb0cb,0x8ead,0x8ead,0xa868,0x8ead,0xf2fe,0x8ead,0xb100,0xa79c,0xcfe2,0x9a79,0x8ead,0x99ed,0xc5dc,0xd04b,0xa868,0xa79c,0xb100,0xd045,0xd0ad,0x90e0,0xda3e,0x90e0,0x90e0,0xed20,0x90e0,0xed20,0x90e0,0xd7f8,0xda0a,0x90e0,0xf773,0xf761,0xda0a,0xda3e,0xda3e,0xed20,0xd7f8,0xda0a,0x93ed,0x9645,0x93ed,0x9686,0x93ed,0x9660,0x93ed,0x93ed,0x96b9,0x94fb,0x93ed,0xb1ae,0xb12d,0x957e,0x94af,0xb12a,0xe9af,0x962d,0xb186,0x9645,0x9645,0x9645,0xc3ae,0x9645,0xf2fe,0x9645,0x9645,0xf17d,0xefd1,0x9645,0xc32a,0xd3b6,0x98f9,0xeded,0xc3ae,0xeded,0xc32a,0xd4cd,0x97be,0xf9b3,0x97be,0xf0b8,0x97be,0x97be,0x97be,0x97be,0x97be,0xd52d,0x97be,0xd575,0xd52d,0xf9a1,0xd575,0xd575,0xf0b8,0xf0b8,0xd52d,0x9a79,0x9a79,0xd0ad,0x9a79,0xf8d1,0x9a79,0xc060,0xd04b,0xdc57,0x9a79,0x9a79,0xc5dc,0xc5dc,0xd04b,0xd0ad,0xd04b,0xc060,0xdc78,0xd0ad,0xcbc0,0x9d74,0xfbe1,0x9d74,0xcef4,0xcc8f,0xcecf,0x9d74,0x9d74,0x9d74,0x9d74,0xcc8f,0xcbc0,0xcc8f,0xccb4,0xcbc0,0xce00,0xccb4,0xccb4,0x9ebe,0x9ebe,0x9ebe,0x9ebe,0xa0fe,0xd101,0xd52a,0x9ebe,0xd101,0xfbe1,0xcfe0,0x9ebe,0xcc8a,0xcc8a,0xd101,0xcfe0,0xd570,0xcfe0,0xcc8a,0xa0fe,0xa0fe,0xa0fe,0xa0fe,0xa0fe,0xd570,0xd52a,0xa0fe,0xd570,0xfe21,0xd52a,0xa0fe,0xceca,0xceca,0xd570,0xd52a,0xd570,0xd52a,0xceca,0xa45d,0xa355,0xa7d5,0xa355,0xaa15,0xa355,0xaa87,0xa355,0xa355,0xa62b,0xa532,0xa355,0xa595,0xc995,0xa4d0,0xa847,0xa92d,0xa86b,0xa4a6,0xa45d,0xa45d,0xd101,0xa45d,0xd570,0xa45d,0xd500,0xa45d,0xa45d,0xdc57,0xcfe2,0xa45d,0xcc16,0xcc16,0xd101,0xcfe2,0xaf2b,0xf773,0xdc7f,0xd101,0xa7d5,0xa7d5,0xa7d5,0xc399,0xa7d5,0xf2f3,0xa7d5,0xa7d5,0xf6b5,0xf773,0xa7d5,0xd111,0xdc7f,0xd101,0xda33,0xc399,0xda33,0xd111,0xd570,0xaa15,0xc399,0xaa15,0xaa15,0xaa15,0xc292,0xaa15,0xaa15,0xd4be,0xd5b3,0xaa15,0xd4f5,0xcebf,0xaf07,0xf2f3,0xc399,0xc292,0xae32,0xad38,0xc5dc,0xc5f8,0xad38,0xfe21,0xc5dc,0xd286,0xc5d7,0xc5d7,0xad38,0xc5dc,0xad38,0xc5dc,0xc5d7,0xc5f8,0xc5d7,0xd286,0xc5f8,0xc5f8,0xf517,0xadd0,0xf8f5,0xadd0,0xd4be,0xadd0,0xadd0,0xadd0,0xadd0,0xadd0,0xcecf,0xadd0,0xd4fe,0xcecf,0xf52f,0xd4fe,0xd4fe,0xd4be,0xd4be,0xb1ae,0xc32a,0xb1ae,0xd52a,0xb1ae,0xd575,0xb1ae,0xb1ae,0xc375,0xd428,0xb1ae,0xb1ae,0xc095,0xd3b6,0xc375,0xc08d,0xf17d,0xc32a,0xddd5,0xb37a,0xb37a,0xd8bd,0xcfe2,0xf17d,0xcfe2,0xc756,0xb37a,0xb37a,0xd055,0xb37a,0xb37a,0xd055,0xd055,0xd8bd,0xcfe2,0xc756,0xd8bd,0xfbe1,0xb810,0xb7d2,0xb7d9,0xb67c,0xbcdc,0xb618,0xbcd8,0xb808,0xb7ac,0xb618,0xb618,0xb618,0xb85c,0xb82f,0xb832,0xb674,0xbc2c,0xb858,0xb6b2,0xb810,0xb992,0xc9cf,0xc5dc,0xced8,0xb810,0xbe12,0xcb4f,0xc992,0xb810,0xb810,0xb810,0xba9c,0xcc0b,0xcc93,0xc992,0xbf1c,0xcc9c,0xc9cf,0xb992,0xb992,0xcc9c,0xc5dc,0xf518,0xb992,0xde96,0xdc57,0xcc0b,0xb992,0xb992,0xb992,0xc5dc,0xcc0b,0xdc78,0xcc0b,0xbf1c,0xcc9c,0xcc9c,0xced8,0xceaa,0xbf18,0xce2c,0xbcdc,0xbcdc,0xde2d,0xbe6c,0xbec8,0xbcdc,0xbcdc,0xbcdc,0xcefe,0xbe99,0xbe6c,0xbf18,0xde8a,0xbe99,0xbec8,0xde96,0xbe55,0xf538,0xbe55,0xf52f,0xbe55,0xbe55,0xcecf,0xcecf,0xbe55,0xbe55,0xbe55,0xde96,0xcecf,0xce44,0xf517,0xde96,0xce44,0xce44,0xc01b,0xf505,0xc01b,0xd571,0xc01b,0xc01b,0xc01b,0xd52d,0xc01b,0xc01b,0xd52d,0xf520,0xc01b,0xd571,0xde86,0xde86,0xf9a1,0xd571,0xd52d,0xc386,0xf828,0xc386,0xf9a1,0xc386,0xd52d,0xc386,0xc386,0xc386,0xc386,0xc386,0xd428,0xc386,0xf217,0xd428,0xf520,0xf217,0xf217,0xd52d,0xc5dc,0xc5dc,0xdc78,0xc5dc,0xfe21,0xc5dc,0xde96,0xdc57,0xdc57,0xc5dc,0xc5dc,0xc5dc,0xc5dc,0xdc57,0xdc78,0xdc57,0xde96,0xdc78,0xdc78,0xc82e,0xd51e,0xc82e,0xc82e,0xc82e,0xc82e,0xc82e,0xf2ca,0xd571,0xc82e,0xf2ca,0xfe21,0xd571,0xc82e,0xd51e,0xd51e,0xf2ca,0xd571,0xf2ca,0xcc16,0xc995,0xdc7f,0xc995,0xcebf,0xc995,0xcecf,0xc995,0xc995,0xcc8f,0xcc8f,0xc995,0xcc16,0xc995,0xcc7f,0xdc57,0xce56,0xdc6f,0xcc7f,0xdc57,0xcc8f,0xfbe1,0xcc8f,0xf52f,0xcc8f,0xcecf,0xcc8f,0xcc8f,0xcc8f,0xcc8f,0xcc8f,0xdc57,0xcc8f,0xdc6f,0xdc57,0xf517,0xdc6f,0xdc6f,0xf517,0xcecf,0xfe21,0xcecf,0xf52f,0xcecf,0xcecf,0xcecf,0xcecf,0xcecf,0xcecf,0xcecf,0xf517,0xcecf,0xf52f,0xf517,0xf517,0xf52f,0xf52f,0xd086,0xdc57,0xf761,0xd086,0xf9a1,0xd086,0xd596,0xd086,0xd086,0xd086,0xd086,0xdc57,0xd086,0xd086,0xfbe1,0xdc57,0xd596,0xf761,0xf761,0xde86,0xde71,0xde86,0xde71,0xd2ed,0xd2ed,0xd2ed,0xde2d,0xd2ed,0xd2ed,0xde2d,0xde2d,0xde86,0xde71,0xd2ed,0xde86,0xfe21,0xde71,0xde2d,0xd428,0xf828,0xd428,0xfe21,0xd428,0xf520,0xd428,0xd428,0xd428,0xd428,0xd428,0xd428,0xd428,0xf828,0xd428,0xf520,0xf828,0xf828,0xf520,0xd711,0xd711,0xd711,0xf691,0xefd1,0xf691,0xefd1,0xd711,0xf5e8,0xd711,0xd711,0xf5e8,0xf5e8,0xd711,0xd711,0xf691,0xefd1,0xf5e8,0xf691,0xf5e8,0xd872,0xd872,0xf668,0xf132,0xfbe1,0xf132,0xf5e8,0xd872,0xd872,0xd872,0xd872,0xd872,0xd872,0xd872,0xf668,0xf132,0xf5e8,0xf668,0xdc57,0xdc57,0xfbe1,0xdc57,0xfe21,0xdc57,0xf517,0xdc57,0xdc57,0xdc57,0xdc57,0xdc57,0xdc57,0xdc57,0xfbe1,0xdc57,0xf517,0xfbe1,0xfbe1,0xde86,0xf505,0xde86,0xf505,0xde86,0xde86,0xde86,0xf520,0xde86,0xde86,0xf520,0xf520,0xde86,0xf505,0xde86,0xde86,0xfe21,0xf505,0xf520,0xe33f,0xe292,0xe2ea,0xe18a,0xe0e1,0xe303,0xe0e1,0xe30d,0xe317,0xe2d9,0xe31f,0xe319,0xe316,0xe321,0xe333,0xe1b6,0xe0e1,0xe30a,0xe257,0xe33f,0xe96d,0xe9af,0xe8ea,0xe33f,0xe552,0xe33f,0xe55c,0xe977,0xe9b0,0xe53d,0xe9b1,0xe97a,0xe475,0xe4c8,0xe937,0xe33f,0xe4d6,0xe89a,0xeded,0xe4be,0xe4be,0xe9c7,0xe4be,0xed98,0xe4be,0xe72c,0xe9cf,0xe76c,0xe9f4,0xe9cf,0xee51,0xee5f,0xe9f4,0xe9c7,0xe4be,0xee4f,0xee16,0xeded,0xe72c,0xe72c,0xed98,0xe72c,0xed98,0xe72c,0xe72c,0xee4f,0xebec,0xeded,0xee4f,0xeff5,0xefd1,0xeded,0xed98,0xe72c,0xee4f,0xef2e,0xed20,0xed98,0xe95a,0xe95a,0xe95a,0xe95a,0xe95a,0xe95a,0xecd8,0xed01,0xed20,0xf2f3,0xf2e1,0xf2ca,0xf2fe,0xed98,0xe95a,0xecd8,0xed01,0xefd1,0xebec,0xebec,0xef2e,0xebec,0xef2e,0xebec,0xebec,0xeff5,0xebec,0xefd1,0xeff5,0xeff5,0xefd1,0xefd1,0xef2e,0xebec,0xeff5,0xef2e,0xed20,0xf2fe,0xed20,0xed20,0xed20,0xed20,0xed20,0xed20,0xf0b8,0xf2ca,0xed20,0xf9b3,0xf9a1,0xf2ca,0xf2fe,0xf2fe,0xed20,0xf0b8,0xf2ca,0xefd1,0xefd1,0xefd1,0xf8d1,0xefd1,0xf8d1,0xefd1,0xefd1,0xf828,0xefd1,0xefd1,0xf828,0xf828,0xefd1,0xefd1,0xf8d1,0xefd1,0xf828,0xf8d1,0xf828,0xf132,0xf132,0xf8a8,0xf132,0xfe21,0xf132,0xf828,0xf132,0xf132,0xf132,0xf132,0xf132,0xf132,0xf132,0xf8a8,0xf132,0xf828,0xf8a8,0xf517,0xf517,0xfe21,0xf517,0xfe21,0xf517,0xf517,0xf517,0xf517,0xf517,0xf517,0xf517,0xf517,0xf517,0xfe21,0xf517,0xf517,0xfe21,0xfe21,0xf5e8,0xf5e8,0xf5e8,0xfbe1,0xf828,0xfbe1,0xf828,0xf5e8,0xf5e8,0xf5e8,0xf5e8,0xf5e8,0xf5e8,0xf5e8,0xf5e8,0xfbe1,0xf828,0xf5e8,0xfbe1,0xf828,0xf828,0xf828,0xfe21,0xf828,0xfe21,0xf828,0xf828,0xf828,0xf828,0xf828,0xf828,0xf828,0xf828,0xf828,0xfe21,0xf828,0xf828,0xfe21,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfe21,0xfbe1,0xfe21,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfbe1,0xfe21,0xfbe1,0xfbe1,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21,0xfe21]
def members (m : Nat) : Finset V := Finset.univ.filter fun x => m.testBit x.val
def zone (r : R) : Finset V := members ((zoneData[r.val]?).getD 0)
def T (r : R) := members ((TData[r.val]?).getD 0)
def U (r : R) := members ((UData[r.val]?).getD 0)
def given (d : Array Nat) (r : R) : V := Fin.ofNat 40 ((d[r.val]?).getD 0)
def line (x : L) : V := ⟨21+x.val,by omega⟩
def changeID (r : R) (x : L) := (switches[r.val*19+x.val]?).getD 0
def nextR (r : R) (x : L) : R := Fin.ofNat 113 (changeID r x / 576)
def label (r : R) (x : L) : K := Fin.ofNat 576 (changeID r x % 576)
def stored (r : R) (v : V) : Bool := ((zoneData[r.val]?).getD 0).testBit v.val
theorem memZone (r : R) (v : V) : v ∈ zone r ↔ stored r v = true := by simp [zone,members,stored]

def transOK (r : R) (x : L) (v : V) : Bool :=
  !(v == line x || (stored r v && !(decide (left v) && decide (G v (line x))))) ||
    stored (nextR r x) (action (label r x) v)
theorem tr0 : ∀ x : L, ∀ v : V, transOK 0 x v = true := by decide +kernel
theorem tr1 : ∀ x : L, ∀ v : V, transOK 1 x v = true := by decide +kernel
theorem tr2 : ∀ x : L, ∀ v : V, transOK 2 x v = true := by decide +kernel
theorem tr3 : ∀ x : L, ∀ v : V, transOK 3 x v = true := by decide +kernel
theorem tr4 : ∀ x : L, ∀ v : V, transOK 4 x v = true := by decide +kernel
theorem tr5 : ∀ x : L, ∀ v : V, transOK 5 x v = true := by decide +kernel
theorem tr6 : ∀ x : L, ∀ v : V, transOK 6 x v = true := by decide +kernel
theorem tr7 : ∀ x : L, ∀ v : V, transOK 7 x v = true := by decide +kernel
theorem tr8 : ∀ x : L, ∀ v : V, transOK 8 x v = true := by decide +kernel
theorem tr9 : ∀ x : L, ∀ v : V, transOK 9 x v = true := by decide +kernel
theorem tr10 : ∀ x : L, ∀ v : V, transOK 10 x v = true := by decide +kernel
theorem tr11 : ∀ x : L, ∀ v : V, transOK 11 x v = true := by decide +kernel
theorem tr12 : ∀ x : L, ∀ v : V, transOK 12 x v = true := by decide +kernel
theorem tr13 : ∀ x : L, ∀ v : V, transOK 13 x v = true := by decide +kernel
theorem tr14 : ∀ x : L, ∀ v : V, transOK 14 x v = true := by decide +kernel
theorem tr15 : ∀ x : L, ∀ v : V, transOK 15 x v = true := by decide +kernel
theorem tr16 : ∀ x : L, ∀ v : V, transOK 16 x v = true := by decide +kernel
theorem tr17 : ∀ x : L, ∀ v : V, transOK 17 x v = true := by decide +kernel
theorem tr18 : ∀ x : L, ∀ v : V, transOK 18 x v = true := by decide +kernel
theorem tr19 : ∀ x : L, ∀ v : V, transOK 19 x v = true := by decide +kernel
theorem tr20 : ∀ x : L, ∀ v : V, transOK 20 x v = true := by decide +kernel
theorem tr21 : ∀ x : L, ∀ v : V, transOK 21 x v = true := by decide +kernel
theorem tr22 : ∀ x : L, ∀ v : V, transOK 22 x v = true := by decide +kernel
theorem tr23 : ∀ x : L, ∀ v : V, transOK 23 x v = true := by decide +kernel
theorem tr24 : ∀ x : L, ∀ v : V, transOK 24 x v = true := by decide +kernel
theorem tr25 : ∀ x : L, ∀ v : V, transOK 25 x v = true := by decide +kernel
theorem tr26 : ∀ x : L, ∀ v : V, transOK 26 x v = true := by decide +kernel
theorem tr27 : ∀ x : L, ∀ v : V, transOK 27 x v = true := by decide +kernel
theorem tr28 : ∀ x : L, ∀ v : V, transOK 28 x v = true := by decide +kernel
theorem tr29 : ∀ x : L, ∀ v : V, transOK 29 x v = true := by decide +kernel
theorem tr30 : ∀ x : L, ∀ v : V, transOK 30 x v = true := by decide +kernel
theorem tr31 : ∀ x : L, ∀ v : V, transOK 31 x v = true := by decide +kernel
theorem tr32 : ∀ x : L, ∀ v : V, transOK 32 x v = true := by decide +kernel
theorem tr33 : ∀ x : L, ∀ v : V, transOK 33 x v = true := by decide +kernel
theorem tr34 : ∀ x : L, ∀ v : V, transOK 34 x v = true := by decide +kernel
theorem tr35 : ∀ x : L, ∀ v : V, transOK 35 x v = true := by decide +kernel
theorem tr36 : ∀ x : L, ∀ v : V, transOK 36 x v = true := by decide +kernel
theorem tr37 : ∀ x : L, ∀ v : V, transOK 37 x v = true := by decide +kernel
theorem tr38 : ∀ x : L, ∀ v : V, transOK 38 x v = true := by decide +kernel
theorem tr39 : ∀ x : L, ∀ v : V, transOK 39 x v = true := by decide +kernel
theorem tr40 : ∀ x : L, ∀ v : V, transOK 40 x v = true := by decide +kernel
theorem tr41 : ∀ x : L, ∀ v : V, transOK 41 x v = true := by decide +kernel
theorem tr42 : ∀ x : L, ∀ v : V, transOK 42 x v = true := by decide +kernel
theorem tr43 : ∀ x : L, ∀ v : V, transOK 43 x v = true := by decide +kernel
theorem tr44 : ∀ x : L, ∀ v : V, transOK 44 x v = true := by decide +kernel
theorem tr45 : ∀ x : L, ∀ v : V, transOK 45 x v = true := by decide +kernel
theorem tr46 : ∀ x : L, ∀ v : V, transOK 46 x v = true := by decide +kernel
theorem tr47 : ∀ x : L, ∀ v : V, transOK 47 x v = true := by decide +kernel
theorem tr48 : ∀ x : L, ∀ v : V, transOK 48 x v = true := by decide +kernel
theorem tr49 : ∀ x : L, ∀ v : V, transOK 49 x v = true := by decide +kernel
theorem tr50 : ∀ x : L, ∀ v : V, transOK 50 x v = true := by decide +kernel
theorem tr51 : ∀ x : L, ∀ v : V, transOK 51 x v = true := by decide +kernel
theorem tr52 : ∀ x : L, ∀ v : V, transOK 52 x v = true := by decide +kernel
theorem tr53 : ∀ x : L, ∀ v : V, transOK 53 x v = true := by decide +kernel
theorem tr54 : ∀ x : L, ∀ v : V, transOK 54 x v = true := by decide +kernel
theorem tr55 : ∀ x : L, ∀ v : V, transOK 55 x v = true := by decide +kernel
theorem tr56 : ∀ x : L, ∀ v : V, transOK 56 x v = true := by decide +kernel
theorem tr57 : ∀ x : L, ∀ v : V, transOK 57 x v = true := by decide +kernel
theorem tr58 : ∀ x : L, ∀ v : V, transOK 58 x v = true := by decide +kernel
theorem tr59 : ∀ x : L, ∀ v : V, transOK 59 x v = true := by decide +kernel
theorem tr60 : ∀ x : L, ∀ v : V, transOK 60 x v = true := by decide +kernel
theorem tr61 : ∀ x : L, ∀ v : V, transOK 61 x v = true := by decide +kernel
theorem tr62 : ∀ x : L, ∀ v : V, transOK 62 x v = true := by decide +kernel
theorem tr63 : ∀ x : L, ∀ v : V, transOK 63 x v = true := by decide +kernel
theorem tr64 : ∀ x : L, ∀ v : V, transOK 64 x v = true := by decide +kernel
theorem tr65 : ∀ x : L, ∀ v : V, transOK 65 x v = true := by decide +kernel
theorem tr66 : ∀ x : L, ∀ v : V, transOK 66 x v = true := by decide +kernel
theorem tr67 : ∀ x : L, ∀ v : V, transOK 67 x v = true := by decide +kernel
theorem tr68 : ∀ x : L, ∀ v : V, transOK 68 x v = true := by decide +kernel
theorem tr69 : ∀ x : L, ∀ v : V, transOK 69 x v = true := by decide +kernel
theorem tr70 : ∀ x : L, ∀ v : V, transOK 70 x v = true := by decide +kernel
theorem tr71 : ∀ x : L, ∀ v : V, transOK 71 x v = true := by decide +kernel
theorem tr72 : ∀ x : L, ∀ v : V, transOK 72 x v = true := by decide +kernel
theorem tr73 : ∀ x : L, ∀ v : V, transOK 73 x v = true := by decide +kernel
theorem tr74 : ∀ x : L, ∀ v : V, transOK 74 x v = true := by decide +kernel
theorem tr75 : ∀ x : L, ∀ v : V, transOK 75 x v = true := by decide +kernel
theorem tr76 : ∀ x : L, ∀ v : V, transOK 76 x v = true := by decide +kernel
theorem tr77 : ∀ x : L, ∀ v : V, transOK 77 x v = true := by decide +kernel
theorem tr78 : ∀ x : L, ∀ v : V, transOK 78 x v = true := by decide +kernel
theorem tr79 : ∀ x : L, ∀ v : V, transOK 79 x v = true := by decide +kernel
theorem tr80 : ∀ x : L, ∀ v : V, transOK 80 x v = true := by decide +kernel
theorem tr81 : ∀ x : L, ∀ v : V, transOK 81 x v = true := by decide +kernel
theorem tr82 : ∀ x : L, ∀ v : V, transOK 82 x v = true := by decide +kernel
theorem tr83 : ∀ x : L, ∀ v : V, transOK 83 x v = true := by decide +kernel
theorem tr84 : ∀ x : L, ∀ v : V, transOK 84 x v = true := by decide +kernel
theorem tr85 : ∀ x : L, ∀ v : V, transOK 85 x v = true := by decide +kernel
theorem tr86 : ∀ x : L, ∀ v : V, transOK 86 x v = true := by decide +kernel
theorem tr87 : ∀ x : L, ∀ v : V, transOK 87 x v = true := by decide +kernel
theorem tr88 : ∀ x : L, ∀ v : V, transOK 88 x v = true := by decide +kernel
theorem tr89 : ∀ x : L, ∀ v : V, transOK 89 x v = true := by decide +kernel
theorem tr90 : ∀ x : L, ∀ v : V, transOK 90 x v = true := by decide +kernel
theorem tr91 : ∀ x : L, ∀ v : V, transOK 91 x v = true := by decide +kernel
theorem tr92 : ∀ x : L, ∀ v : V, transOK 92 x v = true := by decide +kernel
theorem tr93 : ∀ x : L, ∀ v : V, transOK 93 x v = true := by decide +kernel
theorem tr94 : ∀ x : L, ∀ v : V, transOK 94 x v = true := by decide +kernel
theorem tr95 : ∀ x : L, ∀ v : V, transOK 95 x v = true := by decide +kernel
theorem tr96 : ∀ x : L, ∀ v : V, transOK 96 x v = true := by decide +kernel
theorem tr97 : ∀ x : L, ∀ v : V, transOK 97 x v = true := by decide +kernel
theorem tr98 : ∀ x : L, ∀ v : V, transOK 98 x v = true := by decide +kernel
theorem tr99 : ∀ x : L, ∀ v : V, transOK 99 x v = true := by decide +kernel
theorem tr100 : ∀ x : L, ∀ v : V, transOK 100 x v = true := by decide +kernel
theorem tr101 : ∀ x : L, ∀ v : V, transOK 101 x v = true := by decide +kernel
theorem tr102 : ∀ x : L, ∀ v : V, transOK 102 x v = true := by decide +kernel
theorem tr103 : ∀ x : L, ∀ v : V, transOK 103 x v = true := by decide +kernel
theorem tr104 : ∀ x : L, ∀ v : V, transOK 104 x v = true := by decide +kernel
theorem tr105 : ∀ x : L, ∀ v : V, transOK 105 x v = true := by decide +kernel
theorem tr106 : ∀ x : L, ∀ v : V, transOK 106 x v = true := by decide +kernel
theorem tr107 : ∀ x : L, ∀ v : V, transOK 107 x v = true := by decide +kernel
theorem tr108 : ∀ x : L, ∀ v : V, transOK 108 x v = true := by decide +kernel
theorem tr109 : ∀ x : L, ∀ v : V, transOK 109 x v = true := by decide +kernel
theorem tr110 : ∀ x : L, ∀ v : V, transOK 110 x v = true := by decide +kernel
theorem tr111 : ∀ x : L, ∀ v : V, transOK 111 x v = true := by decide +kernel
theorem tr112 : ∀ x : L, ∀ v : V, transOK 112 x v = true := by decide +kernel
theorem transitions (r : R) (x : L) (v : V) :
    v = line x ∨ (v ∈ zone r ∧ ¬ (left v ∧ G v (line x))) →
    action (label r x) v ∈ zone (nextR r x) := by
  intro h
  have ok : transOK r x v = true := by
    fin_cases r <;> first
      | exact tr0 x v
      | exact tr1 x v
      | exact tr2 x v
      | exact tr3 x v
      | exact tr4 x v
      | exact tr5 x v
      | exact tr6 x v
      | exact tr7 x v
      | exact tr8 x v
      | exact tr9 x v
      | exact tr10 x v
      | exact tr11 x v
      | exact tr12 x v
      | exact tr13 x v
      | exact tr14 x v
      | exact tr15 x v
      | exact tr16 x v
      | exact tr17 x v
      | exact tr18 x v
      | exact tr19 x v
      | exact tr20 x v
      | exact tr21 x v
      | exact tr22 x v
      | exact tr23 x v
      | exact tr24 x v
      | exact tr25 x v
      | exact tr26 x v
      | exact tr27 x v
      | exact tr28 x v
      | exact tr29 x v
      | exact tr30 x v
      | exact tr31 x v
      | exact tr32 x v
      | exact tr33 x v
      | exact tr34 x v
      | exact tr35 x v
      | exact tr36 x v
      | exact tr37 x v
      | exact tr38 x v
      | exact tr39 x v
      | exact tr40 x v
      | exact tr41 x v
      | exact tr42 x v
      | exact tr43 x v
      | exact tr44 x v
      | exact tr45 x v
      | exact tr46 x v
      | exact tr47 x v
      | exact tr48 x v
      | exact tr49 x v
      | exact tr50 x v
      | exact tr51 x v
      | exact tr52 x v
      | exact tr53 x v
      | exact tr54 x v
      | exact tr55 x v
      | exact tr56 x v
      | exact tr57 x v
      | exact tr58 x v
      | exact tr59 x v
      | exact tr60 x v
      | exact tr61 x v
      | exact tr62 x v
      | exact tr63 x v
      | exact tr64 x v
      | exact tr65 x v
      | exact tr66 x v
      | exact tr67 x v
      | exact tr68 x v
      | exact tr69 x v
      | exact tr70 x v
      | exact tr71 x v
      | exact tr72 x v
      | exact tr73 x v
      | exact tr74 x v
      | exact tr75 x v
      | exact tr76 x v
      | exact tr77 x v
      | exact tr78 x v
      | exact tr79 x v
      | exact tr80 x v
      | exact tr81 x v
      | exact tr82 x v
      | exact tr83 x v
      | exact tr84 x v
      | exact tr85 x v
      | exact tr86 x v
      | exact tr87 x v
      | exact tr88 x v
      | exact tr89 x v
      | exact tr90 x v
      | exact tr91 x v
      | exact tr92 x v
      | exact tr93 x v
      | exact tr94 x v
      | exact tr95 x v
      | exact tr96 x v
      | exact tr97 x v
      | exact tr98 x v
      | exact tr99 x v
      | exact tr100 x v
      | exact tr101 x v
      | exact tr102 x v
      | exact tr103 x v
      | exact tr104 x v
      | exact tr105 x v
      | exact tr106 x v
      | exact tr107 x v
      | exact tr108 x v
      | exact tr109 x v
      | exact tr110 x v
      | exact tr111 x v
      | exact tr112 x v
  apply (memZone _ _).mpr
  have premise : (v == line x || (stored r v && !(decide (left v) && decide (G v (line x))))) = true := by
    rcases h with h | ⟨h,h2⟩
    · simp [h]
    · by_cases hl : left v
      · have hg : ¬G v (line x) := fun g => h2 ⟨hl,g⟩
        simp [(memZone r v).mp h,hl,hg]
      · simp [(memZone r v).mp h,hl]
  simpa only [transOK,premise,Bool.not_true,Bool.false_or] using ok

theorem starts : ∀ v : V, left v → stored 0 v = true := by decide +kernel
def Envelope (I : Finset V) := ∃ r : R, ∃ e : V ≃ V, Valid e ∧ ∀ v∈I,e v∈zone r
theorem build (P Q : Finset V) (pts : ∀v∈P,left v) (ls : ∀v∈Q,¬left v)
    (none : ∀a∈P,∀b∈Q,¬G a b) : Envelope (P ∪ Q) := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    refine ⟨0,Equiv.refl V,validId,?_⟩
    intro v hv
    exact (memZone _ _).mpr (starts v (pts v (by simpa using hv)))
  | @insert w Q hw ih =>
    obtain ⟨r,e,good,env⟩ := ih (fun v hv => ls v (Finset.mem_insert_of_mem hv))
      (fun a ha b hb => none a ha b (Finset.mem_insert_of_mem hb))
    have right : ¬left (e w) := fun hl => ls w (Finset.mem_insert_self _ _) ((good.side _).mp hl)
    have low : 21≤(e w).val := by simpa [left] using right
    let l : L := ⟨(e w).val-21,by have := (e w).isLt; omega⟩
    have el : e w = line l := Fin.ext (by dsimp [line,l]; omega)
    let k := label r l
    refine ⟨nextR r l,e.trans (perm k), @validComp (fun x => e x) (action k) good (actionValid k),?_⟩
    intro v hv
    change action (label r l) (e v) ∈ zone (nextR r l)
    apply transitions
    rcases Finset.mem_union.mp hv with pv | qv
    · right
      refine ⟨env v (Finset.mem_union_left _ pv),?_⟩
      rintro ⟨_,a⟩
      exact none v pv w (Finset.mem_insert_self _ _) ((good.adj v w).mp (by simpa only [el] using a))
    · rcases Finset.mem_insert.mp qv with h | q
      · subst v
        exact Or.inl el
      · exact Or.inr ⟨env v (Finset.mem_union_right _ q),fun hh =>
          ls v (Finset.mem_insert_of_mem q) ((good.side v).mp hh.1)⟩

theorem envelope {I : Finset V} (ind : ∀i∈I,∀j∈I,¬G i j) : Envelope I := by
  classical
  let P := I.filter left
  let Q := I.filter fun v => ¬left v
  have union : P∪Q=I := by ext i; simp [P,Q]; tauto
  rw [←union]
  exact build P Q (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ h _ h' => ind _ (Finset.mem_filter.mp h).1 _ (Finset.mem_filter.mp h').1)

end Geometry9798


namespace PEqualNP.Outside.L_meta_971_aux
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem partial_exits (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J H : Finset (Fin n))
    (A : Fin n → Finset (Fin n))
    (incl : H ⊆ T) (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ H, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ H, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + H.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ H, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w H := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, incl hg⟩))
  have hdis : Disjoint (J.image pos) (H.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : H.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, incl hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this


end PEqualNP.Outside.L_meta_971_aux
namespace Merge9800
open PEqualNP.Outside.L_meta_971_aux
variable {n : ℕ} {D : Dag}

theorem step (hS : Strict n D) {P : Finset (Fin n)} {x : Fin n} (hx : x∉P)
    {w : ℕ} (xw : x∈supp n D w) (pw : (supp n D w ∩ P).Nonempty) :
    (merges n D (carrierT n D P)).card < (merges n D (carrierT n D (insert x P))).card := by
  classical
  let mixed (v : ℕ) := x∈supp n D v ∧ (supp n D v ∩ P).Nonempty
  have existsMixed : ∃v,mixed v := ⟨w,xw,pw⟩
  have spec := Nat.find_spec existsMixed
  have minimal : ∀ v, v < Nat.find existsMixed → ¬mixed v := fun v hv => Nat.find_min existsMixed hv
  generalize Nat.find existsMixed = q at spec minimal
  obtain ⟨qx,qp⟩ := spec
  have qbound := sem_supp_lt qx
  have qlarge : n≤q := by
    by_contra! h
    have hinput : supp n D q = {⟨q,h⟩} := supp_input D ⟨q,h⟩
    obtain ⟨p,hp⟩ := qp
    obtain ⟨pm,pp⟩ := Finset.mem_inter.mp hp
    rw [hinput,Finset.mem_singleton] at pm qx
    exact hx ((qx.trans pm.symm).symm ▸ pp)
  obtain ⟨j,rfl⟩ : ∃j,q=n+j := ⟨q-n,by omega⟩
  have hj : j<D.length := by omega
  obtain ⟨al,bl,-⟩ := hS j hj
  obtain ⟨y,hy⟩ := qp
  obtain ⟨qy,yp⟩ := Finset.mem_inter.mp hy
  have lift {v : ℕ} (hv : v∈carrierT n D P) : v∈carrierT n D (insert x P) := by
    obtain ⟨a,ha⟩ := k4_mem_carrier.mp hv
    obtain ⟨am,ap⟩ := Finset.mem_inter.mp ha
    exact k4_mem_carrier.mpr ⟨a,Finset.mem_inter.mpr ⟨am,Finset.mem_insert_of_mem ap⟩⟩
  have sub : merges n D (carrierT n D P) ⊆ merges n D (carrierT n D (insert x P)) := by
    intro k hk
    obtain ⟨hr,out,oa,ob⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hr,lift out,lift oa,lift ob⟩
  apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩)
  intro eqm
  have consume (a b : ℕ) (ha : a<n+j) (hb : b<n+j)
      (xa : x∈supp n D a) (yb : y∈supp n D b) :
      a∈carrierT n D (insert x P) ∧ b∈carrierT n D (insert x P) ∧ a∉carrierT n D P := by
    exact ⟨k4_mem_carrier.mpr ⟨x,Finset.mem_inter.mpr ⟨xa,Finset.mem_insert_self _ _⟩⟩,
      k4_mem_carrier.mpr ⟨y,Finset.mem_inter.mpr ⟨yb,Finset.mem_insert_of_mem yp⟩⟩,
      fun hp => minimal a ha ⟨xa,k4_mem_carrier.mp hp⟩⟩
  have out : n+j ∈ carrierT n D (insert x P) := k4_mem_carrier.mpr
    ⟨x,Finset.mem_inter.mpr ⟨qx,Finset.mem_insert_self _ _⟩⟩
  have joined (aa : opA D j∈carrierT n D (insert x P)) (bb : opB D j∈carrierT n D (insert x P)) :
      opA D j∈carrierT n D P ∧ opB D j∈carrierT n D P := by
    have hk : j∈merges n D (carrierT n D (insert x P)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,out,aa,bb⟩
    rw [←eqm] at hk
    exact (Finset.mem_filter.mp hk).2.2
  cases ht : tag D j
  · rw [sem_supp_or hS hj ht,Finset.mem_union] at qx qy
    rcases qx with xa|xb <;> rcases qy with ya|yb
    · exact minimal _ al ⟨xa,y,Finset.mem_inter.mpr ⟨ya,yp⟩⟩
    · obtain ⟨a,b,na⟩ := consume _ _ al bl xa yb
      exact na (joined a b).1
    · obtain ⟨b,a,nb⟩ := consume _ _ bl al xb ya
      exact nb (joined a b).2
    · exact minimal _ bl ⟨xb,y,Finset.mem_inter.mpr ⟨yb,yp⟩⟩
  · rw [sem_supp_and hS hj ht,Finset.mem_inter] at qx qy
    exact minimal _ al ⟨qx.1,y,Finset.mem_inter.mpr ⟨qy.1,yp⟩⟩

theorem support_price (hS : Strict n D) (P : Finset (Fin n)) (w : ℕ) (h : P ⊆ supp n D w) :
    P.card ≤ (merges n D (carrierT n D P)).card+1 := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert x P hx ih =>
    have sub : P ⊆ supp n D w := fun v hv => h (Finset.mem_insert_of_mem hv)
    by_cases ne : P.Nonempty
    · obtain ⟨y,hy⟩ := ne
      have more := step hS hx (h (Finset.mem_insert_self _ _)) ⟨y,Finset.mem_inter.mpr ⟨sub hy,hy⟩⟩
      have prev := ih sub
      rw [Finset.card_insert_of_notMem hx]
      omega
    · have empty := Finset.not_nonempty_iff_eq_empty.mp ne
      simp [empty]
end Merge9800

namespace Mixed9800
open Geometry9798 PEqualNP.Outside.L_meta_971_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def nbr (v : V) := Finset.univ.filter fun i => G v i

def Data (Z T U H : Finset V) (A : V → Finset V) : Prop :=
  H ⊆ T ∧ (∀i∈Z,i∉U → (∃a∈T,G i a) ∧ ∀ f∈H,∃a∈A f,G i a) ∧
  ∀ f∈H, (∀ a∈A f,∀ b∈A f,¬G a b) ∧ T.erase f ⊆ A f ∧ ∃ a∈A f,G f a
def every (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 40).all fun i => if i∈S then f i else true
def someIn (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 40).any fun i => decide (i∈S) && f i
theorem every_true (S : Finset V) (f : V → Bool) :
    every S f=true ↔ ∀i∈S,f i=true := by
  simp [every,List.all_eq_true]
theorem someIn_true (S : Finset V) (f : V → Bool) :
    someIn S f=true ↔ ∃i∈S,f i=true := by
  simp [someIn,List.any_eq_true]

def verifies (Z T U H : Finset V) (A : V → Finset V) : Bool :=
  every H (fun f => decide (f∈T)) &&
  (every Z (fun i => if i∈U then true else
    someIn T (fun a => decide (G i a)) &&
    every H (fun f => someIn (A f) (fun a => decide (G i a)))) &&
   every H (fun f => every (A f) (fun a => every (A f) (fun b => !(decide (G a b)))) &&
     (every (T.erase f) (fun a => decide (a∈A f)) && someIn (A f) (fun a => decide (G f a)))))

theorem verifies_sound {Z T U H : Finset V} {A : V → Finset V} (h : verifies Z T U H A = true) :
    Data Z T U H A := by
  simp only [verifies,Bool.and_eq_true,every_true,someIn_true] at h
  obtain ⟨sub,cover,expose⟩ := h
  refine ⟨fun i hi => of_decide_eq_true (sub i hi),?_,?_⟩
  · intro i hi hu
    have h0 := cover i hi
    simp only [hu,if_false,Bool.and_eq_true,every_true,someIn_true,decide_eq_true_eq] at h0
    exact h0
  · intro f hf
    have h0 := expose f hf
    simp at h0
    exact h0

inductive Good (k : ℕ) : Finset V → Prop where
 | done (Z T U H : Finset V) (A : V → Finset V) (data : Data Z T U H A)
     (price : U.card+2*T.card ≤ k+H.card) : Good k Z
 | pivot (Z T U H : Finset V) (A : V → Finset V) (z : V) (data : Data Z T U H A)
     (price : U.card+2*T.card+1 ≤ k+H.card+(nbr z ∩ T).card)
     (child : Good k (Z.erase z)) : Good k Z

theorem merges_mono {D : Dag} {T P : Finset V} (h : P ⊆ T) :
    merges 40 D (carrierT 40 D P) ⊆ merges 40 D (carrierT 40 D T) := by
  have lift {w : ℕ} (hw : w∈carrierT 40 D P) : w∈carrierT 40 D T := by
    obtain ⟨v,hv⟩ := k4_mem_carrier.mp hw
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hv
    exact k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨a,h b⟩⟩
  intro j hj
  obtain ⟨hr,out,a,b⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hr,lift out,lift a,lift b⟩

theorem charge {D : Dag} (hG : sem_Gr G) (live : StrictLive 40 D) (sem : sem_Comp 40 G D)
    {Z T U H : Finset V} {A : V → Finset V} (inc : ineligSet 40 D ⊆ Z) (dat : Data Z T U H A) :
    79+Bzero 40 D+H.card+(merges 40 D (carrierT 40 D T)).card ≤ D.length+U.card+2*T.card := by
  classical
  let I := ineligSet 40 D
  let E := eligSet 40 D
  have total : I.card+E.card=40 := by
    simpa [I,ineligSet,E] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ E)
  obtain ⟨pos,hp⟩ := k4_assigned hG live sem
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hG live.1 sem
  have bal := k4_budget hG live sem b hb T
  change _+_+E.card≤_ at bal
  have ex := partial_exits hG live.1 sem hp T (I \ U) H A dat.1 (by
    intro i hi
    obtain ⟨hi,hu⟩ := Finset.mem_sdiff.mp hi
    exact ⟨hi,dat.2.1 i (inc hi) hu⟩) dat.2.2
  have ij : I ⊆ (I \ U) ∪ U := by
    intro i hi
    by_cases hu : i∈U
    · exact Finset.mem_union_right _ hu
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,hu⟩)
  have si := (Finset.card_le_card ij).trans (Finset.card_union_le _ _)
  have raw := surplus_identity live
  have plus := totalSurplus_split 40 D
  omega

theorem panelBound {k : ℕ} {Z : Finset V} {D : Dag} (hG : sem_Gr G) (live : StrictLive 40 D)
    (sem : sem_Comp 40 G D) (inc : ineligSet 40 D ⊆ Z) (valid : Good k Z) : 79+Bzero 40 D≤D.length+k := by
  classical
  induction valid with
  | done Z T U H A dat price =>
    have c := charge hG live sem inc dat
    omega
  | pivot Z T U H A z dat price child ih =>
    by_cases hz : z∈ineligSet 40 D
    · have c := charge hG live sem inc dat
      obtain ⟨pos,hp⟩ := k4_assigned hG live sem
      have prop : nbr z ∩ T ⊆ supp 40 D (src D (pos z)) := by
        intro a ha
        exact (hp.1 z hz).2.2.1 a (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
      have m := Merge9800.support_price live.1 (nbr z ∩ T) (src D (pos z)) prop
      have incl := Finset.card_le_card (merges_mono (D:=D) (Finset.inter_subset_right : nbr z ∩ T ⊆ T))
      omega
    · exact ih (fun i hi => Finset.mem_erase.mpr ⟨fun e => hz (e ▸ hi),inc hi⟩)
def zdata : Array Nat := #[0xa06a01,0xa0b402,0xa2d002,0x141a804,0x1502d00,0x2803a01,0x2806a01,0x281a804,0x28a8801,0x2a88801,0x480b402,0x2402b002,0x240a3200,0x9802c800,0xd1120002,0x131018002,0x131500002,0x262882000,0xe06a01,0x1702d00,0x1a0b402,0x1a2d002,0x228e030,0x2a03a01,0x2aa8801,0x2c06a01,0x2c1a804,0x341a804,0x4c0b402,0xaa88801,0x1103d002,0x2482b002,0x248a3200,0x2680b200,0x2682a200,0x2682b000,0x268aa000,0x2870a001,0x50c14003,0x9a02c800,0x9aa04001,0x9aa28000,0xd5120002,0x111459000,0x131418002,0x134409002,0x135500002,0x141300482,0x26a882000,0x200022c031,0x3ac23,0x32c213,0x70d601,0xc1d403,0xe07a01,0x1703d00,0x1e0b402,0x2c07a01,0x2e03a01,0x3c1a804,0x4e0b402,0x5a0b402,0xa28e030,0xaaa8801,0xac1a804,0x1183d002,0x11a2d002,0x1aa88801,0x24a2b002,0x24aa3200,0x26a0b200,0x26a2a200,0x26a2b000,0x26aaa000,0x7d150000,0x9a82c800,0x9aa04801,0x9aaa8000,0x115459000,0x135409002,0x135418002,0x135540002,0x1c40c0608,0x1c60c0208,0x26a8a2000,0x2c8aa0001,0x4d5120002,0x5b0540002,0x5f4140000,0x86e0c2000,0xbe8000005,0xbe8080001,0xdb0400003,0xfc0000007,0x106e882000,0x15e4100002,0x200222c031,0x2002c1c005,0x200a034025,0x201782c000,0x205a814001,0x2482e04001,0x3ac27,0x32c613,0x70d621,0xc1d603,0xe07e01,0x1707d00,0x1e0f402,0x22afa00,0x2607b20,0x2c17a01,0x2e07a01,0x360f900,0x3a2f800,0x3c1e804,0x3e0f800,0x4e0f402,0x5a0f402,0x6e0f200,0x722f010,0x7a2f000,0x7c1f000,0xa2ae030,0xa60e821,0xaaac801,0xac1e804,0xae0e801,0xf22e010,0xfa2e000,0x10e0d803,0x11e0d802,0x12c1d801,0x12e0d801,0x13e0d800,0x1583d002,0x15a2d002,0x1ac1c801,0x20e0b203,0x2170b102,0x21a2b082,0x2260b301,0x22e0b201,0x24aab200,0x24e0b202,0x2570b002,0x25a2b002,0x26aaa200,0x26e0b200,0x27a2b000,0x2eaaa000,0x35a29002,0x44e06602,0x45a26402,0x4da26400,0x4eaa6000,0x6e0f2000,0x8570c402,0x95a2c002,0x9a8ac800,0x9aa0c801,0x9aa88801,0xbaaa8000,0xc5704402,0xf1540102,0x111e09802,0x113e09800,0x135419002,0x135458002,0x135459000,0x135509002,0x135541002,0x17d150000,0x1b0708003,0x1c41c0608,0x1c4380602,0x1c4700602,0x1cd540400,0x26e8a2000,0x2caaa0001,0x5b4540002,0x5f5140000,0x6d5120002,0xbea000005,0xbea080001,0xc90e04003,0xfb0400003,0xfe0000007,0x126e882000,0x15e4500002,0x200a034035,0x200a22c031,0x200ac1c005,0x201783c000,0x201ac1c001,0x205ac14001,0x209782c000,0x24c2e04001,0xc6d5800000,0x3ac67,0x3ac613,0x70d623,0xc1de03,0xe07e03,0x1707d02,0x1e0fc02,0x22afa01,0x2607b21,0x2c17a05,0x2e0fa01,0x322f910,0x3c1f804,0x4e0f602,0x5a2f402,0xa2ae031,0xaaae801,0xac1e805,0x10c1d843,0x1583d00a,0x2070b303,0x24aab202,0x26aab200,0x9a8ac801,0x9ae0c801,0xbeaa8000,0x135459002,0x135709002,0x135c19002,0x137459000,0x17d550000,0x19aa88801,0x1c41c060a,0x26eaa2000,0x2daaa0001,0x3c5700402,0x44fa26000,0x535541002,0x5b5540002,0x5f5540000,0x6f5120002,0xbea800005,0xbea880001,0xcd0e04003,0xfb0c00003,0xfe0400007,0x15e5500002,0x1a6e882000,0x200a03c035,0x201f83c000,0x209f82c000,0x24cae04001,0xd6d5800000,0x3ec67,0x3ac713,0x70de23,0xc1de07,0xe0fe03,0x170fd02,0x1c1fc06,0x22afb01,0x260fb21,0x2c1fa05,0xa2ae831,0x9aaac801,0x135559002,0x2faaa0001,0x5f5540002,0x5fd540000,0x6f5320002,0xbfa880001,0xfe0c00007,0x15f5500002,0x1a6ea82000,0x209fa2c000,0x2bea800005,0x2ccae04001,0x4fb0c00003,0x66fa800001,0xd365c00002,0xd7d5800000,0x3ec77,0x3acf13,0x70df23,0xc1de47,0x207db2c,0x22afb11,0xa0fc835,0xbfaa80001,0x17f5500002,0x2cdae04001,0x2fea800005,0x33fd500000,0x4fb0e00003,0x67fa800001,0xd375c00002,0xd7f5800000,0x3ecf7,0x3adf13,0x70ff23,0xc1fe47,0x207db2d,0x22afb31,0xa0fe835,0x17f5700002,0x2feac00005,0x33fd700000,0x4ff0e00003,0x67faa00001,0xd3f5c00002,0xd7f5c00000,0x7ecf7,0x3adf93,0x20fdb2d,0x37fd700000,0x67fae00001,0xd7f5c00002,0xd7f5e00000,0x7eef7,0x3adfb3,0x20fdb3d,0x6ffae00001,0xd7f5e00002,0xdff5e00000,0x7eff7,0x3affb3,0x20ffb3d,0xdff5e00002,0xdffde00000,0xfeff7,0xfffde00000,0x1feff7,0xffffe00000,0x1fefff,0x1fffff]
def tdata : Array Nat := #[0x40000,0x40000,0x40000,0x80000,0x80000,0x100000,0x100000,0x100000,0x100000,0x40,0x100,0x800,0x800,0x200,0x10,0x20,0x8,0x10,0x18,0x48,0x60,0x60,0x400040,0x40040,0x40040,0x90,0x90,0xc0,0x90,0xa,0x8000200,0x120,0x120,0xa0,0xa0,0xa0,0xa0,0x8,0x10,0x82,0x6,0x6,0x5,0x50,0x18,0xc,0x5,0x40,0xa,0x440000,0xa0000000,0xa00000000,0x1200000000,0x1400000000,0xc040000000,0x9040000000,0x80018,0xc040000000,0x98,0x100030,0x4000c,0x105,0x80000a,0x10a,0x10a,0x8000030,0x214,0x16,0x4000c,0x4000c,0x4c,0x4c,0x4c,0x4c,0xa00,0x32,0x24000200,0x400400200,0x85,0x40080200,0xd,0x2000800400,0x80000c0,0xc0,0x100400800,0x41000,0x800080400,0x2400,0x500,0x800,0xa00,0xa00,0x2400,0x18000,0x500,0x500,0x400042,0x200012,0x1200002,0x100100200,0x12,0x10080,0x14000000,0x12000000,0x21000000,0x208000000,0x1010000000,0x4100000000,0xc020040000,0x140000000,0x28000000,0x880000000,0xc020040000,0x40000040,0x40000040,0xc020000010,0x40000040,0xc020040000,0xc020040000,0x200000080,0x40000040,0x100000040,0x80000080,0x100400000,0x20000008,0xc020000002,0xc020000002,0x8000000008,0x100000040,0x140,0x40000010,0x40000010,0x40000010,0x40000010,0x40000010,0x40000105,0x105,0x4000012,0x8000008,0x8000008,0x80000020,0x8000008,0x8000000008,0x8840000004,0x8000008,0x8000000008,0x61,0x2401100000,0x88,0x60,0x108,0x24,0x10000010,0x100000040,0x140,0x140,0x2000000800,0x2000080,0x24,0x2500100000,0x8200001400,0xa000011000,0x28,0xc0,0x800010,0x40000010,0x40000040,0xc8000400,0x2200200400,0x1400004800,0xc002000800,0x5008000800,0x140,0x2008,0xc802000000,0x2000040,0xc0,0xc0,0x180,0xc0,0x180,0x60,0x8080,0xc0,0xc0,0x10010,0x280,0x4800,0x40080,0x20080,0xe00002,0x10080000a,0x20000010a,0xa00080400,0x200000012,0x98,0xa0,0x50,0x8004,0x3200000,0x3400000,0xb000000,0x68000000,0x3008000000,0x6002000000,0x2060000000,0xc001000000,0x85000000,0x4804000000,0x8240000000,0x40000040,0x40c0000000,0x218000000,0x1100000020,0x8001400000,0xa100000000,0x8004000002,0x40000010,0x8028400000,0x8000000008,0x2008000004,0xc008040800,0x9001000012,0x98,0x504,0x1408002800,0x4c,0x130,0x4c0,0x58,0x2140,0x200a000000,0xc8,0x250,0x2000040,0x100000040,0x80500,0x82020,0x80090,0x4a0,0x100120,0x100120,0x9810,0x130,0x28080,0x80021,0x100800,0xc840000002,0x302,0x302,0x10a,0x1001,0x120000000,0x1400800000,0x860000000,0x4014000000,0x8240000000,0x8440000000,0x6400000000,0x8108000000,0x8240000000,0x8240000000,0x2060000000,0x3200110008,0x9800084004,0x428,0x850,0x148,0x10044,0x610,0x130,0x411,0x140008,0x40044,0x40802,0x110800,0x184000,0x41400,0x4011,0x2100,0x70000000,0x2840000000,0x408800000,0x41200000,0x28200000,0x50400000,0x8020600000,0x50040,0x8280,0x2610,0x10500,0x3080,0x5000c,0x6100,0x2610,0x4420,0x86000000,0x5008000000,0xa180000000,0xa090000000,0x9004000000,0xa1800000,0xa180000000,0x50044,0xa0088,0x40048,0x9810,0x50040,0x10a0,0x80090,0x3000200000,0x6400000,0x4401000000,0x80500,0x80088,0x80500,0x40048,0xa11000000,0xa1800000,0x50c00000,0x110a00,0x4004c,0x130800,0x504800000,0xa180000000,0xa180000000,0x120a00,0x1308,0x2401400000,0xc2800,0xc802800000,0x1004c2,0x8028600000,0x50c8000000]
def udata : Array Nat := #[0x6a01,0xb402,0x2d002,0x1a804,0x102d00,0x3a01,0x6a01,0x1a804,0xa8801,0x888801,0xb402,0x2b002,0xa3200,0x8002c800,0x81120002,0x110018002,0x111100002,0x222082000,0x6a01,0x102d00,0xb402,0x2d002,0xe020,0x3a01,0xa8801,0x6a01,0x1a804,0x1a804,0xb402,0x888801,0x3c000,0x2b002,0xa3200,0xb200,0x2a200,0x2b000,0xaa000,0x10a001,0x14003,0x1002c800,0x80804001,0x80828000,0xc0120002,0x59000,0x101018002,0x100009002,0x120500002,0x100482,0x240882000,0xc021,0x28003,0x200013,0x700000,0xc04002,0xe00200,0x1600100,0xb402,0x2c00200,0x3a01,0x1a804,0xb402,0xb402,0x8e000,0xa8801,0x1a804,0x3c000,0x2d002,0x88801,0x2b002,0xa3200,0x80b200,0x82a200,0x82b000,0x8aa000,0x150000,0x2c800,0x82a00000,0x82a00000,0x100059000,0x124000002,0x100018002,0x105400000,0xc0400,0xc0208,0x20a800000,0xa0001,0xc4000002,0x540002,0xc0140000,0xa0c2000,0x180000005,0x180080001,0x800400003,0x100000007,0x40082000,0xc0100002,0xc021,0xc001,0x24000,0x2004008000,0x14001,0x2000804001,0x38022,0x22c001,0x709000,0xc10401,0xe04800,0x1600c00,0x1400002,0x2280200,0x2602000,0x2c04001,0x2400200,0x406100,0x826000,0x3010000,0xc06000,0x4400002,0x5000002,0xa03000,0x4026000,0x4809000,0x180c000,0xa208020,0x200a001,0xa20000,0xc10000,0x2804800,0xc008010,0x2e000,0x204003,0x1204002,0x2014001,0x2204001,0x3204000,0x34002,0x2d002,0x1c000,0x80a001,0x110a000,0x228002,0x200a001,0x2801200,0x20880000,0x480a000,0x5001002,0x2b002,0x24220000,0x80b200,0x402b000,0x20aa000,0x29002,0x4204002,0x4800402,0x26400,0xa6000,0xa030000,0x120c000,0x2c002,0x98000000,0xa00800,0x12800000,0x120a8000,0x104402,0xa1000002,0x101200002,0x10c00000,0x105400000,0x105400000,0x11400000,0x111400000,0x111400000,0x30150000,0x108003,0x1c4040000,0x84080200,0x100602,0x8140400,0x600a2000,0x88a0001,0x30140002,0x414140000,0x11120002,0x828000005,0x828080001,0x4003,0x520000003,0x480000007,0x68082000,0x460100002,0x4001,0x8001,0x10005,0x4800000,0x10001,0x2000014001,0x201002c000,0x2480004001,0x81800000,0x2a800,0x20c000,0x60c000,0xc10001,0xe04000,0x1600100,0x1e00000,0x2220800,0x2604000,0x2c02000,0x2e00000,0x26100,0x3c00000,0x4e00000,0x4208002,0xa204000,0xaa00000,0xc14000,0x14003,0x15810000,0x1302,0x20828000,0x2020000,0x80004800,0xc801,0x800a8000,0x1400000,0x109002,0x19002,0x59000,0x4150000,0x88801,0x1c4000000,0x8a2000,0x800a0001,0x284400000,0x40c800000,0x141002,0x4140002,0x120140000,0x40120002,0x240000005,0x240080001,0x204003,0xa00000003,0x20000007,0x140100002,0x1208082000,0x20,0x3c000,0x8002c000,0xc0004001,0x610800000,0x18007,0x204202,0x600003,0xc18002,0xe00402,0x1604002,0x1c00000,0x2280800,0x2600120,0x2c10004,0xa220001,0x10000000,0x2,0x2400a0001,0x480140002,0x90140000,0x220120002,0x180080001,0xa00000007,0x180100002,0x44082000,0x8802c000,0x180000005,0x8404001,0x90000003,0x1,0x2,0x5241000000,0x30003,0x204501,0x604801,0xc04402,0x2028000,0x2204101,0xa000000,0x38080001,0x1120100002,0x204001,0x2240000005,0x21100000,0x100000003,0x42000001,0x4004000002,0x8044000000,0x2c010,0x208810,0x600600,0xc04040,0x2014220,0x2228000,0xa000014,0x20500002,0x40800005,0x94100000,0x100200003,0x4038000001,0x8110000002,0x9120000000,0xc0b0,0x20d200,0x2060808,0x2c0300000,0x150800001,0x82c0000002,0x4494000000,0x2,0x228002,0x2014001,0x100400001,0x480000002,0x211000000,0x202,0x200610,0x2000214,0x480200002,0x0,0x4004,0x8000000,0x0,0x0,0x0,0x0]
def hdata : Array Nat := #[0x40000,0x40000,0x40000,0x80000,0x80000,0x100000,0x100000,0x100000,0x100000,0x40,0x100,0x800,0x800,0x200,0x10,0x20,0x8,0x10,0x18,0x48,0x60,0x60,0x400040,0x40040,0x40040,0x90,0x90,0xc0,0x90,0xa,0x8000200,0x120,0x120,0xa0,0xa0,0xa0,0xa0,0x8,0x0,0x82,0x6,0x6,0x5,0x50,0x18,0xc,0x5,0x40,0xa,0x440000,0xa0000000,0xa00000000,0x1200000000,0x1400000000,0xc040000000,0x9040000000,0x80018,0xc040000000,0x98,0x100030,0x4000c,0x105,0x80000a,0x10a,0x10a,0x8000030,0x214,0x16,0x4000c,0x4000c,0x4c,0x4c,0x4c,0x4c,0xa00,0x32,0x24000200,0x400400200,0x85,0x40080200,0xd,0x2000800400,0x80000c0,0xc0,0x100400800,0x41000,0x800080400,0x2400,0x500,0x800,0xa00,0xa00,0x2400,0x18000,0x500,0x500,0x400042,0x200012,0x1200000,0x100100200,0x10,0x10080,0x14000000,0x12000000,0x21000000,0x208000000,0x1010000000,0x4100000000,0xc020040000,0x140000000,0x28000000,0x880000000,0xc020040000,0x40000040,0x40000040,0xc020000010,0x40000040,0xc020040000,0xc020040000,0x200000080,0x40000040,0x100000040,0x80000080,0x100400000,0x20000008,0xc020000002,0xc020000002,0x8000000008,0x100000040,0x140,0x40000010,0x40000010,0x40000010,0x40000010,0x40000010,0x40000105,0x105,0x4000012,0x8000008,0x8000008,0x80000020,0x8000008,0x8000000008,0x8840000004,0x8000008,0x8000000008,0x61,0x2401100000,0x88,0x60,0x108,0x24,0x10000010,0x100000040,0x140,0x140,0x2000000800,0x2000080,0x24,0x2500100000,0x8200001400,0xa000011000,0x28,0xc0,0x800010,0x40000010,0x40000040,0xc8000400,0x2200200400,0x1400004800,0xc002000800,0x5008000800,0x140,0x2008,0xc802000000,0x2000040,0xc0,0xc0,0x180,0xc0,0x180,0x60,0x8080,0xc0,0xc0,0x10,0x280,0x4800,0x40080,0x20080,0xe00000,0x100800008,0x200000108,0xa00080400,0x200000010,0x88,0xa0,0x50,0x4,0x3200000,0x1400000,0xb000000,0x68000000,0x3008000000,0x6002000000,0x2060000000,0xc001000000,0x85000000,0x4804000000,0x8240000000,0x40000040,0x40c0000000,0x218000000,0x1100000020,0x8001400000,0xa100000000,0x8004000002,0x40000010,0x8028400000,0x8000000008,0x2008000004,0xc008040800,0x9001000012,0x98,0x504,0x1408002800,0x4c,0x130,0x4c0,0x58,0x2140,0x200a000000,0xc8,0x250,0x2000040,0x100000040,0x80500,0x82020,0x80090,0x4a0,0x100120,0x100120,0x9800,0x130,0x28080,0x80021,0x100800,0xc840000000,0x300,0x300,0x108,0x1000,0x120000000,0x1400800000,0x860000000,0x4014000000,0x8240000000,0x8440000000,0x6400000000,0x8108000000,0x8240000000,0x8240000000,0x2060000000,0x3200110008,0x9800084004,0x428,0x850,0x148,0x10044,0x610,0x130,0x411,0x140008,0x40044,0x40800,0x100800,0x180000,0x40000,0x10,0x2100,0x70000000,0x2840000000,0x408800000,0x41200000,0x28200000,0x50400000,0x8020600000,0x50040,0x8280,0x2600,0x10500,0x3080,0x4000c,0x2100,0x2600,0x400,0x86000000,0x5008000000,0xa180000000,0xa090000000,0x9004000000,0xa1800000,0xa180000000,0x50044,0xa0088,0x40048,0x9800,0x50040,0x1080,0x80080,0x3000200000,0x6400000,0x4401000000,0x80500,0x80088,0x80500,0x40048,0x801000000,0xa1800000,0x50c00000,0x100a00,0x40048,0x100800,0x400800000,0xa180000000,0xa180000000,0x100a00,0x0,0x400000,0x0,0xc000000000,0x0,0x8000000,0x0]
def adata : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201fb3d7,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201fb3d7,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x155fd06,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400827acf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x420f632d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc1fe47,0x0,0x0,0x0,0x1101d98ab,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x860ec218,0x0,0x303a9183,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8600c2187,0x0,0x200c13c47,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1061112186,0x0,0x0,0x20b032814,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10403863a2,0x0,0x409166894,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80600f0386,0x405107018a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9004094272,0x0,0x0,0x0,0x0,0x0,0x80420f4324,0x0,0x0,0x105089408a,0x0,0x0,0x0,0x81fecf5,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80600f0386,0x405107018a,0x0,0x0,0x0,0x81fecf5,0x101fd9eb,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x201fb3d7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200083d6cd,0x0,0xc1fe47,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1117d98a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x855ec65,0x281fa0d5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100209eb3c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x41ff67a,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x55ff67,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x55ff67,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2517b012,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x102019a3d6,0x0,0x0,0x1041d963a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401547806,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x500141abf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40556727,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x481f64a5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4401662af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80800e4f56,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x400007affb,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200283d20d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x280000d5fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x88becc5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x83aecb1,0x855ec65,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x301f91c3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x104559622,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101159c9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1055d963,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8020cf13d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80044f567,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100899e8f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x855ec65,0x0,0x0,0x0,0x0,0x155fd06,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80088f4cf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x83aecb1,0x0,0x0,0x103ad9a3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x841ec65a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8516c41a,0x0,0x0,0x4aaf602,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1081d8cb5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4100058ebb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2055b347,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x31179182,0x0,0x860ec218,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x188bc8c1,0x0,0x0,0x345f904,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2c1fa050,0x0,0x0,0x0,0x0,0x10305981c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2420b212d,0x0,0x0,0x0,0x0,0x0,0x681f2085,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x108110c91e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1917c880,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40108388cb,0x0,0x0,0x0,0x0,0x0,0x108898c85,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc220030152,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc002070b30,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80280f00d4,0x4070070183,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30c190430,0x0,0x70550103,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x61832086,0x0,0x10c898400,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8180cc0e1,0x0,0x0,0x0,0x8516c41a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc220030152,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80280f00d4,0x4031078182,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc0300701c2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80202a1392,0x42a0020153,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc220030152,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc002070b30,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80280f00d4,0x4070070183,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc220030152,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc002070b30,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80280f00d4,0x4070070183,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x61172186,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x208512c65,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30559143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x183ac8a1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101819c8e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30559143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201fb3d7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10489960a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe0200303d0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8020451346,0x4061072182,0x0,0xe0200303d0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc004070672,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80202a1392,0x4070070183,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5117418a,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30559143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10401963ae,0x0,0x403a67a3,0x0,0x0,0x0,0x0,0x0,0x481f64a5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2801a0d5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200413d678,0x0,0x0,0x441f662a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2117b196,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4307610c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x428b620d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1855c861,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4183648e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5117418a,0x0,0x0,0x88500c41a2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x88080c44f4,0x0,0x0,0x0,0x0,0x8041454506,0x0,0x0,0x0,0x8c00c450f,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4307610c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x508b408b,0x100019ebfe,0x0,0x0,0x0,0x0,0x801ecf5f,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2c0100509c,0x0,0x0,0x0,0x24081240f5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x204113458c,0x0,0x0,0x41116588a,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x801ecf5f,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8306c91c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30559143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1070d923,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x188bc8c1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x201fb3d7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2d000010bd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2420501245,0x0,0x21401106ad,0x0,0x0,0x50414123a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x82200b1156,0x0,0x82400b0526,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81000d1eb6,0x0,0x0,0x0,0x0,0x0,0x201133d1e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa0400347a4,0x0,0x0,0x0,0xa4000252f4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8004455662,0x0,0x220113151c,0x0,0x0,0x0,0x55ff67,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x62af230,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1b2470,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xca0e4005,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c012470d,0x0,0x0,0x2881a0c55,0x483a64a1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2202221131,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x228012055d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20403247a1,0x0,0x0,0x0,0x2083a2c31,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14401062ae,0x0,0x0,0x160010287e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9000284bb2,0x0,0x4083268b1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc042070320,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc008070cf0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800a0f4834,0x4202032939,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x50480120a0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x500201ab38,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400822acb1,0x0,0x100889e8c4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc8100401e2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc003070910,0x0,0x0,0x8802445124,0x480220a131,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x188bc8c1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x84c0c642,0x100a89e83,0x170fd02,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100c19e07,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x11115988a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa0088344f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2003a3d33,0x0,0x0,0x0,0x0,0x2041b347a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40400727ab,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa20083157,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa00403567,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9400c04af,0x0,0x300381c33,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2401b252f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4201632d7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201fb3d7,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8706c018,0x0,0x0,0x6aaf200,0x1932c880,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10381980c,0x0,0xe45e020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe8be000,0x1983c880,0x0,0x4307610c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x63072104,0x0,0x14a0d0025,0x2281b2055,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x300111c19c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200b03c014,0x101c19c060,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x60100381e9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4016078028,0x202a038015,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x214201022d,0x2228130055,0x0,0x0,0x0,0x0,0x0,0x0,0x720f0101,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc008070cf0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8029070094,0x405107018a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8c1ec450,0x0,0xa1828006,0x0,0x0,0x0,0x0,0x1d17c000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x480104a59a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400522a412,0x0,0x0,0x82c0ca050,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820c0b0470,0x0,0x0,0x8061070186,0x0,0x0,0x0,0x0,0x0,0x25113010a,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c512460,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x428402045a,0x40502201a3,0x0,0x0,0x0,0x0,0x0,0x0,0xe03a0303,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2520b0129,0x28a0a0815,0x0,0x0,0x0,0x0,0x781f0081,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1120198296,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x121019096a,0x0,0x0,0x0,0x10a0d8835,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8101811c86,0x0,0x8000c15e46,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x51554102,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa020411344,0x0,0x0,0x0,0x0,0x8104451622,0x0,0x214111048c,0x0,0xa004035670,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80202a1392,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x541f402a,0x0,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c3a2430,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81280d0094,0x0,0x0,0x0,0x0,0x8062450304,0x0,0x8108450c24,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x68552005,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5183408a,0x0,0x0,0x201813c0e1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x204113458c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8854cc45,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc0480704a0,0x0,0x0,0x0,0x0,0x0,0x0,0xc208030c70,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc001070d92,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8008454c64,0x44180608e1,0x0,0xb001014194,0x0,0x0,0x9001414906,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9400004af6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8101051c96,0x0,0x0,0x120111291e,0x0,0x0,0x0,0x201fb3d7,0x401f67af,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14481060a4,0x0,0x1488104854,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1402006a3c,0x0,0x0,0x0,0x0,0x0,0x0,0x1208382830,0x0,0x4083268b1,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x81fecf5,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x801ecf5f,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x801ecf5f,0x0,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x8bfecf,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201883c0c1,0x0,0x200322d110,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa60e821,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x117fd9e,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x1001d9ebf,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x188bc8c1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x30559143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x55ff67,0x0,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x81fecf5,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f67af,0x117fd9e,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc800440562,0x0,0x0,0x0,0x0,0xc040600722,0x0,0x0,0x88700c0182,0x484104258a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1001d9ebf,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201fb3d7,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x106899208,0x0,0x0,0x30709103,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1402406a24,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1040c16206,0x0,0x401c07806,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x95088008b,0xa28082055,0x0,0x0,0x0,0x0,0x61832086,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4031078182,0x0,0x400707a018,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3c1f8040,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820c0b0470,0x0,0x0,0x8061070186,0x0,0x0,0x0,0x0,0x0,0x25113010a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x840c064070,0x0,0x0,0x0,0x80428b4204,0x0,0x0,0x0,0x0,0x45082408b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6042220321,0x0,0x0,0x44380600c1,0x2428320091,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8141050486,0x0,0x0,0x0,0x0,0x8028450044,0x0,0x0,0x0,0x0,0x0,0x0,0x149150484,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820c0b0470,0x0,0x0,0x8061070186,0x0,0x0,0x0,0x0,0x0,0x25113010a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820c0b0470,0x0,0x0,0x8061070186,0x0,0x0,0x0,0x0,0x0,0x25113010a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x214081068d,0x2220511145,0x0,0x0,0x0,0x0,0x0,0x0,0x70550103,0x0,0x0,0x0,0x0,0x0,0x3200510164,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x360010007c,0x0,0x0,0x0,0x7200010178,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x31401102ac,0x0,0x0,0x230111141c,0x120511201a,0x0,0x0,0x0,0x0,0x98002841b2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9a00080176,0x0,0x0,0x0,0x0,0x9c000040f6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9080084b56,0x88088844c4,0x0,0x0,0x18400861ae,0x0,0x0,0x0,0x55ff67,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x20ffb3d,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x117fd9e,0x400167aff,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x117fd9e,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x55ff67,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x401f67af,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001b3d7f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xe03a0303,0x15089008b,0x2303a1103,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2a00401565,0x0,0x0,0x0,0x0,0x2048c14405,0x0,0x842446125,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x40b066814,0x0,0x0,0x0,0x44382600c,0x0,0x0,0x0,0x0,0x0,0x0,0x4a8b6005,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc516440a,0x0,0x0,0x4c3a6420,0x0,0x0,0x0,0x0,0x0,0x20d322410,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb88a8041,0x0,0x0,0x0,0x0,0x0,0x70aa0083,0x0,0x18c388410,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x15115008a,0x0,0x0,0x0,0x0,0x0,0xc1544506,0x0,0x2b0500143,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8424c01242,0x8520a01282,0x0,0x0,0x0,0x0,0x0,0x0,0x8104e01602,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x221703102,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400167aff,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x201fb3d7,0x0,0x0,0x1001d9ebf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x101fd9eb,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x400007affb,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x20ffb3d,0x0,0x0,0x801ecf5f,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9c3ac000,0xd3064108,0x0,0x0,0x0,0x0,0x16aad000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x500381a808,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400b45a800,0x0,0x1028c1a044,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa109010494,0xa288020454,0x0,0x0,0x0,0x0,0x81a20c0214,0x0,0x2b8100041c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa083224110,0x0,0x0,0xa0502241a0,0x0,0x0,0x0,0x0,0x0,0x809c0e4040,0x0,0x20d1124108,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x90308900c2,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8044604622,0x0,0x0,0x1044386222,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb5168002,0x18a0c08046,0x0,0x0,0x0,0x0,0x2c182040e,0x0,0x1121818086,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa100a01680,0xaa80000554,0x0,0x0,0x0,0x0,0x81c0c00606,0x0,0x21c4100608,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3affb3,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x100019ebfe,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41ff67a,0x81fecf5,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8000cf5ff,0x0,0x100019ebfe,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x308510c018,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200660d220,0x101c38c020,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117059008,0x0,0x0,0x81c44c060,0x23c1b004,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x442c062050,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4041a22482,0x0,0x0,0x0,0x429322090,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8bfecf,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x400007affb,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb1488100a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x231701102,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x9a1448006,0x18a0c08046,0x0,0x0,0x0,0x0,0x6c182000e,0x0,0x2b83a004,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc50a04083,0x370510003,0x0,0x0,0x0,0x0,0x45c16402,0x0,0xc90c04043,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x117fd9e,0x0,0x41ff67a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000f5ff6,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x524701202,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xb1488100a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa140c10604,0xaa88000454,0x0,0x0,0x0,0x0,0x85a2040214,0x0,0x2b8100041c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa909000494,0xaa88000454,0x0,0x0,0x0,0x0,0x81c0c00606,0x0,0x21c4700600,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81fecf5,0x0,0x200013d7fd,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20ffb3d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2715101008,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xaf37e01000,0x7fd7800008,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xaf37e01000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def zset (i : Nat) := members ((zdata[i]?).getD 0)
def tset (i : Nat) := members ((tdata[i]?).getD 0)
def uset (i : Nat) := members ((udata[i]?).getD 0)
def hset (i : Nat) := members ((hdata[i]?).getD 0)
def aset (i : Nat) (f : V) := members ((adata[i*40+f.val]?).getD 0)
theorem nd0 : Data (zset 0) (tset 0) (uset 0) (hset 0) (aset 0) := verifies_sound (by decide +kernel)
theorem ng0 : Good 6 (zset 0) := .done _ _ _ _ _ nd0 (by decide +kernel)
theorem nd1 : Data (zset 1) (tset 1) (uset 1) (hset 1) (aset 1) := verifies_sound (by decide +kernel)
theorem ng1 : Good 6 (zset 1) := .done _ _ _ _ _ nd1 (by decide +kernel)
theorem nd2 : Data (zset 2) (tset 2) (uset 2) (hset 2) (aset 2) := verifies_sound (by decide +kernel)
theorem ng2 : Good 6 (zset 2) := .done _ _ _ _ _ nd2 (by decide +kernel)
theorem nd3 : Data (zset 3) (tset 3) (uset 3) (hset 3) (aset 3) := verifies_sound (by decide +kernel)
theorem ng3 : Good 6 (zset 3) := .done _ _ _ _ _ nd3 (by decide +kernel)
theorem nd4 : Data (zset 4) (tset 4) (uset 4) (hset 4) (aset 4) := verifies_sound (by decide +kernel)
theorem ng4 : Good 6 (zset 4) := .done _ _ _ _ _ nd4 (by decide +kernel)
theorem nd5 : Data (zset 5) (tset 5) (uset 5) (hset 5) (aset 5) := verifies_sound (by decide +kernel)
theorem ng5 : Good 6 (zset 5) := .done _ _ _ _ _ nd5 (by decide +kernel)
theorem nd6 : Data (zset 6) (tset 6) (uset 6) (hset 6) (aset 6) := verifies_sound (by decide +kernel)
theorem ng6 : Good 6 (zset 6) := .done _ _ _ _ _ nd6 (by decide +kernel)
theorem nd7 : Data (zset 7) (tset 7) (uset 7) (hset 7) (aset 7) := verifies_sound (by decide +kernel)
theorem ng7 : Good 6 (zset 7) := .done _ _ _ _ _ nd7 (by decide +kernel)
theorem nd8 : Data (zset 8) (tset 8) (uset 8) (hset 8) (aset 8) := verifies_sound (by decide +kernel)
theorem ng8 : Good 6 (zset 8) := .done _ _ _ _ _ nd8 (by decide +kernel)
theorem nd9 : Data (zset 9) (tset 9) (uset 9) (hset 9) (aset 9) := verifies_sound (by decide +kernel)
theorem ng9 : Good 6 (zset 9) := .done _ _ _ _ _ nd9 (by decide +kernel)
theorem nd10 : Data (zset 10) (tset 10) (uset 10) (hset 10) (aset 10) := verifies_sound (by decide +kernel)
theorem ng10 : Good 6 (zset 10) := .done _ _ _ _ _ nd10 (by decide +kernel)
theorem nd11 : Data (zset 11) (tset 11) (uset 11) (hset 11) (aset 11) := verifies_sound (by decide +kernel)
theorem ng11 : Good 6 (zset 11) := .done _ _ _ _ _ nd11 (by decide +kernel)
theorem nd12 : Data (zset 12) (tset 12) (uset 12) (hset 12) (aset 12) := verifies_sound (by decide +kernel)
theorem ng12 : Good 6 (zset 12) := .done _ _ _ _ _ nd12 (by decide +kernel)
theorem nd13 : Data (zset 13) (tset 13) (uset 13) (hset 13) (aset 13) := verifies_sound (by decide +kernel)
theorem ng13 : Good 6 (zset 13) := .done _ _ _ _ _ nd13 (by decide +kernel)
theorem nd14 : Data (zset 14) (tset 14) (uset 14) (hset 14) (aset 14) := verifies_sound (by decide +kernel)
theorem ng14 : Good 6 (zset 14) := .done _ _ _ _ _ nd14 (by decide +kernel)
theorem nd15 : Data (zset 15) (tset 15) (uset 15) (hset 15) (aset 15) := verifies_sound (by decide +kernel)
theorem ng15 : Good 6 (zset 15) := .done _ _ _ _ _ nd15 (by decide +kernel)
theorem nd16 : Data (zset 16) (tset 16) (uset 16) (hset 16) (aset 16) := verifies_sound (by decide +kernel)
theorem ng16 : Good 6 (zset 16) := .done _ _ _ _ _ nd16 (by decide +kernel)
theorem nd17 : Data (zset 17) (tset 17) (uset 17) (hset 17) (aset 17) := verifies_sound (by decide +kernel)
theorem ng17 : Good 6 (zset 17) := .done _ _ _ _ _ nd17 (by decide +kernel)
theorem nd18 : Data (zset 18) (tset 18) (uset 18) (hset 18) (aset 18) := verifies_sound (by decide +kernel)
theorem ng18 : Good 6 (zset 18) := by
  have eq : (zset 18).erase 22=zset 0 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd18 (by decide +kernel) (eq.symm ▸ ng0)
theorem nd19 : Data (zset 19) (tset 19) (uset 19) (hset 19) (aset 19) := verifies_sound (by decide +kernel)
theorem ng19 : Good 6 (zset 19) := by
  have eq : (zset 19).erase 21=zset 4 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd19 (by decide +kernel) (eq.symm ▸ ng4)
theorem nd20 : Data (zset 20) (tset 20) (uset 20) (hset 20) (aset 20) := verifies_sound (by decide +kernel)
theorem ng20 : Good 6 (zset 20) := by
  have eq : (zset 20).erase 24=zset 1 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd20 (by decide +kernel) (eq.symm ▸ ng1)
theorem nd21 : Data (zset 21) (tset 21) (uset 21) (hset 21) (aset 21) := verifies_sound (by decide +kernel)
theorem ng21 : Good 6 (zset 21) := by
  have eq : (zset 21).erase 24=zset 2 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd21 (by decide +kernel) (eq.symm ▸ ng2)
theorem nd22 : Data (zset 22) (tset 22) (uset 22) (hset 22) (aset 22) := verifies_sound (by decide +kernel)
theorem ng22 : Good 6 (zset 22) := .done _ _ _ _ _ nd22 (by decide +kernel)
theorem nd23 : Data (zset 23) (tset 23) (uset 23) (hset 23) (aset 23) := verifies_sound (by decide +kernel)
theorem ng23 : Good 6 (zset 23) := by
  have eq : (zset 23).erase 21=zset 5 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd23 (by decide +kernel) (eq.symm ▸ ng5)
theorem nd24 : Data (zset 24) (tset 24) (uset 24) (hset 24) (aset 24) := verifies_sound (by decide +kernel)
theorem ng24 : Good 6 (zset 24) := by
  have eq : (zset 24).erase 21=zset 8 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd24 (by decide +kernel) (eq.symm ▸ ng8)
theorem nd25 : Data (zset 25) (tset 25) (uset 25) (hset 25) (aset 25) := verifies_sound (by decide +kernel)
theorem ng25 : Good 6 (zset 25) := by
  have eq : (zset 25).erase 22=zset 6 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd25 (by decide +kernel) (eq.symm ▸ ng6)
theorem nd26 : Data (zset 26) (tset 26) (uset 26) (hset 26) (aset 26) := verifies_sound (by decide +kernel)
theorem ng26 : Good 6 (zset 26) := by
  have eq : (zset 26).erase 22=zset 7 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd26 (by decide +kernel) (eq.symm ▸ ng7)
theorem nd27 : Data (zset 27) (tset 27) (uset 27) (hset 27) (aset 27) := verifies_sound (by decide +kernel)
theorem ng27 : Good 6 (zset 27) := by
  have eq : (zset 27).erase 25=zset 3 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd27 (by decide +kernel) (eq.symm ▸ ng3)
theorem nd28 : Data (zset 28) (tset 28) (uset 28) (hset 28) (aset 28) := verifies_sound (by decide +kernel)
theorem ng28 : Good 6 (zset 28) := by
  have eq : (zset 28).erase 22=zset 10 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd28 (by decide +kernel) (eq.symm ▸ ng10)
theorem nd29 : Data (zset 29) (tset 29) (uset 29) (hset 29) (aset 29) := verifies_sound (by decide +kernel)
theorem ng29 : Good 6 (zset 29) := by
  have eq : (zset 29).erase 27=zset 9 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd29 (by decide +kernel) (eq.symm ▸ ng9)
theorem nd30 : Data (zset 30) (tset 30) (uset 30) (hset 30) (aset 30) := verifies_sound (by decide +kernel)
theorem ng30 : Good 6 (zset 30) := .done _ _ _ _ _ nd30 (by decide +kernel)
theorem nd31 : Data (zset 31) (tset 31) (uset 31) (hset 31) (aset 31) := verifies_sound (by decide +kernel)
theorem ng31 : Good 6 (zset 31) := by
  have eq : (zset 31).erase 23=zset 11 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd31 (by decide +kernel) (eq.symm ▸ ng11)
theorem nd32 : Data (zset 32) (tset 32) (uset 32) (hset 32) (aset 32) := verifies_sound (by decide +kernel)
theorem ng32 : Good 6 (zset 32) := by
  have eq : (zset 32).erase 23=zset 12 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd32 (by decide +kernel) (eq.symm ▸ ng12)
theorem nd33 : Data (zset 33) (tset 33) (uset 33) (hset 33) (aset 33) := verifies_sound (by decide +kernel)
theorem ng33 : Good 6 (zset 33) := .done _ _ _ _ _ nd33 (by decide +kernel)
theorem nd34 : Data (zset 34) (tset 34) (uset 34) (hset 34) (aset 34) := verifies_sound (by decide +kernel)
theorem ng34 : Good 6 (zset 34) := .done _ _ _ _ _ nd34 (by decide +kernel)
theorem nd35 : Data (zset 35) (tset 35) (uset 35) (hset 35) (aset 35) := verifies_sound (by decide +kernel)
theorem ng35 : Good 6 (zset 35) := .done _ _ _ _ _ nd35 (by decide +kernel)
theorem nd36 : Data (zset 36) (tset 36) (uset 36) (hset 36) (aset 36) := verifies_sound (by decide +kernel)
theorem ng36 : Good 6 (zset 36) := .done _ _ _ _ _ nd36 (by decide +kernel)
theorem nd37 : Data (zset 37) (tset 37) (uset 37) (hset 37) (aset 37) := verifies_sound (by decide +kernel)
theorem ng37 : Good 6 (zset 37) := .done _ _ _ _ _ nd37 (by decide +kernel)
theorem nd38 : Data (zset 38) (tset 38) (uset 38) (hset 38) (aset 38) := verifies_sound (by decide +kernel)
theorem ng38 : Good 6 (zset 38) := .done _ _ _ _ _ nd38 (by decide +kernel)
theorem nd39 : Data (zset 39) (tset 39) (uset 39) (hset 39) (aset 39) := verifies_sound (by decide +kernel)
theorem ng39 : Good 6 (zset 39) := by
  have eq : (zset 39).erase 25=zset 13 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd39 (by decide +kernel) (eq.symm ▸ ng13)
theorem nd40 : Data (zset 40) (tset 40) (uset 40) (hset 40) (aset 40) := verifies_sound (by decide +kernel)
theorem ng40 : Good 6 (zset 40) := .done _ _ _ _ _ nd40 (by decide +kernel)
theorem nd41 : Data (zset 41) (tset 41) (uset 41) (hset 41) (aset 41) := verifies_sound (by decide +kernel)
theorem ng41 : Good 6 (zset 41) := .done _ _ _ _ _ nd41 (by decide +kernel)
theorem nd42 : Data (zset 42) (tset 42) (uset 42) (hset 42) (aset 42) := verifies_sound (by decide +kernel)
theorem ng42 : Good 6 (zset 42) := by
  have eq : (zset 42).erase 26=zset 14 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd42 (by decide +kernel) (eq.symm ▸ ng14)
theorem nd43 : Data (zset 43) (tset 43) (uset 43) (hset 43) (aset 43) := verifies_sound (by decide +kernel)
theorem ng43 : Good 6 (zset 43) := .done _ _ _ _ _ nd43 (by decide +kernel)
theorem nd44 : Data (zset 44) (tset 44) (uset 44) (hset 44) (aset 44) := verifies_sound (by decide +kernel)
theorem ng44 : Good 6 (zset 44) := by
  have eq : (zset 44).erase 22=zset 15 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd44 (by decide +kernel) (eq.symm ▸ ng15)
theorem nd45 : Data (zset 45) (tset 45) (uset 45) (hset 45) (aset 45) := verifies_sound (by decide +kernel)
theorem ng45 : Good 6 (zset 45) := .done _ _ _ _ _ nd45 (by decide +kernel)
theorem nd46 : Data (zset 46) (tset 46) (uset 46) (hset 46) (aset 46) := verifies_sound (by decide +kernel)
theorem ng46 : Good 6 (zset 46) := by
  have eq : (zset 46).erase 26=zset 16 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd46 (by decide +kernel) (eq.symm ▸ ng16)
theorem nd47 : Data (zset 47) (tset 47) (uset 47) (hset 47) (aset 47) := verifies_sound (by decide +kernel)
theorem ng47 : Good 6 (zset 47) := .done _ _ _ _ _ nd47 (by decide +kernel)
theorem nd48 : Data (zset 48) (tset 48) (uset 48) (hset 48) (aset 48) := verifies_sound (by decide +kernel)
theorem ng48 : Good 6 (zset 48) := by
  have eq : (zset 48).erase 27=zset 17 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd48 (by decide +kernel) (eq.symm ▸ ng17)
theorem nd49 : Data (zset 49) (tset 49) (uset 49) (hset 49) (aset 49) := verifies_sound (by decide +kernel)
theorem ng49 : Good 6 (zset 49) := .done _ _ _ _ _ nd49 (by decide +kernel)
theorem nd50 : Data (zset 50) (tset 50) (uset 50) (hset 50) (aset 50) := verifies_sound (by decide +kernel)
theorem ng50 : Good 6 (zset 50) := .done _ _ _ _ _ nd50 (by decide +kernel)
theorem nd51 : Data (zset 51) (tset 51) (uset 51) (hset 51) (aset 51) := verifies_sound (by decide +kernel)
theorem ng51 : Good 6 (zset 51) := .done _ _ _ _ _ nd51 (by decide +kernel)
theorem nd52 : Data (zset 52) (tset 52) (uset 52) (hset 52) (aset 52) := verifies_sound (by decide +kernel)
theorem ng52 : Good 6 (zset 52) := .done _ _ _ _ _ nd52 (by decide +kernel)
theorem nd53 : Data (zset 53) (tset 53) (uset 53) (hset 53) (aset 53) := verifies_sound (by decide +kernel)
theorem ng53 : Good 6 (zset 53) := .done _ _ _ _ _ nd53 (by decide +kernel)
theorem nd54 : Data (zset 54) (tset 54) (uset 54) (hset 54) (aset 54) := verifies_sound (by decide +kernel)
theorem ng54 : Good 6 (zset 54) := by
  have eq : (zset 54).erase 12=zset 18 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd54 (by decide +kernel) (eq.symm ▸ ng18)
theorem nd55 : Data (zset 55) (tset 55) (uset 55) (hset 55) (aset 55) := verifies_sound (by decide +kernel)
theorem ng55 : Good 6 (zset 55) := by
  have eq : (zset 55).erase 12=zset 19 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd55 (by decide +kernel) (eq.symm ▸ ng19)
theorem nd56 : Data (zset 56) (tset 56) (uset 56) (hset 56) (aset 56) := verifies_sound (by decide +kernel)
theorem ng56 : Good 6 (zset 56) := by
  have eq : (zset 56).erase 22=zset 20 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd56 (by decide +kernel) (eq.symm ▸ ng20)
theorem nd57 : Data (zset 57) (tset 57) (uset 57) (hset 57) (aset 57) := verifies_sound (by decide +kernel)
theorem ng57 : Good 6 (zset 57) := by
  have eq : (zset 57).erase 12=zset 25 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd57 (by decide +kernel) (eq.symm ▸ ng25)
theorem nd58 : Data (zset 58) (tset 58) (uset 58) (hset 58) (aset 58) := verifies_sound (by decide +kernel)
theorem ng58 : Good 6 (zset 58) := by
  have eq : (zset 58).erase 22=zset 23 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd58 (by decide +kernel) (eq.symm ▸ ng23)
theorem nd59 : Data (zset 59) (tset 59) (uset 59) (hset 59) (aset 59) := verifies_sound (by decide +kernel)
theorem ng59 : Good 6 (zset 59) := by
  have eq : (zset 59).erase 23=zset 27 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd59 (by decide +kernel) (eq.symm ▸ ng27)
theorem nd60 : Data (zset 60) (tset 60) (uset 60) (hset 60) (aset 60) := verifies_sound (by decide +kernel)
theorem ng60 : Good 6 (zset 60) := by
  have eq : (zset 60).erase 21=zset 28 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd60 (by decide +kernel) (eq.symm ▸ ng28)
theorem nd61 : Data (zset 61) (tset 61) (uset 61) (hset 61) (aset 61) := verifies_sound (by decide +kernel)
theorem ng61 : Good 6 (zset 61) := by
  have eq : (zset 61).erase 26=zset 20 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd61 (by decide +kernel) (eq.symm ▸ ng20)
theorem nd62 : Data (zset 62) (tset 62) (uset 62) (hset 62) (aset 62) := verifies_sound (by decide +kernel)
theorem ng62 : Good 6 (zset 62) := by
  have eq : (zset 62).erase 27=zset 22 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd62 (by decide +kernel) (eq.symm ▸ ng22)
theorem nd63 : Data (zset 63) (tset 63) (uset 63) (hset 63) (aset 63) := verifies_sound (by decide +kernel)
theorem ng63 : Good 6 (zset 63) := by
  have eq : (zset 63).erase 27=zset 24 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd63 (by decide +kernel) (eq.symm ▸ ng24)
theorem nd64 : Data (zset 64) (tset 64) (uset 64) (hset 64) (aset 64) := verifies_sound (by decide +kernel)
theorem ng64 : Good 6 (zset 64) := by
  have eq : (zset 64).erase 27=zset 26 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd64 (by decide +kernel) (eq.symm ▸ ng26)
theorem nd65 : Data (zset 65) (tset 65) (uset 65) (hset 65) (aset 65) := verifies_sound (by decide +kernel)
theorem ng65 : Good 6 (zset 65) := by
  have eq : (zset 65).erase 23=zset 30 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd65 (by decide +kernel) (eq.symm ▸ ng30)
theorem nd66 : Data (zset 66) (tset 66) (uset 66) (hset 66) (aset 66) := verifies_sound (by decide +kernel)
theorem ng66 : Good 6 (zset 66) := by
  have eq : (zset 66).erase 28=zset 21 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd66 (by decide +kernel) (eq.symm ▸ ng21)
theorem nd67 : Data (zset 67) (tset 67) (uset 67) (hset 67) (aset 67) := verifies_sound (by decide +kernel)
theorem ng67 : Good 6 (zset 67) := by
  have eq : (zset 67).erase 28=zset 29 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd67 (by decide +kernel) (eq.symm ▸ ng29)
theorem nd68 : Data (zset 68) (tset 68) (uset 68) (hset 68) (aset 68) := verifies_sound (by decide +kernel)
theorem ng68 : Good 6 (zset 68) := by
  have eq : (zset 68).erase 21=zset 31 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd68 (by decide +kernel) (eq.symm ▸ ng31)
theorem nd69 : Data (zset 69) (tset 69) (uset 69) (hset 69) (aset 69) := verifies_sound (by decide +kernel)
theorem ng69 : Good 6 (zset 69) := by
  have eq : (zset 69).erase 21=zset 32 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd69 (by decide +kernel) (eq.symm ▸ ng32)
theorem nd70 : Data (zset 70) (tset 70) (uset 70) (hset 70) (aset 70) := verifies_sound (by decide +kernel)
theorem ng70 : Good 6 (zset 70) := by
  have eq : (zset 70).erase 21=zset 33 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd70 (by decide +kernel) (eq.symm ▸ ng33)
theorem nd71 : Data (zset 71) (tset 71) (uset 71) (hset 71) (aset 71) := verifies_sound (by decide +kernel)
theorem ng71 : Good 6 (zset 71) := by
  have eq : (zset 71).erase 21=zset 34 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd71 (by decide +kernel) (eq.symm ▸ ng34)
theorem nd72 : Data (zset 72) (tset 72) (uset 72) (hset 72) (aset 72) := verifies_sound (by decide +kernel)
theorem ng72 : Good 6 (zset 72) := by
  have eq : (zset 72).erase 21=zset 35 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd72 (by decide +kernel) (eq.symm ▸ ng35)
theorem nd73 : Data (zset 73) (tset 73) (uset 73) (hset 73) (aset 73) := verifies_sound (by decide +kernel)
theorem ng73 : Good 6 (zset 73) := by
  have eq : (zset 73).erase 21=zset 36 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd73 (by decide +kernel) (eq.symm ▸ ng36)
theorem nd74 : Data (zset 74) (tset 74) (uset 74) (hset 74) (aset 74) := verifies_sound (by decide +kernel)
theorem ng74 : Good 6 (zset 74) := .done _ _ _ _ _ nd74 (by decide +kernel)
theorem nd75 : Data (zset 75) (tset 75) (uset 75) (hset 75) (aset 75) := verifies_sound (by decide +kernel)
theorem ng75 : Good 6 (zset 75) := by
  have eq : (zset 75).erase 23=zset 39 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd75 (by decide +kernel) (eq.symm ▸ ng39)
theorem nd76 : Data (zset 76) (tset 76) (uset 76) (hset 76) (aset 76) := verifies_sound (by decide +kernel)
theorem ng76 : Good 6 (zset 76) := by
  have eq : (zset 76).erase 11=zset 40 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd76 (by decide +kernel) (eq.symm ▸ ng40)
theorem nd77 : Data (zset 77) (tset 77) (uset 77) (hset 77) (aset 77) := verifies_sound (by decide +kernel)
theorem ng77 : Good 6 (zset 77) := by
  have eq : (zset 77).erase 19=zset 41 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd77 (by decide +kernel) (eq.symm ▸ ng41)
theorem nd78 : Data (zset 78) (tset 78) (uset 78) (hset 78) (aset 78) := verifies_sound (by decide +kernel)
theorem ng78 : Good 6 (zset 78) := by
  have eq : (zset 78).erase 26=zset 43 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd78 (by decide +kernel) (eq.symm ▸ ng43)
theorem nd79 : Data (zset 79) (tset 79) (uset 79) (hset 79) (aset 79) := verifies_sound (by decide +kernel)
theorem ng79 : Good 6 (zset 79) := by
  have eq : (zset 79).erase 24=zset 45 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd79 (by decide +kernel) (eq.symm ▸ ng45)
theorem nd80 : Data (zset 80) (tset 80) (uset 80) (hset 80) (aset 80) := verifies_sound (by decide +kernel)
theorem ng80 : Good 6 (zset 80) := by
  have eq : (zset 80).erase 26=zset 44 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd80 (by decide +kernel) (eq.symm ▸ ng44)
theorem nd81 : Data (zset 81) (tset 81) (uset 81) (hset 81) (aset 81) := verifies_sound (by decide +kernel)
theorem ng81 : Good 6 (zset 81) := by
  have eq : (zset 81).erase 18=zset 46 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 nd81 (by decide +kernel) (eq.symm ▸ ng46)
theorem nd82 : Data (zset 82) (tset 82) (uset 82) (hset 82) (aset 82) := verifies_sound (by decide +kernel)
theorem ng82 : Good 6 (zset 82) := .done _ _ _ _ _ nd82 (by decide +kernel)
theorem nd83 : Data (zset 83) (tset 83) (uset 83) (hset 83) (aset 83) := verifies_sound (by decide +kernel)
theorem ng83 : Good 6 (zset 83) := .done _ _ _ _ _ nd83 (by decide +kernel)
theorem nd84 : Data (zset 84) (tset 84) (uset 84) (hset 84) (aset 84) := verifies_sound (by decide +kernel)
theorem ng84 : Good 6 (zset 84) := by
  have eq : (zset 84).erase 17=zset 48 := by decide +kernel
  exact .pivot _ _ _ _ _ 17 nd84 (by decide +kernel) (eq.symm ▸ ng48)
theorem nd85 : Data (zset 85) (tset 85) (uset 85) (hset 85) (aset 85) := verifies_sound (by decide +kernel)
theorem ng85 : Good 6 (zset 85) := .done _ _ _ _ _ nd85 (by decide +kernel)
theorem nd86 : Data (zset 86) (tset 86) (uset 86) (hset 86) (aset 86) := verifies_sound (by decide +kernel)
theorem ng86 : Good 6 (zset 86) := by
  have eq : (zset 86).erase 34=zset 42 := by decide +kernel
  exact .pivot _ _ _ _ _ 34 nd86 (by decide +kernel) (eq.symm ▸ ng42)
theorem nd87 : Data (zset 87) (tset 87) (uset 87) (hset 87) (aset 87) := verifies_sound (by decide +kernel)
theorem ng87 : Good 6 (zset 87) := .done _ _ _ _ _ nd87 (by decide +kernel)
theorem nd88 : Data (zset 88) (tset 88) (uset 88) (hset 88) (aset 88) := verifies_sound (by decide +kernel)
theorem ng88 : Good 6 (zset 88) := .done _ _ _ _ _ nd88 (by decide +kernel)
theorem nd89 : Data (zset 89) (tset 89) (uset 89) (hset 89) (aset 89) := verifies_sound (by decide +kernel)
theorem ng89 : Good 6 (zset 89) := .done _ _ _ _ _ nd89 (by decide +kernel)
theorem nd90 : Data (zset 90) (tset 90) (uset 90) (hset 90) (aset 90) := verifies_sound (by decide +kernel)
theorem ng90 : Good 6 (zset 90) := .done _ _ _ _ _ nd90 (by decide +kernel)
theorem nd91 : Data (zset 91) (tset 91) (uset 91) (hset 91) (aset 91) := verifies_sound (by decide +kernel)
theorem ng91 : Good 6 (zset 91) := .done _ _ _ _ _ nd91 (by decide +kernel)
theorem nd92 : Data (zset 92) (tset 92) (uset 92) (hset 92) (aset 92) := verifies_sound (by decide +kernel)
theorem ng92 : Good 6 (zset 92) := .done _ _ _ _ _ nd92 (by decide +kernel)
theorem nd93 : Data (zset 93) (tset 93) (uset 93) (hset 93) (aset 93) := verifies_sound (by decide +kernel)
theorem ng93 : Good 6 (zset 93) := .done _ _ _ _ _ nd93 (by decide +kernel)
theorem nd94 : Data (zset 94) (tset 94) (uset 94) (hset 94) (aset 94) := verifies_sound (by decide +kernel)
theorem ng94 : Good 6 (zset 94) := .done _ _ _ _ _ nd94 (by decide +kernel)
theorem nd95 : Data (zset 95) (tset 95) (uset 95) (hset 95) (aset 95) := verifies_sound (by decide +kernel)
theorem ng95 : Good 6 (zset 95) := .done _ _ _ _ _ nd95 (by decide +kernel)
theorem nd96 : Data (zset 96) (tset 96) (uset 96) (hset 96) (aset 96) := verifies_sound (by decide +kernel)
theorem ng96 : Good 6 (zset 96) := by
  have eq : (zset 96).erase 25=zset 49 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd96 (by decide +kernel) (eq.symm ▸ ng49)
theorem nd97 : Data (zset 97) (tset 97) (uset 97) (hset 97) (aset 97) := verifies_sound (by decide +kernel)
theorem ng97 : Good 6 (zset 97) := .done _ _ _ _ _ nd97 (by decide +kernel)
theorem nd98 : Data (zset 98) (tset 98) (uset 98) (hset 98) (aset 98) := verifies_sound (by decide +kernel)
theorem ng98 : Good 6 (zset 98) := .done _ _ _ _ _ nd98 (by decide +kernel)
theorem nd99 : Data (zset 99) (tset 99) (uset 99) (hset 99) (aset 99) := verifies_sound (by decide +kernel)
theorem ng99 : Good 6 (zset 99) := .done _ _ _ _ _ nd99 (by decide +kernel)
theorem nd100 : Data (zset 100) (tset 100) (uset 100) (hset 100) (aset 100) := verifies_sound (by decide +kernel)
theorem ng100 : Good 6 (zset 100) := .done _ _ _ _ _ nd100 (by decide +kernel)
theorem nd101 : Data (zset 101) (tset 101) (uset 101) (hset 101) (aset 101) := verifies_sound (by decide +kernel)
theorem ng101 : Good 6 (zset 101) := .done _ _ _ _ _ nd101 (by decide +kernel)
theorem nd102 : Data (zset 102) (tset 102) (uset 102) (hset 102) (aset 102) := verifies_sound (by decide +kernel)
theorem ng102 : Good 6 (zset 102) := by
  have eq : (zset 102).erase 2=zset 50 := by decide +kernel
  exact .pivot _ _ _ _ _ 2 nd102 (by decide +kernel) (eq.symm ▸ ng50)
theorem nd103 : Data (zset 103) (tset 103) (uset 103) (hset 103) (aset 103) := verifies_sound (by decide +kernel)
theorem ng103 : Good 6 (zset 103) := by
  have eq : (zset 103).erase 10=zset 51 := by decide +kernel
  exact .pivot _ _ _ _ _ 10 nd103 (by decide +kernel) (eq.symm ▸ ng51)
theorem nd104 : Data (zset 104) (tset 104) (uset 104) (hset 104) (aset 104) := verifies_sound (by decide +kernel)
theorem ng104 : Good 6 (zset 104) := by
  have eq : (zset 104).erase 5=zset 52 := by decide +kernel
  exact .pivot _ _ _ _ _ 5 nd104 (by decide +kernel) (eq.symm ▸ ng52)
theorem nd105 : Data (zset 105) (tset 105) (uset 105) (hset 105) (aset 105) := verifies_sound (by decide +kernel)
theorem ng105 : Good 6 (zset 105) := by
  have eq : (zset 105).erase 9=zset 53 := by decide +kernel
  exact .pivot _ _ _ _ _ 9 nd105 (by decide +kernel) (eq.symm ▸ ng53)
theorem nd106 : Data (zset 106) (tset 106) (uset 106) (hset 106) (aset 106) := verifies_sound (by decide +kernel)
theorem ng106 : Good 6 (zset 106) := by
  have eq : (zset 106).erase 10=zset 54 := by decide +kernel
  exact .pivot _ _ _ _ _ 10 nd106 (by decide +kernel) (eq.symm ▸ ng54)
theorem nd107 : Data (zset 107) (tset 107) (uset 107) (hset 107) (aset 107) := verifies_sound (by decide +kernel)
theorem ng107 : Good 6 (zset 107) := by
  have eq : (zset 107).erase 14=zset 55 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd107 (by decide +kernel) (eq.symm ▸ ng55)
theorem nd108 : Data (zset 108) (tset 108) (uset 108) (hset 108) (aset 108) := verifies_sound (by decide +kernel)
theorem ng108 : Good 6 (zset 108) := by
  have eq : (zset 108).erase 14=zset 56 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd108 (by decide +kernel) (eq.symm ▸ ng56)
theorem nd109 : Data (zset 109) (tset 109) (uset 109) (hset 109) (aset 109) := verifies_sound (by decide +kernel)
theorem ng109 : Good 6 (zset 109) := .done _ _ _ _ _ nd109 (by decide +kernel)
theorem nd110 : Data (zset 110) (tset 110) (uset 110) (hset 110) (aset 110) := verifies_sound (by decide +kernel)
theorem ng110 : Good 6 (zset 110) := .done _ _ _ _ _ nd110 (by decide +kernel)
theorem nd111 : Data (zset 111) (tset 111) (uset 111) (hset 111) (aset 111) := verifies_sound (by decide +kernel)
theorem ng111 : Good 6 (zset 111) := by
  have eq : (zset 111).erase 16=zset 57 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 nd111 (by decide +kernel) (eq.symm ▸ ng57)
theorem nd112 : Data (zset 112) (tset 112) (uset 112) (hset 112) (aset 112) := verifies_sound (by decide +kernel)
theorem ng112 : Good 6 (zset 112) := by
  have eq : (zset 112).erase 14=zset 58 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd112 (by decide +kernel) (eq.symm ▸ ng58)
theorem nd113 : Data (zset 113) (tset 113) (uset 113) (hset 113) (aset 113) := verifies_sound (by decide +kernel)
theorem ng113 : Good 6 (zset 113) := .done _ _ _ _ _ nd113 (by decide +kernel)
theorem nd114 : Data (zset 114) (tset 114) (uset 114) (hset 114) (aset 114) := verifies_sound (by decide +kernel)
theorem ng114 : Good 6 (zset 114) := .done _ _ _ _ _ nd114 (by decide +kernel)
theorem nd115 : Data (zset 115) (tset 115) (uset 115) (hset 115) (aset 115) := verifies_sound (by decide +kernel)
theorem ng115 : Good 6 (zset 115) := by
  have eq : (zset 115).erase 14=zset 59 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd115 (by decide +kernel) (eq.symm ▸ ng59)
theorem nd116 : Data (zset 116) (tset 116) (uset 116) (hset 116) (aset 116) := verifies_sound (by decide +kernel)
theorem ng116 : Good 6 (zset 116) := .done _ _ _ _ _ nd116 (by decide +kernel)
theorem nd117 : Data (zset 117) (tset 117) (uset 117) (hset 117) (aset 117) := verifies_sound (by decide +kernel)
theorem ng117 : Good 6 (zset 117) := by
  have eq : (zset 117).erase 14=zset 60 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd117 (by decide +kernel) (eq.symm ▸ ng60)
theorem nd118 : Data (zset 118) (tset 118) (uset 118) (hset 118) (aset 118) := verifies_sound (by decide +kernel)
theorem ng118 : Good 6 (zset 118) := by
  have eq : (zset 118).erase 14=zset 61 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd118 (by decide +kernel) (eq.symm ▸ ng61)
theorem nd119 : Data (zset 119) (tset 119) (uset 119) (hset 119) (aset 119) := verifies_sound (by decide +kernel)
theorem ng119 : Good 6 (zset 119) := .done _ _ _ _ _ nd119 (by decide +kernel)
theorem nd120 : Data (zset 120) (tset 120) (uset 120) (hset 120) (aset 120) := verifies_sound (by decide +kernel)
theorem ng120 : Good 6 (zset 120) := .done _ _ _ _ _ nd120 (by decide +kernel)
theorem nd121 : Data (zset 121) (tset 121) (uset 121) (hset 121) (aset 121) := verifies_sound (by decide +kernel)
theorem ng121 : Good 6 (zset 121) := .done _ _ _ _ _ nd121 (by decide +kernel)
theorem nd122 : Data (zset 122) (tset 122) (uset 122) (hset 122) (aset 122) := verifies_sound (by decide +kernel)
theorem ng122 : Good 6 (zset 122) := .done _ _ _ _ _ nd122 (by decide +kernel)
theorem nd123 : Data (zset 123) (tset 123) (uset 123) (hset 123) (aset 123) := verifies_sound (by decide +kernel)
theorem ng123 : Good 6 (zset 123) := by
  have eq : (zset 123).erase 17=zset 62 := by decide +kernel
  exact .pivot _ _ _ _ _ 17 nd123 (by decide +kernel) (eq.symm ▸ ng62)
theorem nd124 : Data (zset 124) (tset 124) (uset 124) (hset 124) (aset 124) := verifies_sound (by decide +kernel)
theorem ng124 : Good 6 (zset 124) := .done _ _ _ _ _ nd124 (by decide +kernel)
theorem nd125 : Data (zset 125) (tset 125) (uset 125) (hset 125) (aset 125) := verifies_sound (by decide +kernel)
theorem ng125 : Good 6 (zset 125) := by
  have eq : (zset 125).erase 14=zset 63 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd125 (by decide +kernel) (eq.symm ▸ ng63)
theorem nd126 : Data (zset 126) (tset 126) (uset 126) (hset 126) (aset 126) := verifies_sound (by decide +kernel)
theorem ng126 : Good 6 (zset 126) := by
  have eq : (zset 126).erase 14=zset 64 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd126 (by decide +kernel) (eq.symm ▸ ng64)
theorem nd127 : Data (zset 127) (tset 127) (uset 127) (hset 127) (aset 127) := verifies_sound (by decide +kernel)
theorem ng127 : Good 6 (zset 127) := .done _ _ _ _ _ nd127 (by decide +kernel)
theorem nd128 : Data (zset 128) (tset 128) (uset 128) (hset 128) (aset 128) := verifies_sound (by decide +kernel)
theorem ng128 : Good 6 (zset 128) := .done _ _ _ _ _ nd128 (by decide +kernel)
theorem nd129 : Data (zset 129) (tset 129) (uset 129) (hset 129) (aset 129) := verifies_sound (by decide +kernel)
theorem ng129 : Good 6 (zset 129) := .done _ _ _ _ _ nd129 (by decide +kernel)
theorem nd130 : Data (zset 130) (tset 130) (uset 130) (hset 130) (aset 130) := verifies_sound (by decide +kernel)
theorem ng130 : Good 6 (zset 130) := .done _ _ _ _ _ nd130 (by decide +kernel)
theorem nd131 : Data (zset 131) (tset 131) (uset 131) (hset 131) (aset 131) := verifies_sound (by decide +kernel)
theorem ng131 : Good 6 (zset 131) := .done _ _ _ _ _ nd131 (by decide +kernel)
theorem nd132 : Data (zset 132) (tset 132) (uset 132) (hset 132) (aset 132) := verifies_sound (by decide +kernel)
theorem ng132 : Good 6 (zset 132) := .done _ _ _ _ _ nd132 (by decide +kernel)
theorem nd133 : Data (zset 133) (tset 133) (uset 133) (hset 133) (aset 133) := verifies_sound (by decide +kernel)
theorem ng133 : Good 6 (zset 133) := .done _ _ _ _ _ nd133 (by decide +kernel)
theorem nd134 : Data (zset 134) (tset 134) (uset 134) (hset 134) (aset 134) := verifies_sound (by decide +kernel)
theorem ng134 : Good 6 (zset 134) := .done _ _ _ _ _ nd134 (by decide +kernel)
theorem nd135 : Data (zset 135) (tset 135) (uset 135) (hset 135) (aset 135) := verifies_sound (by decide +kernel)
theorem ng135 : Good 6 (zset 135) := by
  have eq : (zset 135).erase 26=zset 65 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd135 (by decide +kernel) (eq.symm ▸ ng65)
theorem nd136 : Data (zset 136) (tset 136) (uset 136) (hset 136) (aset 136) := verifies_sound (by decide +kernel)
theorem ng136 : Good 6 (zset 136) := by
  have eq : (zset 136).erase 26=zset 66 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd136 (by decide +kernel) (eq.symm ▸ ng66)
theorem nd137 : Data (zset 137) (tset 137) (uset 137) (hset 137) (aset 137) := verifies_sound (by decide +kernel)
theorem ng137 : Good 6 (zset 137) := .done _ _ _ _ _ nd137 (by decide +kernel)
theorem nd138 : Data (zset 138) (tset 138) (uset 138) (hset 138) (aset 138) := verifies_sound (by decide +kernel)
theorem ng138 : Good 6 (zset 138) := .done _ _ _ _ _ nd138 (by decide +kernel)
theorem nd139 : Data (zset 139) (tset 139) (uset 139) (hset 139) (aset 139) := verifies_sound (by decide +kernel)
theorem ng139 : Good 6 (zset 139) := .done _ _ _ _ _ nd139 (by decide +kernel)
theorem nd140 : Data (zset 140) (tset 140) (uset 140) (hset 140) (aset 140) := verifies_sound (by decide +kernel)
theorem ng140 : Good 6 (zset 140) := .done _ _ _ _ _ nd140 (by decide +kernel)
theorem nd141 : Data (zset 141) (tset 141) (uset 141) (hset 141) (aset 141) := verifies_sound (by decide +kernel)
theorem ng141 : Good 6 (zset 141) := .done _ _ _ _ _ nd141 (by decide +kernel)
theorem nd142 : Data (zset 142) (tset 142) (uset 142) (hset 142) (aset 142) := verifies_sound (by decide +kernel)
theorem ng142 : Good 6 (zset 142) := .done _ _ _ _ _ nd142 (by decide +kernel)
theorem nd143 : Data (zset 143) (tset 143) (uset 143) (hset 143) (aset 143) := verifies_sound (by decide +kernel)
theorem ng143 : Good 6 (zset 143) := by
  have eq : (zset 143).erase 15=zset 69 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd143 (by decide +kernel) (eq.symm ▸ ng69)
theorem nd144 : Data (zset 144) (tset 144) (uset 144) (hset 144) (aset 144) := verifies_sound (by decide +kernel)
theorem ng144 : Good 6 (zset 144) := .done _ _ _ _ _ nd144 (by decide +kernel)
theorem nd145 : Data (zset 145) (tset 145) (uset 145) (hset 145) (aset 145) := verifies_sound (by decide +kernel)
theorem ng145 : Good 6 (zset 145) := .done _ _ _ _ _ nd145 (by decide +kernel)
theorem nd146 : Data (zset 146) (tset 146) (uset 146) (hset 146) (aset 146) := verifies_sound (by decide +kernel)
theorem ng146 : Good 6 (zset 146) := by
  have eq : (zset 146).erase 24=zset 68 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd146 (by decide +kernel) (eq.symm ▸ ng68)
theorem nd147 : Data (zset 147) (tset 147) (uset 147) (hset 147) (aset 147) := verifies_sound (by decide +kernel)
theorem ng147 : Good 6 (zset 147) := by
  have eq : (zset 147).erase 19=zset 71 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd147 (by decide +kernel) (eq.symm ▸ ng71)
theorem nd148 : Data (zset 148) (tset 148) (uset 148) (hset 148) (aset 148) := verifies_sound (by decide +kernel)
theorem ng148 : Good 6 (zset 148) := by
  have eq : (zset 148).erase 22=zset 70 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd148 (by decide +kernel) (eq.symm ▸ ng70)
theorem nd149 : Data (zset 149) (tset 149) (uset 149) (hset 149) (aset 149) := verifies_sound (by decide +kernel)
theorem ng149 : Good 6 (zset 149) := by
  have eq : (zset 149).erase 24=zset 72 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd149 (by decide +kernel) (eq.symm ▸ ng72)
theorem nd150 : Data (zset 150) (tset 150) (uset 150) (hset 150) (aset 150) := verifies_sound (by decide +kernel)
theorem ng150 : Good 6 (zset 150) := by
  have eq : (zset 150).erase 27=zset 73 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd150 (by decide +kernel) (eq.symm ▸ ng73)
theorem nd151 : Data (zset 151) (tset 151) (uset 151) (hset 151) (aset 151) := verifies_sound (by decide +kernel)
theorem ng151 : Good 6 (zset 151) := .done _ _ _ _ _ nd151 (by decide +kernel)
theorem nd152 : Data (zset 152) (tset 152) (uset 152) (hset 152) (aset 152) := verifies_sound (by decide +kernel)
theorem ng152 : Good 6 (zset 152) := .done _ _ _ _ _ nd152 (by decide +kernel)
theorem nd153 : Data (zset 153) (tset 153) (uset 153) (hset 153) (aset 153) := verifies_sound (by decide +kernel)
theorem ng153 : Good 6 (zset 153) := .done _ _ _ _ _ nd153 (by decide +kernel)
theorem nd154 : Data (zset 154) (tset 154) (uset 154) (hset 154) (aset 154) := verifies_sound (by decide +kernel)
theorem ng154 : Good 6 (zset 154) := .done _ _ _ _ _ nd154 (by decide +kernel)
theorem nd155 : Data (zset 155) (tset 155) (uset 155) (hset 155) (aset 155) := verifies_sound (by decide +kernel)
theorem ng155 : Good 6 (zset 155) := .done _ _ _ _ _ nd155 (by decide +kernel)
theorem nd156 : Data (zset 156) (tset 156) (uset 156) (hset 156) (aset 156) := verifies_sound (by decide +kernel)
theorem ng156 : Good 6 (zset 156) := .done _ _ _ _ _ nd156 (by decide +kernel)
theorem nd157 : Data (zset 157) (tset 157) (uset 157) (hset 157) (aset 157) := verifies_sound (by decide +kernel)
theorem ng157 : Good 6 (zset 157) := .done _ _ _ _ _ nd157 (by decide +kernel)
theorem nd158 : Data (zset 158) (tset 158) (uset 158) (hset 158) (aset 158) := verifies_sound (by decide +kernel)
theorem ng158 : Good 6 (zset 158) := .done _ _ _ _ _ nd158 (by decide +kernel)
theorem nd159 : Data (zset 159) (tset 159) (uset 159) (hset 159) (aset 159) := verifies_sound (by decide +kernel)
theorem ng159 : Good 6 (zset 159) := by
  have eq : (zset 159).erase 19=zset 75 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd159 (by decide +kernel) (eq.symm ▸ ng75)
theorem nd160 : Data (zset 160) (tset 160) (uset 160) (hset 160) (aset 160) := verifies_sound (by decide +kernel)
theorem ng160 : Good 6 (zset 160) := by
  have eq : (zset 160).erase 15=zset 76 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd160 (by decide +kernel) (eq.symm ▸ ng76)
theorem nd161 : Data (zset 161) (tset 161) (uset 161) (hset 161) (aset 161) := verifies_sound (by decide +kernel)
theorem ng161 : Good 6 (zset 161) := by
  have eq : (zset 161).erase 31=zset 67 := by decide +kernel
  exact .pivot _ _ _ _ _ 31 nd161 (by decide +kernel) (eq.symm ▸ ng67)
theorem nd162 : Data (zset 162) (tset 162) (uset 162) (hset 162) (aset 162) := verifies_sound (by decide +kernel)
theorem ng162 : Good 6 (zset 162) := by
  have eq : (zset 162).erase 29=zset 77 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd162 (by decide +kernel) (eq.symm ▸ ng77)
theorem nd163 : Data (zset 163) (tset 163) (uset 163) (hset 163) (aset 163) := verifies_sound (by decide +kernel)
theorem ng163 : Good 6 (zset 163) := .done _ _ _ _ _ nd163 (by decide +kernel)
theorem nd164 : Data (zset 164) (tset 164) (uset 164) (hset 164) (aset 164) := verifies_sound (by decide +kernel)
theorem ng164 : Good 6 (zset 164) := .done _ _ _ _ _ nd164 (by decide +kernel)
theorem nd165 : Data (zset 165) (tset 165) (uset 165) (hset 165) (aset 165) := verifies_sound (by decide +kernel)
theorem ng165 : Good 6 (zset 165) := .done _ _ _ _ _ nd165 (by decide +kernel)
theorem nd166 : Data (zset 166) (tset 166) (uset 166) (hset 166) (aset 166) := verifies_sound (by decide +kernel)
theorem ng166 : Good 6 (zset 166) := .done _ _ _ _ _ nd166 (by decide +kernel)
theorem nd167 : Data (zset 167) (tset 167) (uset 167) (hset 167) (aset 167) := verifies_sound (by decide +kernel)
theorem ng167 : Good 6 (zset 167) := by
  have eq : (zset 167).erase 12=zset 80 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd167 (by decide +kernel) (eq.symm ▸ ng80)
theorem nd168 : Data (zset 168) (tset 168) (uset 168) (hset 168) (aset 168) := verifies_sound (by decide +kernel)
theorem ng168 : Good 6 (zset 168) := by
  have eq : (zset 168).erase 18=zset 80 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 nd168 (by decide +kernel) (eq.symm ▸ ng80)
theorem nd169 : Data (zset 169) (tset 169) (uset 169) (hset 169) (aset 169) := verifies_sound (by decide +kernel)
theorem ng169 : Good 6 (zset 169) := by
  have eq : (zset 169).erase 29=zset 78 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd169 (by decide +kernel) (eq.symm ▸ ng78)
theorem nd170 : Data (zset 170) (tset 170) (uset 170) (hset 170) (aset 170) := verifies_sound (by decide +kernel)
theorem ng170 : Good 6 (zset 170) := by
  have eq : (zset 170).erase 20=zset 79 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 nd170 (by decide +kernel) (eq.symm ▸ ng79)
theorem nd171 : Data (zset 171) (tset 171) (uset 171) (hset 171) (aset 171) := verifies_sound (by decide +kernel)
theorem ng171 : Good 6 (zset 171) := by
  have eq : (zset 171).erase 12=zset 81 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd171 (by decide +kernel) (eq.symm ▸ ng81)
theorem nd172 : Data (zset 172) (tset 172) (uset 172) (hset 172) (aset 172) := verifies_sound (by decide +kernel)
theorem ng172 : Good 6 (zset 172) := by
  have eq : (zset 172).erase 32=zset 74 := by decide +kernel
  exact .pivot _ _ _ _ _ 32 nd172 (by decide +kernel) (eq.symm ▸ ng74)
theorem nd173 : Data (zset 173) (tset 173) (uset 173) (hset 173) (aset 173) := verifies_sound (by decide +kernel)
theorem ng173 : Good 6 (zset 173) := .done _ _ _ _ _ nd173 (by decide +kernel)
theorem nd174 : Data (zset 174) (tset 174) (uset 174) (hset 174) (aset 174) := verifies_sound (by decide +kernel)
theorem ng174 : Good 6 (zset 174) := by
  have eq : (zset 174).erase 20=zset 82 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 nd174 (by decide +kernel) (eq.symm ▸ ng82)
theorem nd175 : Data (zset 175) (tset 175) (uset 175) (hset 175) (aset 175) := verifies_sound (by decide +kernel)
theorem ng175 : Good 6 (zset 175) := .done _ _ _ _ _ nd175 (by decide +kernel)
theorem nd176 : Data (zset 176) (tset 176) (uset 176) (hset 176) (aset 176) := verifies_sound (by decide +kernel)
theorem ng176 : Good 6 (zset 176) := .done _ _ _ _ _ nd176 (by decide +kernel)
theorem nd177 : Data (zset 177) (tset 177) (uset 177) (hset 177) (aset 177) := verifies_sound (by decide +kernel)
theorem ng177 : Good 6 (zset 177) := .done _ _ _ _ _ nd177 (by decide +kernel)
theorem nd178 : Data (zset 178) (tset 178) (uset 178) (hset 178) (aset 178) := verifies_sound (by decide +kernel)
theorem ng178 : Good 6 (zset 178) := by
  have eq : (zset 178).erase 26=zset 84 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd178 (by decide +kernel) (eq.symm ▸ ng84)
theorem nd179 : Data (zset 179) (tset 179) (uset 179) (hset 179) (aset 179) := verifies_sound (by decide +kernel)
theorem ng179 : Good 6 (zset 179) := by
  have eq : (zset 179).erase 25=zset 85 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd179 (by decide +kernel) (eq.symm ▸ ng85)
theorem nd180 : Data (zset 180) (tset 180) (uset 180) (hset 180) (aset 180) := verifies_sound (by decide +kernel)
theorem ng180 : Good 6 (zset 180) := by
  have eq : (zset 180).erase 26=zset 87 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd180 (by decide +kernel) (eq.symm ▸ ng87)
theorem nd181 : Data (zset 181) (tset 181) (uset 181) (hset 181) (aset 181) := verifies_sound (by decide +kernel)
theorem ng181 : Good 6 (zset 181) := by
  have eq : (zset 181).erase 24=zset 88 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd181 (by decide +kernel) (eq.symm ▸ ng88)
theorem nd182 : Data (zset 182) (tset 182) (uset 182) (hset 182) (aset 182) := verifies_sound (by decide +kernel)
theorem ng182 : Good 6 (zset 182) := by
  have eq : (zset 182).erase 33=zset 86 := by decide +kernel
  exact .pivot _ _ _ _ _ 33 nd182 (by decide +kernel) (eq.symm ▸ ng86)
theorem nd183 : Data (zset 183) (tset 183) (uset 183) (hset 183) (aset 183) := verifies_sound (by decide +kernel)
theorem ng183 : Good 6 (zset 183) := by
  have eq : (zset 183).erase 25=zset 90 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd183 (by decide +kernel) (eq.symm ▸ ng90)
theorem nd184 : Data (zset 184) (tset 184) (uset 184) (hset 184) (aset 184) := verifies_sound (by decide +kernel)
theorem ng184 : Good 6 (zset 184) := by
  have eq : (zset 184).erase 25=zset 91 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd184 (by decide +kernel) (eq.symm ▸ ng91)
theorem nd185 : Data (zset 185) (tset 185) (uset 185) (hset 185) (aset 185) := verifies_sound (by decide +kernel)
theorem ng185 : Good 6 (zset 185) := .done _ _ _ _ _ nd185 (by decide +kernel)
theorem nd186 : Data (zset 186) (tset 186) (uset 186) (hset 186) (aset 186) := verifies_sound (by decide +kernel)
theorem ng186 : Good 6 (zset 186) := by
  have eq : (zset 186).erase 33=zset 92 := by decide +kernel
  exact .pivot _ _ _ _ _ 33 nd186 (by decide +kernel) (eq.symm ▸ ng92)
theorem nd187 : Data (zset 187) (tset 187) (uset 187) (hset 187) (aset 187) := verifies_sound (by decide +kernel)
theorem ng187 : Good 6 (zset 187) := by
  have eq : (zset 187).erase 29=zset 93 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd187 (by decide +kernel) (eq.symm ▸ ng93)
theorem nd188 : Data (zset 188) (tset 188) (uset 188) (hset 188) (aset 188) := verifies_sound (by decide +kernel)
theorem ng188 : Good 6 (zset 188) := by
  have eq : (zset 188).erase 33=zset 94 := by decide +kernel
  exact .pivot _ _ _ _ _ 33 nd188 (by decide +kernel) (eq.symm ▸ ng94)
theorem nd189 : Data (zset 189) (tset 189) (uset 189) (hset 189) (aset 189) := verifies_sound (by decide +kernel)
theorem ng189 : Good 6 (zset 189) := by
  have eq : (zset 189).erase 22=zset 95 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd189 (by decide +kernel) (eq.symm ▸ ng95)
theorem nd190 : Data (zset 190) (tset 190) (uset 190) (hset 190) (aset 190) := verifies_sound (by decide +kernel)
theorem ng190 : Good 6 (zset 190) := by
  have eq : (zset 190).erase 4=zset 98 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 nd190 (by decide +kernel) (eq.symm ▸ ng98)
theorem nd191 : Data (zset 191) (tset 191) (uset 191) (hset 191) (aset 191) := verifies_sound (by decide +kernel)
theorem ng191 : Good 6 (zset 191) := by
  have eq : (zset 191).erase 27=zset 96 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd191 (by decide +kernel) (eq.symm ▸ ng96)
theorem nd192 : Data (zset 192) (tset 192) (uset 192) (hset 192) (aset 192) := verifies_sound (by decide +kernel)
theorem ng192 : Good 6 (zset 192) := by
  have eq : (zset 192).erase 27=zset 97 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd192 (by decide +kernel) (eq.symm ▸ ng97)
theorem nd193 : Data (zset 193) (tset 193) (uset 193) (hset 193) (aset 193) := verifies_sound (by decide +kernel)
theorem ng193 : Good 6 (zset 193) := .done _ _ _ _ _ nd193 (by decide +kernel)
theorem nd194 : Data (zset 194) (tset 194) (uset 194) (hset 194) (aset 194) := verifies_sound (by decide +kernel)
theorem ng194 : Good 6 (zset 194) := .done _ _ _ _ _ nd194 (by decide +kernel)
theorem nd195 : Data (zset 195) (tset 195) (uset 195) (hset 195) (aset 195) := verifies_sound (by decide +kernel)
theorem ng195 : Good 6 (zset 195) := by
  have eq : (zset 195).erase 22=zset 100 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd195 (by decide +kernel) (eq.symm ▸ ng100)
theorem nd196 : Data (zset 196) (tset 196) (uset 196) (hset 196) (aset 196) := verifies_sound (by decide +kernel)
theorem ng196 : Good 6 (zset 196) := by
  have eq : (zset 196).erase 31=zset 99 := by decide +kernel
  exact .pivot _ _ _ _ _ 31 nd196 (by decide +kernel) (eq.symm ▸ ng99)
theorem nd197 : Data (zset 197) (tset 197) (uset 197) (hset 197) (aset 197) := verifies_sound (by decide +kernel)
theorem ng197 : Good 6 (zset 197) := by
  have eq : (zset 197).erase 30=zset 101 := by decide +kernel
  exact .pivot _ _ _ _ _ 30 nd197 (by decide +kernel) (eq.symm ▸ ng101)
theorem nd198 : Data (zset 198) (tset 198) (uset 198) (hset 198) (aset 198) := verifies_sound (by decide +kernel)
theorem ng198 : Good 6 (zset 198) := .done _ _ _ _ _ nd198 (by decide +kernel)
theorem nd199 : Data (zset 199) (tset 199) (uset 199) (hset 199) (aset 199) := verifies_sound (by decide +kernel)
theorem ng199 : Good 6 (zset 199) := by
  have eq : (zset 199).erase 6=zset 102 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 nd199 (by decide +kernel) (eq.symm ▸ ng102)
theorem nd200 : Data (zset 200) (tset 200) (uset 200) (hset 200) (aset 200) := verifies_sound (by decide +kernel)
theorem ng200 : Good 6 (zset 200) := by
  have eq : (zset 200).erase 19=zset 103 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd200 (by decide +kernel) (eq.symm ▸ ng103)
theorem nd201 : Data (zset 201) (tset 201) (uset 201) (hset 201) (aset 201) := verifies_sound (by decide +kernel)
theorem ng201 : Good 6 (zset 201) := by
  have eq : (zset 201).erase 1=zset 104 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd201 (by decide +kernel) (eq.symm ▸ ng104)
theorem nd202 : Data (zset 202) (tset 202) (uset 202) (hset 202) (aset 202) := verifies_sound (by decide +kernel)
theorem ng202 : Good 6 (zset 202) := by
  have eq : (zset 202).erase 11=zset 105 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd202 (by decide +kernel) (eq.symm ▸ ng105)
theorem nd203 : Data (zset 203) (tset 203) (uset 203) (hset 203) (aset 203) := verifies_sound (by decide +kernel)
theorem ng203 : Good 6 (zset 203) := by
  have eq : (zset 203).erase 1=zset 106 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd203 (by decide +kernel) (eq.symm ▸ ng106)
theorem nd204 : Data (zset 204) (tset 204) (uset 204) (hset 204) (aset 204) := verifies_sound (by decide +kernel)
theorem ng204 : Good 6 (zset 204) := by
  have eq : (zset 204).erase 1=zset 107 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd204 (by decide +kernel) (eq.symm ▸ ng107)
theorem nd205 : Data (zset 205) (tset 205) (uset 205) (hset 205) (aset 205) := verifies_sound (by decide +kernel)
theorem ng205 : Good 6 (zset 205) := by
  have eq : (zset 205).erase 11=zset 108 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd205 (by decide +kernel) (eq.symm ▸ ng108)
theorem nd206 : Data (zset 206) (tset 206) (uset 206) (hset 206) (aset 206) := verifies_sound (by decide +kernel)
theorem ng206 : Good 6 (zset 206) := by
  have eq : (zset 206).erase 0=zset 109 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd206 (by decide +kernel) (eq.symm ▸ ng109)
theorem nd207 : Data (zset 207) (tset 207) (uset 207) (hset 207) (aset 207) := verifies_sound (by decide +kernel)
theorem ng207 : Good 6 (zset 207) := by
  have eq : (zset 207).erase 0=zset 110 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd207 (by decide +kernel) (eq.symm ▸ ng110)
theorem nd208 : Data (zset 208) (tset 208) (uset 208) (hset 208) (aset 208) := verifies_sound (by decide +kernel)
theorem ng208 : Good 6 (zset 208) := by
  have eq : (zset 208).erase 2=zset 111 := by decide +kernel
  exact .pivot _ _ _ _ _ 2 nd208 (by decide +kernel) (eq.symm ▸ ng111)
theorem nd209 : Data (zset 209) (tset 209) (uset 209) (hset 209) (aset 209) := verifies_sound (by decide +kernel)
theorem ng209 : Good 6 (zset 209) := by
  have eq : (zset 209).erase 15=zset 112 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd209 (by decide +kernel) (eq.symm ▸ ng112)
theorem nd210 : Data (zset 210) (tset 210) (uset 210) (hset 210) (aset 210) := verifies_sound (by decide +kernel)
theorem ng210 : Good 6 (zset 210) := .done _ _ _ _ _ nd210 (by decide +kernel)
theorem nd211 : Data (zset 211) (tset 211) (uset 211) (hset 211) (aset 211) := verifies_sound (by decide +kernel)
theorem ng211 : Good 6 (zset 211) := by
  have eq : (zset 211).erase 12=zset 115 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd211 (by decide +kernel) (eq.symm ▸ ng115)
theorem nd212 : Data (zset 212) (tset 212) (uset 212) (hset 212) (aset 212) := verifies_sound (by decide +kernel)
theorem ng212 : Good 6 (zset 212) := by
  have eq : (zset 212).erase 9=zset 117 := by decide +kernel
  exact .pivot _ _ _ _ _ 9 nd212 (by decide +kernel) (eq.symm ▸ ng117)
theorem nd213 : Data (zset 213) (tset 213) (uset 213) (hset 213) (aset 213) := verifies_sound (by decide +kernel)
theorem ng213 : Good 6 (zset 213) := by
  have eq : (zset 213).erase 17=zset 118 := by decide +kernel
  exact .pivot _ _ _ _ _ 17 nd213 (by decide +kernel) (eq.symm ▸ ng118)
theorem nd214 : Data (zset 214) (tset 214) (uset 214) (hset 214) (aset 214) := verifies_sound (by decide +kernel)
theorem ng214 : Good 6 (zset 214) := by
  have eq : (zset 214).erase 0=zset 123 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd214 (by decide +kernel) (eq.symm ▸ ng123)
theorem nd215 : Data (zset 215) (tset 215) (uset 215) (hset 215) (aset 215) := verifies_sound (by decide +kernel)
theorem ng215 : Good 6 (zset 215) := by
  have eq : (zset 215).erase 13=zset 125 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd215 (by decide +kernel) (eq.symm ▸ ng125)
theorem nd216 : Data (zset 216) (tset 216) (uset 216) (hset 216) (aset 216) := verifies_sound (by decide +kernel)
theorem ng216 : Good 6 (zset 216) := by
  have eq : (zset 216).erase 0=zset 126 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd216 (by decide +kernel) (eq.symm ▸ ng126)
theorem nd217 : Data (zset 217) (tset 217) (uset 217) (hset 217) (aset 217) := verifies_sound (by decide +kernel)
theorem ng217 : Good 6 (zset 217) := .done _ _ _ _ _ nd217 (by decide +kernel)
theorem nd218 : Data (zset 218) (tset 218) (uset 218) (hset 218) (aset 218) := verifies_sound (by decide +kernel)
theorem ng218 : Good 6 (zset 218) := by
  have eq : (zset 218).erase 3=zset 135 := by decide +kernel
  exact .pivot _ _ _ _ _ 3 nd218 (by decide +kernel) (eq.symm ▸ ng135)
theorem nd219 : Data (zset 219) (tset 219) (uset 219) (hset 219) (aset 219) := verifies_sound (by decide +kernel)
theorem ng219 : Good 6 (zset 219) := .done _ _ _ _ _ nd219 (by decide +kernel)
theorem nd220 : Data (zset 220) (tset 220) (uset 220) (hset 220) (aset 220) := verifies_sound (by decide +kernel)
theorem ng220 : Good 6 (zset 220) := by
  have eq : (zset 220).erase 1=zset 143 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd220 (by decide +kernel) (eq.symm ▸ ng143)
theorem nd221 : Data (zset 221) (tset 221) (uset 221) (hset 221) (aset 221) := verifies_sound (by decide +kernel)
theorem ng221 : Good 6 (zset 221) := by
  have eq : (zset 221).erase 12=zset 147 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd221 (by decide +kernel) (eq.symm ▸ ng147)
theorem nd222 : Data (zset 222) (tset 222) (uset 222) (hset 222) (aset 222) := verifies_sound (by decide +kernel)
theorem ng222 : Good 6 (zset 222) := by
  have eq : (zset 222).erase 0=zset 159 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd222 (by decide +kernel) (eq.symm ▸ ng159)
theorem nd223 : Data (zset 223) (tset 223) (uset 223) (hset 223) (aset 223) := verifies_sound (by decide +kernel)
theorem ng223 : Good 6 (zset 223) := by
  have eq : (zset 223).erase 22=zset 160 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd223 (by decide +kernel) (eq.symm ▸ ng160)
theorem nd224 : Data (zset 224) (tset 224) (uset 224) (hset 224) (aset 224) := verifies_sound (by decide +kernel)
theorem ng224 : Good 6 (zset 224) := by
  have eq : (zset 224).erase 26=zset 162 := by decide +kernel
  exact .pivot _ _ _ _ _ 26 nd224 (by decide +kernel) (eq.symm ▸ ng162)
theorem nd225 : Data (zset 225) (tset 225) (uset 225) (hset 225) (aset 225) := verifies_sound (by decide +kernel)
theorem ng225 : Good 6 (zset 225) := by
  have eq : (zset 225).erase 12=zset 168 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd225 (by decide +kernel) (eq.symm ▸ ng168)
theorem nd226 : Data (zset 226) (tset 226) (uset 226) (hset 226) (aset 226) := verifies_sound (by decide +kernel)
theorem ng226 : Good 6 (zset 226) := by
  have eq : (zset 226).erase 21=zset 170 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd226 (by decide +kernel) (eq.symm ▸ ng170)
theorem nd227 : Data (zset 227) (tset 227) (uset 227) (hset 227) (aset 227) := verifies_sound (by decide +kernel)
theorem ng227 : Good 6 (zset 227) := by
  have eq : (zset 227).erase 23=zset 167 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd227 (by decide +kernel) (eq.symm ▸ ng167)
theorem nd228 : Data (zset 228) (tset 228) (uset 228) (hset 228) (aset 228) := verifies_sound (by decide +kernel)
theorem ng228 : Good 6 (zset 228) := by
  have eq : (zset 228).erase 25=zset 169 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd228 (by decide +kernel) (eq.symm ▸ ng169)
theorem nd229 : Data (zset 229) (tset 229) (uset 229) (hset 229) (aset 229) := verifies_sound (by decide +kernel)
theorem ng229 : Good 6 (zset 229) := by
  have eq : (zset 229).erase 22=zset 172 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd229 (by decide +kernel) (eq.symm ▸ ng172)
theorem nd230 : Data (zset 230) (tset 230) (uset 230) (hset 230) (aset 230) := verifies_sound (by decide +kernel)
theorem ng230 : Good 6 (zset 230) := by
  have eq : (zset 230).erase 32=zset 161 := by decide +kernel
  exact .pivot _ _ _ _ _ 32 nd230 (by decide +kernel) (eq.symm ▸ ng161)
theorem nd231 : Data (zset 231) (tset 231) (uset 231) (hset 231) (aset 231) := verifies_sound (by decide +kernel)
theorem ng231 : Good 6 (zset 231) := by
  have eq : (zset 231).erase 1=zset 174 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd231 (by decide +kernel) (eq.symm ▸ ng174)
theorem nd232 : Data (zset 232) (tset 232) (uset 232) (hset 232) (aset 232) := verifies_sound (by decide +kernel)
theorem ng232 : Good 6 (zset 232) := by
  have eq : (zset 232).erase 21=zset 178 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd232 (by decide +kernel) (eq.symm ▸ ng178)
theorem nd233 : Data (zset 233) (tset 233) (uset 233) (hset 233) (aset 233) := verifies_sound (by decide +kernel)
theorem ng233 : Good 6 (zset 233) := by
  have eq : (zset 233).erase 28=zset 179 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd233 (by decide +kernel) (eq.symm ▸ ng179)
theorem nd234 : Data (zset 234) (tset 234) (uset 234) (hset 234) (aset 234) := verifies_sound (by decide +kernel)
theorem ng234 : Good 6 (zset 234) := .done _ _ _ _ _ nd234 (by decide +kernel)
theorem nd235 : Data (zset 235) (tset 235) (uset 235) (hset 235) (aset 235) := verifies_sound (by decide +kernel)
theorem ng235 : Good 6 (zset 235) := .done _ _ _ _ _ nd235 (by decide +kernel)
theorem nd236 : Data (zset 236) (tset 236) (uset 236) (hset 236) (aset 236) := verifies_sound (by decide +kernel)
theorem ng236 : Good 6 (zset 236) := by
  have eq : (zset 236).erase 34=zset 171 := by decide +kernel
  exact .pivot _ _ _ _ _ 34 nd236 (by decide +kernel) (eq.symm ▸ ng171)
theorem nd237 : Data (zset 237) (tset 237) (uset 237) (hset 237) (aset 237) := verifies_sound (by decide +kernel)
theorem ng237 : Good 6 (zset 237) := by
  have eq : (zset 237).erase 24=zset 180 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd237 (by decide +kernel) (eq.symm ▸ ng180)
theorem nd238 : Data (zset 238) (tset 238) (uset 238) (hset 238) (aset 238) := verifies_sound (by decide +kernel)
theorem ng238 : Good 6 (zset 238) := by
  have eq : (zset 238).erase 22=zset 181 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd238 (by decide +kernel) (eq.symm ▸ ng181)
theorem nd239 : Data (zset 239) (tset 239) (uset 239) (hset 239) (aset 239) := verifies_sound (by decide +kernel)
theorem ng239 : Good 6 (zset 239) := by
  have eq : (zset 239).erase 29=zset 182 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd239 (by decide +kernel) (eq.symm ▸ ng182)
theorem nd240 : Data (zset 240) (tset 240) (uset 240) (hset 240) (aset 240) := verifies_sound (by decide +kernel)
theorem ng240 : Good 6 (zset 240) := by
  have eq : (zset 240).erase 23=zset 183 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd240 (by decide +kernel) (eq.symm ▸ ng183)
theorem nd241 : Data (zset 241) (tset 241) (uset 241) (hset 241) (aset 241) := verifies_sound (by decide +kernel)
theorem ng241 : Good 6 (zset 241) := by
  have eq : (zset 241).erase 23=zset 184 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd241 (by decide +kernel) (eq.symm ▸ ng184)
theorem nd242 : Data (zset 242) (tset 242) (uset 242) (hset 242) (aset 242) := verifies_sound (by decide +kernel)
theorem ng242 : Good 6 (zset 242) := by
  have eq : (zset 242).erase 30=zset 185 := by decide +kernel
  exact .pivot _ _ _ _ _ 30 nd242 (by decide +kernel) (eq.symm ▸ ng185)
theorem nd243 : Data (zset 243) (tset 243) (uset 243) (hset 243) (aset 243) := verifies_sound (by decide +kernel)
theorem ng243 : Good 6 (zset 243) := by
  have eq : (zset 243).erase 23=zset 186 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd243 (by decide +kernel) (eq.symm ▸ ng186)
theorem nd244 : Data (zset 244) (tset 244) (uset 244) (hset 244) (aset 244) := verifies_sound (by decide +kernel)
theorem ng244 : Good 6 (zset 244) := by
  have eq : (zset 244).erase 22=zset 187 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd244 (by decide +kernel) (eq.symm ▸ ng187)
theorem nd245 : Data (zset 245) (tset 245) (uset 245) (hset 245) (aset 245) := verifies_sound (by decide +kernel)
theorem ng245 : Good 6 (zset 245) := by
  have eq : (zset 245).erase 24=zset 189 := by decide +kernel
  exact .pivot _ _ _ _ _ 24 nd245 (by decide +kernel) (eq.symm ▸ ng189)
theorem nd246 : Data (zset 246) (tset 246) (uset 246) (hset 246) (aset 246) := verifies_sound (by decide +kernel)
theorem ng246 : Good 6 (zset 246) := by
  have eq : (zset 246).erase 35=zset 188 := by decide +kernel
  exact .pivot _ _ _ _ _ 35 nd246 (by decide +kernel) (eq.symm ▸ ng188)
theorem nd247 : Data (zset 247) (tset 247) (uset 247) (hset 247) (aset 247) := verifies_sound (by decide +kernel)
theorem ng247 : Good 6 (zset 247) := by
  have eq : (zset 247).erase 15=zset 190 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd247 (by decide +kernel) (eq.symm ▸ ng190)
theorem nd248 : Data (zset 248) (tset 248) (uset 248) (hset 248) (aset 248) := verifies_sound (by decide +kernel)
theorem ng248 : Good 6 (zset 248) := by
  have eq : (zset 248).erase 27=zset 193 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd248 (by decide +kernel) (eq.symm ▸ ng193)
theorem nd249 : Data (zset 249) (tset 249) (uset 249) (hset 249) (aset 249) := verifies_sound (by decide +kernel)
theorem ng249 : Good 6 (zset 249) := by
  have eq : (zset 249).erase 27=zset 196 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd249 (by decide +kernel) (eq.symm ▸ ng196)
theorem nd250 : Data (zset 250) (tset 250) (uset 250) (hset 250) (aset 250) := verifies_sound (by decide +kernel)
theorem ng250 : Good 6 (zset 250) := by
  have eq : (zset 250).erase 27=zset 197 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd250 (by decide +kernel) (eq.symm ▸ ng197)
theorem nd251 : Data (zset 251) (tset 251) (uset 251) (hset 251) (aset 251) := verifies_sound (by decide +kernel)
theorem ng251 : Good 6 (zset 251) := by
  have eq : (zset 251).erase 36=zset 198 := by decide +kernel
  exact .pivot _ _ _ _ _ 36 nd251 (by decide +kernel) (eq.symm ▸ ng198)
theorem nd252 : Data (zset 252) (tset 252) (uset 252) (hset 252) (aset 252) := verifies_sound (by decide +kernel)
theorem ng252 : Good 6 (zset 252) := by
  have eq : (zset 252).erase 14=zset 199 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd252 (by decide +kernel) (eq.symm ▸ ng199)
theorem nd253 : Data (zset 253) (tset 253) (uset 253) (hset 253) (aset 253) := verifies_sound (by decide +kernel)
theorem ng253 : Good 6 (zset 253) := by
  have eq : (zset 253).erase 8=zset 200 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 nd253 (by decide +kernel) (eq.symm ▸ ng200)
theorem nd254 : Data (zset 254) (tset 254) (uset 254) (hset 254) (aset 254) := verifies_sound (by decide +kernel)
theorem ng254 : Good 6 (zset 254) := by
  have eq : (zset 254).erase 11=zset 201 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd254 (by decide +kernel) (eq.symm ▸ ng201)
theorem nd255 : Data (zset 255) (tset 255) (uset 255) (hset 255) (aset 255) := verifies_sound (by decide +kernel)
theorem ng255 : Good 6 (zset 255) := by
  have eq : (zset 255).erase 2=zset 202 := by decide +kernel
  exact .pivot _ _ _ _ _ 2 nd255 (by decide +kernel) (eq.symm ▸ ng202)
theorem nd256 : Data (zset 256) (tset 256) (uset 256) (hset 256) (aset 256) := verifies_sound (by decide +kernel)
theorem ng256 : Good 6 (zset 256) := by
  have eq : (zset 256).erase 15=zset 203 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd256 (by decide +kernel) (eq.symm ▸ ng203)
theorem nd257 : Data (zset 257) (tset 257) (uset 257) (hset 257) (aset 257) := verifies_sound (by decide +kernel)
theorem ng257 : Good 6 (zset 257) := by
  have eq : (zset 257).erase 15=zset 204 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd257 (by decide +kernel) (eq.symm ▸ ng204)
theorem nd258 : Data (zset 258) (tset 258) (uset 258) (hset 258) (aset 258) := verifies_sound (by decide +kernel)
theorem ng258 : Good 6 (zset 258) := .done _ _ _ _ _ nd258 (by decide +kernel)
theorem nd259 : Data (zset 259) (tset 259) (uset 259) (hset 259) (aset 259) := verifies_sound (by decide +kernel)
theorem ng259 : Good 6 (zset 259) := by
  have eq : (zset 259).erase 8=zset 206 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 nd259 (by decide +kernel) (eq.symm ▸ ng206)
theorem nd260 : Data (zset 260) (tset 260) (uset 260) (hset 260) (aset 260) := verifies_sound (by decide +kernel)
theorem ng260 : Good 6 (zset 260) := by
  have eq : (zset 260).erase 15=zset 207 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd260 (by decide +kernel) (eq.symm ▸ ng207)
theorem nd261 : Data (zset 261) (tset 261) (uset 261) (hset 261) (aset 261) := verifies_sound (by decide +kernel)
theorem ng261 : Good 6 (zset 261) := by
  have eq : (zset 261).erase 15=zset 208 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd261 (by decide +kernel) (eq.symm ▸ ng208)
theorem nd262 : Data (zset 262) (tset 262) (uset 262) (hset 262) (aset 262) := verifies_sound (by decide +kernel)
theorem ng262 : Good 6 (zset 262) := by
  have eq : (zset 262).erase 11=zset 214 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd262 (by decide +kernel) (eq.symm ▸ ng214)
theorem nd263 : Data (zset 263) (tset 263) (uset 263) (hset 263) (aset 263) := verifies_sound (by decide +kernel)
theorem ng263 : Good 6 (zset 263) := by
  have eq : (zset 263).erase 21=zset 222 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd263 (by decide +kernel) (eq.symm ▸ ng222)
theorem nd264 : Data (zset 264) (tset 264) (uset 264) (hset 264) (aset 264) := verifies_sound (by decide +kernel)
theorem ng264 : Good 6 (zset 264) := by
  have eq : (zset 264).erase 20=zset 225 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 nd264 (by decide +kernel) (eq.symm ▸ ng225)
theorem nd265 : Data (zset 265) (tset 265) (uset 265) (hset 265) (aset 265) := verifies_sound (by decide +kernel)
theorem ng265 : Good 6 (zset 265) := by
  have eq : (zset 265).erase 29=zset 233 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd265 (by decide +kernel) (eq.symm ▸ ng233)
theorem nd266 : Data (zset 266) (tset 266) (uset 266) (hset 266) (aset 266) := verifies_sound (by decide +kernel)
theorem ng266 : Good 6 (zset 266) := by
  have eq : (zset 266).erase 30=zset 237 := by decide +kernel
  exact .pivot _ _ _ _ _ 30 nd266 (by decide +kernel) (eq.symm ▸ ng237)
theorem nd267 : Data (zset 267) (tset 267) (uset 267) (hset 267) (aset 267) := verifies_sound (by decide +kernel)
theorem ng267 : Good 6 (zset 267) := by
  have eq : (zset 267).erase 27=zset 238 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd267 (by decide +kernel) (eq.symm ▸ ng238)
theorem nd268 : Data (zset 268) (tset 268) (uset 268) (hset 268) (aset 268) := verifies_sound (by decide +kernel)
theorem ng268 : Good 6 (zset 268) := by
  have eq : (zset 268).erase 21=zset 239 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd268 (by decide +kernel) (eq.symm ▸ ng239)
theorem nd269 : Data (zset 269) (tset 269) (uset 269) (hset 269) (aset 269) := verifies_sound (by decide +kernel)
theorem ng269 : Good 6 (zset 269) := by
  have eq : (zset 269).erase 28=zset 241 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd269 (by decide +kernel) (eq.symm ▸ ng241)
theorem nd270 : Data (zset 270) (tset 270) (uset 270) (hset 270) (aset 270) := verifies_sound (by decide +kernel)
theorem ng270 : Good 6 (zset 270) := by
  have eq : (zset 270).erase 23=zset 244 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 nd270 (by decide +kernel) (eq.symm ▸ ng244)
theorem nd271 : Data (zset 271) (tset 271) (uset 271) (hset 271) (aset 271) := verifies_sound (by decide +kernel)
theorem ng271 : Good 6 (zset 271) := by
  have eq : (zset 271).erase 28=zset 245 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd271 (by decide +kernel) (eq.symm ▸ ng245)
theorem nd272 : Data (zset 272) (tset 272) (uset 272) (hset 272) (aset 272) := verifies_sound (by decide +kernel)
theorem ng272 : Good 6 (zset 272) := by
  have eq : (zset 272).erase 21=zset 246 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd272 (by decide +kernel) (eq.symm ▸ ng246)
theorem nd273 : Data (zset 273) (tset 273) (uset 273) (hset 273) (aset 273) := verifies_sound (by decide +kernel)
theorem ng273 : Good 6 (zset 273) := by
  have eq : (zset 273).erase 21=zset 249 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd273 (by decide +kernel) (eq.symm ▸ ng249)
theorem nd274 : Data (zset 274) (tset 274) (uset 274) (hset 274) (aset 274) := verifies_sound (by decide +kernel)
theorem ng274 : Good 6 (zset 274) := by
  have eq : (zset 274).erase 37=zset 240 := by decide +kernel
  exact .pivot _ _ _ _ _ 37 nd274 (by decide +kernel) (eq.symm ▸ ng240)
theorem nd275 : Data (zset 275) (tset 275) (uset 275) (hset 275) (aset 275) := verifies_sound (by decide +kernel)
theorem ng275 : Good 6 (zset 275) := by
  have eq : (zset 275).erase 35=zset 250 := by decide +kernel
  exact .pivot _ _ _ _ _ 35 nd275 (by decide +kernel) (eq.symm ▸ ng250)
theorem nd276 : Data (zset 276) (tset 276) (uset 276) (hset 276) (aset 276) := verifies_sound (by decide +kernel)
theorem ng276 : Good 6 (zset 276) := by
  have eq : (zset 276).erase 38=zset 243 := by decide +kernel
  exact .pivot _ _ _ _ _ 38 nd276 (by decide +kernel) (eq.symm ▸ ng243)
theorem nd277 : Data (zset 277) (tset 277) (uset 277) (hset 277) (aset 277) := verifies_sound (by decide +kernel)
theorem ng277 : Good 6 (zset 277) := .done _ _ _ _ _ nd277 (by decide +kernel)
theorem nd278 : Data (zset 278) (tset 278) (uset 278) (hset 278) (aset 278) := verifies_sound (by decide +kernel)
theorem ng278 : Good 6 (zset 278) := .done _ _ _ _ _ nd278 (by decide +kernel)
theorem nd279 : Data (zset 279) (tset 279) (uset 279) (hset 279) (aset 279) := verifies_sound (by decide +kernel)
theorem ng279 : Good 6 (zset 279) := by
  have eq : (zset 279).erase 32=zset 251 := by decide +kernel
  exact .pivot _ _ _ _ _ 32 nd279 (by decide +kernel) (eq.symm ▸ ng251)
theorem nd280 : Data (zset 280) (tset 280) (uset 280) (hset 280) (aset 280) := verifies_sound (by decide +kernel)
theorem ng280 : Good 6 (zset 280) := by
  have eq : (zset 280).erase 4=zset 252 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 nd280 (by decide +kernel) (eq.symm ▸ ng252)
theorem nd281 : Data (zset 281) (tset 281) (uset 281) (hset 281) (aset 281) := verifies_sound (by decide +kernel)
theorem ng281 : Good 6 (zset 281) := by
  have eq : (zset 281).erase 11=zset 253 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd281 (by decide +kernel) (eq.symm ▸ ng253)
theorem nd282 : Data (zset 282) (tset 282) (uset 282) (hset 282) (aset 282) := verifies_sound (by decide +kernel)
theorem ng282 : Good 6 (zset 282) := by
  have eq : (zset 282).erase 8=zset 254 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 nd282 (by decide +kernel) (eq.symm ▸ ng254)
theorem nd283 : Data (zset 283) (tset 283) (uset 283) (hset 283) (aset 283) := verifies_sound (by decide +kernel)
theorem ng283 : Good 6 (zset 283) := by
  have eq : (zset 283).erase 6=zset 255 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 nd283 (by decide +kernel) (eq.symm ▸ ng255)
theorem nd284 : Data (zset 284) (tset 284) (uset 284) (hset 284) (aset 284) := verifies_sound (by decide +kernel)
theorem ng284 : Good 6 (zset 284) := .done _ _ _ _ _ nd284 (by decide +kernel)
theorem nd285 : Data (zset 285) (tset 285) (uset 285) (hset 285) (aset 285) := verifies_sound (by decide +kernel)
theorem ng285 : Good 6 (zset 285) := by
  have eq : (zset 285).erase 4=zset 259 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 nd285 (by decide +kernel) (eq.symm ▸ ng259)
theorem nd286 : Data (zset 286) (tset 286) (uset 286) (hset 286) (aset 286) := verifies_sound (by decide +kernel)
theorem ng286 : Good 6 (zset 286) := .done _ _ _ _ _ nd286 (by decide +kernel)
theorem nd287 : Data (zset 287) (tset 287) (uset 287) (hset 287) (aset 287) := verifies_sound (by decide +kernel)
theorem ng287 : Good 6 (zset 287) := by
  have eq : (zset 287).erase 21=zset 269 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd287 (by decide +kernel) (eq.symm ▸ ng269)
theorem nd288 : Data (zset 288) (tset 288) (uset 288) (hset 288) (aset 288) := verifies_sound (by decide +kernel)
theorem ng288 : Good 6 (zset 288) := by
  have eq : (zset 288).erase 33=zset 271 := by decide +kernel
  exact .pivot _ _ _ _ _ 33 nd288 (by decide +kernel) (eq.symm ▸ ng271)
theorem nd289 : Data (zset 289) (tset 289) (uset 289) (hset 289) (aset 289) := verifies_sound (by decide +kernel)
theorem ng289 : Good 6 (zset 289) := by
  have eq : (zset 289).erase 28=zset 275 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd289 (by decide +kernel) (eq.symm ▸ ng275)
theorem nd290 : Data (zset 290) (tset 290) (uset 290) (hset 290) (aset 290) := verifies_sound (by decide +kernel)
theorem ng290 : Good 6 (zset 290) := by
  have eq : (zset 290).erase 34=zset 274 := by decide +kernel
  exact .pivot _ _ _ _ _ 34 nd290 (by decide +kernel) (eq.symm ▸ ng274)
theorem nd291 : Data (zset 291) (tset 291) (uset 291) (hset 291) (aset 291) := verifies_sound (by decide +kernel)
theorem ng291 : Good 6 (zset 291) := .done _ _ _ _ _ nd291 (by decide +kernel)
theorem nd292 : Data (zset 292) (tset 292) (uset 292) (hset 292) (aset 292) := verifies_sound (by decide +kernel)
theorem ng292 : Good 6 (zset 292) := by
  have eq : (zset 292).erase 21=zset 276 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd292 (by decide +kernel) (eq.symm ▸ ng276)
theorem nd293 : Data (zset 293) (tset 293) (uset 293) (hset 293) (aset 293) := verifies_sound (by decide +kernel)
theorem ng293 : Good 6 (zset 293) := by
  have eq : (zset 293).erase 32=zset 277 := by decide +kernel
  exact .pivot _ _ _ _ _ 32 nd293 (by decide +kernel) (eq.symm ▸ ng277)
theorem nd294 : Data (zset 294) (tset 294) (uset 294) (hset 294) (aset 294) := verifies_sound (by decide +kernel)
theorem ng294 : Good 6 (zset 294) := by
  have eq : (zset 294).erase 28=zset 278 := by decide +kernel
  exact .pivot _ _ _ _ _ 28 nd294 (by decide +kernel) (eq.symm ▸ ng278)
theorem nd295 : Data (zset 295) (tset 295) (uset 295) (hset 295) (aset 295) := verifies_sound (by decide +kernel)
theorem ng295 : Good 6 (zset 295) := by
  have eq : (zset 295).erase 29=zset 279 := by decide +kernel
  exact .pivot _ _ _ _ _ 29 nd295 (by decide +kernel) (eq.symm ▸ ng279)
theorem nd296 : Data (zset 296) (tset 296) (uset 296) (hset 296) (aset 296) := verifies_sound (by decide +kernel)
theorem ng296 : Good 6 (zset 296) := by
  have eq : (zset 296).erase 7=zset 280 := by decide +kernel
  exact .pivot _ _ _ _ _ 7 nd296 (by decide +kernel) (eq.symm ▸ ng280)
theorem nd297 : Data (zset 297) (tset 297) (uset 297) (hset 297) (aset 297) := verifies_sound (by decide +kernel)
theorem ng297 : Good 6 (zset 297) := by
  have eq : (zset 297).erase 12=zset 281 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd297 (by decide +kernel) (eq.symm ▸ ng281)
theorem nd298 : Data (zset 298) (tset 298) (uset 298) (hset 298) (aset 298) := verifies_sound (by decide +kernel)
theorem ng298 : Good 6 (zset 298) := by
  have eq : (zset 298).erase 13=zset 282 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd298 (by decide +kernel) (eq.symm ▸ ng282)
theorem nd299 : Data (zset 299) (tset 299) (uset 299) (hset 299) (aset 299) := verifies_sound (by decide +kernel)
theorem ng299 : Good 6 (zset 299) := by
  have eq : (zset 299).erase 13=zset 283 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd299 (by decide +kernel) (eq.symm ▸ ng283)
theorem nd300 : Data (zset 300) (tset 300) (uset 300) (hset 300) (aset 300) := verifies_sound (by decide +kernel)
theorem ng300 : Good 6 (zset 300) := by
  have eq : (zset 300).erase 0=zset 284 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd300 (by decide +kernel) (eq.symm ▸ ng284)
theorem nd301 : Data (zset 301) (tset 301) (uset 301) (hset 301) (aset 301) := verifies_sound (by decide +kernel)
theorem ng301 : Good 6 (zset 301) := by
  have eq : (zset 301).erase 5=zset 285 := by decide +kernel
  exact .pivot _ _ _ _ _ 5 nd301 (by decide +kernel) (eq.symm ▸ ng285)
theorem nd302 : Data (zset 302) (tset 302) (uset 302) (hset 302) (aset 302) := verifies_sound (by decide +kernel)
theorem ng302 : Good 6 (zset 302) := by
  have eq : (zset 302).erase 13=zset 286 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd302 (by decide +kernel) (eq.symm ▸ ng286)
theorem nd303 : Data (zset 303) (tset 303) (uset 303) (hset 303) (aset 303) := verifies_sound (by decide +kernel)
theorem ng303 : Good 6 (zset 303) := by
  have eq : (zset 303).erase 21=zset 288 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd303 (by decide +kernel) (eq.symm ▸ ng288)
theorem nd304 : Data (zset 304) (tset 304) (uset 304) (hset 304) (aset 304) := verifies_sound (by decide +kernel)
theorem ng304 : Good 6 (zset 304) := by
  have eq : (zset 304).erase 22=zset 290 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd304 (by decide +kernel) (eq.symm ▸ ng290)
theorem nd305 : Data (zset 305) (tset 305) (uset 305) (hset 305) (aset 305) := verifies_sound (by decide +kernel)
theorem ng305 : Good 6 (zset 305) := by
  have eq : (zset 305).erase 21=zset 291 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd305 (by decide +kernel) (eq.symm ▸ ng291)
theorem nd306 : Data (zset 306) (tset 306) (uset 306) (hset 306) (aset 306) := verifies_sound (by decide +kernel)
theorem ng306 : Good 6 (zset 306) := by
  have eq : (zset 306).erase 30=zset 292 := by decide +kernel
  exact .pivot _ _ _ _ _ 30 nd306 (by decide +kernel) (eq.symm ▸ ng292)
theorem nd307 : Data (zset 307) (tset 307) (uset 307) (hset 307) (aset 307) := verifies_sound (by decide +kernel)
theorem ng307 : Good 6 (zset 307) := by
  have eq : (zset 307).erase 21=zset 293 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd307 (by decide +kernel) (eq.symm ▸ ng293)
theorem nd308 : Data (zset 308) (tset 308) (uset 308) (hset 308) (aset 308) := verifies_sound (by decide +kernel)
theorem ng308 : Good 6 (zset 308) := by
  have eq : (zset 308).erase 31=zset 294 := by decide +kernel
  exact .pivot _ _ _ _ _ 31 nd308 (by decide +kernel) (eq.symm ▸ ng294)
theorem nd309 : Data (zset 309) (tset 309) (uset 309) (hset 309) (aset 309) := verifies_sound (by decide +kernel)
theorem ng309 : Good 6 (zset 309) := by
  have eq : (zset 309).erase 22=zset 295 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd309 (by decide +kernel) (eq.symm ▸ ng295)
theorem nd310 : Data (zset 310) (tset 310) (uset 310) (hset 310) (aset 310) := verifies_sound (by decide +kernel)
theorem ng310 : Good 6 (zset 310) := by
  have eq : (zset 310).erase 18=zset 296 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 nd310 (by decide +kernel) (eq.symm ▸ ng296)
theorem nd311 : Data (zset 311) (tset 311) (uset 311) (hset 311) (aset 311) := verifies_sound (by decide +kernel)
theorem ng311 : Good 6 (zset 311) := by
  have eq : (zset 311).erase 7=zset 297 := by decide +kernel
  exact .pivot _ _ _ _ _ 7 nd311 (by decide +kernel) (eq.symm ▸ ng297)
theorem nd312 : Data (zset 312) (tset 312) (uset 312) (hset 312) (aset 312) := verifies_sound (by decide +kernel)
theorem ng312 : Good 6 (zset 312) := by
  have eq : (zset 312).erase 19=zset 300 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd312 (by decide +kernel) (eq.symm ▸ ng300)
theorem nd313 : Data (zset 313) (tset 313) (uset 313) (hset 313) (aset 313) := verifies_sound (by decide +kernel)
theorem ng313 : Good 6 (zset 313) := by
  have eq : (zset 313).erase 34=zset 305 := by decide +kernel
  exact .pivot _ _ _ _ _ 34 nd313 (by decide +kernel) (eq.symm ▸ ng305)
theorem nd314 : Data (zset 314) (tset 314) (uset 314) (hset 314) (aset 314) := verifies_sound (by decide +kernel)
theorem ng314 : Good 6 (zset 314) := by
  have eq : (zset 314).erase 22=zset 307 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd314 (by decide +kernel) (eq.symm ▸ ng307)
theorem nd315 : Data (zset 315) (tset 315) (uset 315) (hset 315) (aset 315) := verifies_sound (by decide +kernel)
theorem ng315 : Good 6 (zset 315) := by
  have eq : (zset 315).erase 34=zset 308 := by decide +kernel
  exact .pivot _ _ _ _ _ 34 nd315 (by decide +kernel) (eq.symm ▸ ng308)
theorem nd316 : Data (zset 316) (tset 316) (uset 316) (hset 316) (aset 316) := verifies_sound (by decide +kernel)
theorem ng316 : Good 6 (zset 316) := by
  have eq : (zset 316).erase 21=zset 309 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd316 (by decide +kernel) (eq.symm ▸ ng309)
theorem nd317 : Data (zset 317) (tset 317) (uset 317) (hset 317) (aset 317) := verifies_sound (by decide +kernel)
theorem ng317 : Good 6 (zset 317) := by
  have eq : (zset 317).erase 9=zset 310 := by decide +kernel
  exact .pivot _ _ _ _ _ 9 nd317 (by decide +kernel) (eq.symm ▸ ng310)
theorem nd318 : Data (zset 318) (tset 318) (uset 318) (hset 318) (aset 318) := verifies_sound (by decide +kernel)
theorem ng318 : Good 6 (zset 318) := by
  have eq : (zset 318).erase 5=zset 311 := by decide +kernel
  exact .pivot _ _ _ _ _ 5 nd318 (by decide +kernel) (eq.symm ▸ ng311)
theorem nd319 : Data (zset 319) (tset 319) (uset 319) (hset 319) (aset 319) := verifies_sound (by decide +kernel)
theorem ng319 : Good 6 (zset 319) := by
  have eq : (zset 319).erase 4=zset 312 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 nd319 (by decide +kernel) (eq.symm ▸ ng312)
theorem nd320 : Data (zset 320) (tset 320) (uset 320) (hset 320) (aset 320) := verifies_sound (by decide +kernel)
theorem ng320 : Good 6 (zset 320) := by
  have eq : (zset 320).erase 35=zset 314 := by decide +kernel
  exact .pivot _ _ _ _ _ 35 nd320 (by decide +kernel) (eq.symm ▸ ng314)
theorem nd321 : Data (zset 321) (tset 321) (uset 321) (hset 321) (aset 321) := verifies_sound (by decide +kernel)
theorem ng321 : Good 6 (zset 321) := by
  have eq : (zset 321).erase 21=zset 315 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd321 (by decide +kernel) (eq.symm ▸ ng315)
theorem nd322 : Data (zset 322) (tset 322) (uset 322) (hset 322) (aset 322) := verifies_sound (by decide +kernel)
theorem ng322 : Good 6 (zset 322) := by
  have eq : (zset 322).erase 35=zset 316 := by decide +kernel
  exact .pivot _ _ _ _ _ 35 nd322 (by decide +kernel) (eq.symm ▸ ng316)
theorem nd323 : Data (zset 323) (tset 323) (uset 323) (hset 323) (aset 323) := verifies_sound (by decide +kernel)
theorem ng323 : Good 6 (zset 323) := by
  have eq : (zset 323).erase 8=zset 317 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 nd323 (by decide +kernel) (eq.symm ▸ ng317)
theorem nd324 : Data (zset 324) (tset 324) (uset 324) (hset 324) (aset 324) := verifies_sound (by decide +kernel)
theorem ng324 : Good 6 (zset 324) := by
  have eq : (zset 324).erase 13=zset 318 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd324 (by decide +kernel) (eq.symm ▸ ng318)
theorem nd325 : Data (zset 325) (tset 325) (uset 325) (hset 325) (aset 325) := verifies_sound (by decide +kernel)
theorem ng325 : Good 6 (zset 325) := by
  have eq : (zset 325).erase 13=zset 319 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd325 (by decide +kernel) (eq.symm ▸ ng319)
theorem nd326 : Data (zset 326) (tset 326) (uset 326) (hset 326) (aset 326) := verifies_sound (by decide +kernel)
theorem ng326 : Good 6 (zset 326) := by
  have eq : (zset 326).erase 35=zset 321 := by decide +kernel
  exact .pivot _ _ _ _ _ 35 nd326 (by decide +kernel) (eq.symm ▸ ng321)
theorem nd327 : Data (zset 327) (tset 327) (uset 327) (hset 327) (aset 327) := verifies_sound (by decide +kernel)
theorem ng327 : Good 6 (zset 327) := by
  have eq : (zset 327).erase 27=zset 322 := by decide +kernel
  exact .pivot _ _ _ _ _ 27 nd327 (by decide +kernel) (eq.symm ▸ ng322)
theorem nd328 : Data (zset 328) (tset 328) (uset 328) (hset 328) (aset 328) := verifies_sound (by decide +kernel)
theorem ng328 : Good 6 (zset 328) := by
  have eq : (zset 328).erase 19=zset 323 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 nd328 (by decide +kernel) (eq.symm ▸ ng323)
theorem nd329 : Data (zset 329) (tset 329) (uset 329) (hset 329) (aset 329) := verifies_sound (by decide +kernel)
theorem ng329 : Good 6 (zset 329) := by
  have eq : (zset 329).erase 37=zset 327 := by decide +kernel
  exact .pivot _ _ _ _ _ 37 nd329 (by decide +kernel) (eq.symm ▸ ng327)
theorem nd330 : Data (zset 330) (tset 330) (uset 330) (hset 330) (aset 330) := verifies_sound (by decide +kernel)
theorem ng330 : Good 6 (zset 330) := by
  have eq : (zset 330).erase 20=zset 328 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 nd330 (by decide +kernel) (eq.symm ▸ ng328)
theorem nd331 : Data (zset 331) (tset 331) (uset 331) (hset 331) (aset 331) := verifies_sound (by decide +kernel)
theorem ng331 : Good 6 (zset 331) := by
  have eq : (zset 331).erase 25=zset 329 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd331 (by decide +kernel) (eq.symm ▸ ng329)
theorem nd332 : Data (zset 332) (tset 332) (uset 332) (hset 332) (aset 332) := verifies_sound (by decide +kernel)
theorem ng332 : Good 6 (zset 332) := by
  have eq : (zset 332).erase 3=zset 330 := by decide +kernel
  exact .pivot _ _ _ _ _ 3 nd332 (by decide +kernel) (eq.symm ▸ ng330)
theorem nd333 : Data (zset 333) (tset 333) (uset 333) (hset 333) (aset 333) := verifies_sound (by decide +kernel)
theorem ng333 : Good 6 (zset 333) := by
  have eq : (zset 333).erase 12=zset 332 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd333 (by decide +kernel) (eq.symm ▸ ng332)
theorem allPanels (r : R) : Good 6 (zone r) := by
  fin_cases r
  · have e : zone 0 = zset 333 := by decide +kernel
    exact e.symm ▸ ng333
  · have e : zone 1 = zset 324 := by decide +kernel
    exact e.symm ▸ ng324
  · have e : zone 2 = zset 298 := by decide +kernel
    exact e.symm ▸ ng298
  · have e : zone 3 = zset 299 := by decide +kernel
    exact e.symm ▸ ng299
  · have e : zone 4 = zset 256 := by decide +kernel
    exact e.symm ▸ ng256
  · have e : zone 5 = zset 257 := by decide +kernel
    exact e.symm ▸ ng257
  · have e : zone 6 = zset 258 := by decide +kernel
    exact e.symm ▸ ng258
  · have e : zone 7 = zset 205 := by decide +kernel
    exact e.symm ▸ ng205
  · have e : zone 8 = zset 325 := by decide +kernel
    exact e.symm ▸ ng325
  · have e : zone 9 = zset 301 := by decide +kernel
    exact e.symm ▸ ng301
  · have e : zone 10 = zset 260 := by decide +kernel
    exact e.symm ▸ ng260
  · have e : zone 11 = zset 261 := by decide +kernel
    exact e.symm ▸ ng261
  · have e : zone 12 = zset 209 := by decide +kernel
    exact e.symm ▸ ng209
  · have e : zone 13 = zset 210 := by decide +kernel
    exact e.symm ▸ ng210
  · have e : zone 14 = zset 113 := by decide +kernel
    exact e.symm ▸ ng113
  · have e : zone 15 = zset 114 := by decide +kernel
    exact e.symm ▸ ng114
  · have e : zone 16 = zset 211 := by decide +kernel
    exact e.symm ▸ ng211
  · have e : zone 17 = zset 116 := by decide +kernel
    exact e.symm ▸ ng116
  · have e : zone 18 = zset 212 := by decide +kernel
    exact e.symm ▸ ng212
  · have e : zone 19 = zset 213 := by decide +kernel
    exact e.symm ▸ ng213
  · have e : zone 20 = zset 119 := by decide +kernel
    exact e.symm ▸ ng119
  · have e : zone 21 = zset 120 := by decide +kernel
    exact e.symm ▸ ng120
  · have e : zone 22 = zset 121 := by decide +kernel
    exact e.symm ▸ ng121
  · have e : zone 23 = zset 122 := by decide +kernel
    exact e.symm ▸ ng122
  · have e : zone 24 = zset 302 := by decide +kernel
    exact e.symm ▸ ng302
  · have e : zone 25 = zset 262 := by decide +kernel
    exact e.symm ▸ ng262
  · have e : zone 26 = zset 124 := by decide +kernel
    exact e.symm ▸ ng124
  · have e : zone 27 = zset 215 := by decide +kernel
    exact e.symm ▸ ng215
  · have e : zone 28 = zset 216 := by decide +kernel
    exact e.symm ▸ ng216
  · have e : zone 29 = zset 127 := by decide +kernel
    exact e.symm ▸ ng127
  · have e : zone 30 = zset 128 := by decide +kernel
    exact e.symm ▸ ng128
  · have e : zone 31 = zset 129 := by decide +kernel
    exact e.symm ▸ ng129
  · have e : zone 32 = zset 217 := by decide +kernel
    exact e.symm ▸ ng217
  · have e : zone 33 = zset 130 := by decide +kernel
    exact e.symm ▸ ng130
  · have e : zone 34 = zset 131 := by decide +kernel
    exact e.symm ▸ ng131
  · have e : zone 35 = zset 132 := by decide +kernel
    exact e.symm ▸ ng132
  · have e : zone 36 = zset 133 := by decide +kernel
    exact e.symm ▸ ng133
  · have e : zone 37 = zset 134 := by decide +kernel
    exact e.symm ▸ ng134
  · have e : zone 38 = zset 218 := by decide +kernel
    exact e.symm ▸ ng218
  · have e : zone 39 = zset 136 := by decide +kernel
    exact e.symm ▸ ng136
  · have e : zone 40 = zset 137 := by decide +kernel
    exact e.symm ▸ ng137
  · have e : zone 41 = zset 219 := by decide +kernel
    exact e.symm ▸ ng219
  · have e : zone 42 = zset 138 := by decide +kernel
    exact e.symm ▸ ng138
  · have e : zone 43 = zset 139 := by decide +kernel
    exact e.symm ▸ ng139
  · have e : zone 44 = zset 140 := by decide +kernel
    exact e.symm ▸ ng140
  · have e : zone 45 = zset 141 := by decide +kernel
    exact e.symm ▸ ng141
  · have e : zone 46 = zset 142 := by decide +kernel
    exact e.symm ▸ ng142
  · have e : zone 47 = zset 220 := by decide +kernel
    exact e.symm ▸ ng220
  · have e : zone 48 = zset 144 := by decide +kernel
    exact e.symm ▸ ng144
  · have e : zone 49 = zset 145 := by decide +kernel
    exact e.symm ▸ ng145
  · have e : zone 50 = zset 146 := by decide +kernel
    exact e.symm ▸ ng146
  · have e : zone 51 = zset 221 := by decide +kernel
    exact e.symm ▸ ng221
  · have e : zone 52 = zset 148 := by decide +kernel
    exact e.symm ▸ ng148
  · have e : zone 53 = zset 149 := by decide +kernel
    exact e.symm ▸ ng149
  · have e : zone 54 = zset 37 := by decide +kernel
    exact e.symm ▸ ng37
  · have e : zone 55 = zset 150 := by decide +kernel
    exact e.symm ▸ ng150
  · have e : zone 56 = zset 151 := by decide +kernel
    exact e.symm ▸ ng151
  · have e : zone 57 = zset 152 := by decide +kernel
    exact e.symm ▸ ng152
  · have e : zone 58 = zset 153 := by decide +kernel
    exact e.symm ▸ ng153
  · have e : zone 59 = zset 154 := by decide +kernel
    exact e.symm ▸ ng154
  · have e : zone 60 = zset 155 := by decide +kernel
    exact e.symm ▸ ng155
  · have e : zone 61 = zset 38 := by decide +kernel
    exact e.symm ▸ ng38
  · have e : zone 62 = zset 156 := by decide +kernel
    exact e.symm ▸ ng156
  · have e : zone 63 = zset 157 := by decide +kernel
    exact e.symm ▸ ng157
  · have e : zone 64 = zset 158 := by decide +kernel
    exact e.symm ▸ ng158
  · have e : zone 65 = zset 263 := by decide +kernel
    exact e.symm ▸ ng263
  · have e : zone 66 = zset 223 := by decide +kernel
    exact e.symm ▸ ng223
  · have e : zone 67 = zset 224 := by decide +kernel
    exact e.symm ▸ ng224
  · have e : zone 68 = zset 163 := by decide +kernel
    exact e.symm ▸ ng163
  · have e : zone 69 = zset 164 := by decide +kernel
    exact e.symm ▸ ng164
  · have e : zone 70 = zset 165 := by decide +kernel
    exact e.symm ▸ ng165
  · have e : zone 71 = zset 166 := by decide +kernel
    exact e.symm ▸ ng166
  · have e : zone 72 = zset 264 := by decide +kernel
    exact e.symm ▸ ng264
  · have e : zone 73 = zset 226 := by decide +kernel
    exact e.symm ▸ ng226
  · have e : zone 74 = zset 227 := by decide +kernel
    exact e.symm ▸ ng227
  · have e : zone 75 = zset 228 := by decide +kernel
    exact e.symm ▸ ng228
  · have e : zone 76 = zset 47 := by decide +kernel
    exact e.symm ▸ ng47
  · have e : zone 77 = zset 229 := by decide +kernel
    exact e.symm ▸ ng229
  · have e : zone 78 = zset 230 := by decide +kernel
    exact e.symm ▸ ng230
  · have e : zone 79 = zset 173 := by decide +kernel
    exact e.symm ▸ ng173
  · have e : zone 80 = zset 231 := by decide +kernel
    exact e.symm ▸ ng231
  · have e : zone 81 = zset 175 := by decide +kernel
    exact e.symm ▸ ng175
  · have e : zone 82 = zset 176 := by decide +kernel
    exact e.symm ▸ ng176
  · have e : zone 83 = zset 83 := by decide +kernel
    exact e.symm ▸ ng83
  · have e : zone 84 = zset 177 := by decide +kernel
    exact e.symm ▸ ng177
  · have e : zone 85 = zset 232 := by decide +kernel
    exact e.symm ▸ ng232
  · have e : zone 86 = zset 265 := by decide +kernel
    exact e.symm ▸ ng265
  · have e : zone 87 = zset 234 := by decide +kernel
    exact e.symm ▸ ng234
  · have e : zone 88 = zset 235 := by decide +kernel
    exact e.symm ▸ ng235
  · have e : zone 89 = zset 236 := by decide +kernel
    exact e.symm ▸ ng236
  · have e : zone 90 = zset 266 := by decide +kernel
    exact e.symm ▸ ng266
  · have e : zone 91 = zset 267 := by decide +kernel
    exact e.symm ▸ ng267
  · have e : zone 92 = zset 268 := by decide +kernel
    exact e.symm ▸ ng268
  · have e : zone 93 = zset 89 := by decide +kernel
    exact e.symm ▸ ng89
  · have e : zone 94 = zset 287 := by decide +kernel
    exact e.symm ▸ ng287
  · have e : zone 95 = zset 242 := by decide +kernel
    exact e.symm ▸ ng242
  · have e : zone 96 = zset 270 := by decide +kernel
    exact e.symm ▸ ng270
  · have e : zone 97 = zset 303 := by decide +kernel
    exact e.symm ▸ ng303
  · have e : zone 98 = zset 272 := by decide +kernel
    exact e.symm ▸ ng272
  · have e : zone 99 = zset 247 := by decide +kernel
    exact e.symm ▸ ng247
  · have e : zone 100 = zset 191 := by decide +kernel
    exact e.symm ▸ ng191
  · have e : zone 101 = zset 192 := by decide +kernel
    exact e.symm ▸ ng192
  · have e : zone 102 = zset 194 := by decide +kernel
    exact e.symm ▸ ng194
  · have e : zone 103 = zset 248 := by decide +kernel
    exact e.symm ▸ ng248
  · have e : zone 104 = zset 195 := by decide +kernel
    exact e.symm ▸ ng195
  · have e : zone 105 = zset 273 := by decide +kernel
    exact e.symm ▸ ng273
  · have e : zone 106 = zset 289 := by decide +kernel
    exact e.symm ▸ ng289
  · have e : zone 107 = zset 304 := by decide +kernel
    exact e.symm ▸ ng304
  · have e : zone 108 = zset 313 := by decide +kernel
    exact e.symm ▸ ng313
  · have e : zone 109 = zset 306 := by decide +kernel
    exact e.symm ▸ ng306
  · have e : zone 110 = zset 320 := by decide +kernel
    exact e.symm ▸ ng320
  · have e : zone 111 = zset 326 := by decide +kernel
    exact e.symm ▸ ng326
  · have e : zone 112 = zset 331 := by decide +kernel
    exact e.symm ▸ ng331
theorem core (hG : sem_Gr G) {D : Dag} (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (ind : ∀ i∈ineligSet 40 D, ∀ j∈ineligSet 40 D, ¬G i j) : 73+Bzero 40 D≤D.length := by
  classical
  obtain ⟨r,e,valid,sub⟩ := envelope ind
  have hrel : sem_Comp 40 G (relabel e D) := by
    intro x
    rw [relabel_out e h.1 h.2.2 x, hc]
    unfold sem_Edge
    constructor
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e u,e v,(valid.adj u v).mpr huv,hu,hv⟩
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e.symm u,e.symm v,(valid.adj _ _).mp (by simpa using huv),
        by simpa using hu,by simpa using hv⟩
  have inc : ineligSet 40 (relabel e D) ⊆ zone r := by
    rw [relabel_ineligSet e h.1]
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact sub i hi
  have result := panelBound hG (relabel_strictLive e h) hrel inc (allPanels r)
  rw [relabel_length,relabel_Bzero e h.1] at result
  omega
theorem lowerSem (hG : sem_Gr G)
    (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
      C.eval (List.ofFn x)=true ↔ sem_Edge G x) : 73≤C.size := by
  classical
  have single (i : V) : ¬ sem_Edge G (fun k => decide (k=i)) := by
    rintro ⟨u,v,edge,hu,hv⟩
    have eu : u=i := of_decide_eq_true hu
    have ev : v=i := of_decide_eq_true hv
    subst u
    subst v
    exact hG.2.1 i edge
  have extra (i : V) : ∃ j, G i j ∧ j≠i := hG.2.2.2 i i
  have hit {i j : V} (edge : G i j) :
      sem_Edge G (fun v => decide (v=i ∨ v=j)) := ⟨i,j,edge,by simp,by simp⟩
  obtain ⟨D,ld,lim,simulation⟩ := normalize_strictLive (n:=40) C hm
    (by
      intro b
      cases b
      · obtain ⟨v,edge,-⟩ := extra 0
        exact ⟨_,by rw [Ne,Bool.not_eq_false]; exact (correct _).mpr (hit edge)⟩
      · exact ⟨fun _ => false,fun e => by
          obtain ⟨u,v,_,h,_⟩ := (correct _).mp e
          contradiction⟩)
    (by
      intro i
      refine ⟨fun k => decide (k=i),fun h => single i ((correct _).mp ?_)⟩
      rw [h]
      simp)
    (by
      intro i
      obtain ⟨j,edge,diff⟩ := extra i
      refine ⟨fun k => decide (k=j),fun k => decide (k=i ∨ k=j),?_,?_⟩
      · intro k hk
        simp [hk]
      · intro same
        apply single j
        exact (correct _).mp (same.trans ((correct _).mpr (hit edge))))
  have sem : sem_Comp 40 G D := fun x => by rw [simulation x]; exact correct x
  have ind : ∀i∈ineligSet 40 D,∀j∈ineligSet 40 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover hG ld sem ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have enriched := core hG ld sem ind
  omega

def listed : List (Nat × Nat) := [(0, 24), (0, 26), (0, 36), (0, 39), (1, 25), (1, 27), (1, 37), (2, 21), (2, 26), (2, 28), (2, 38), (3, 21), (3, 22), (3, 27), (3, 29), (3, 39), (4, 22), (4, 23), (4, 28), (4, 30), (5, 23), (5, 24), (5, 29), (5, 31), (6, 21), (6, 24), (6, 25), (6, 30), (6, 32), (7, 22), (7, 25), (7, 26), (7, 31), (7, 33), (8, 23), (8, 26), (8, 27), (8, 32), (8, 34), (9, 24), (9, 27), (9, 28), (9, 33), (9, 35), (10, 25), (10, 28), (10, 29), (10, 34), (10, 36), (11, 26), (11, 29), (11, 30), (11, 35), (11, 37), (12, 27), (12, 30), (12, 31), (12, 36), (12, 38), (13, 28), (13, 31), (13, 32), (13, 37), (13, 39), (14, 29), (14, 32), (14, 33), (14, 38), (15, 30), (15, 33), (15, 34), (15, 39), (16, 21), (16, 31), (16, 34), (16, 35), (17, 22), (17, 32), (17, 35), (17, 36), (18, 21), (18, 23), (18, 33), (18, 36), (18, 37), (19, 22), (19, 24), (19, 34), (19, 37), (19, 38), (20, 23), (20, 25), (20, 35), (20, 38), (20, 39)]
theorem shown : ∀ u v : V, G u v ↔ ((u.val,v.val)∈listed ∨ (v.val,u.val)∈listed) := by decide +kernel
theorem regular : sem_Gr G := by
  unfold sem_Gr
  decide +kernel
theorem lower (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
    C.eval (List.ofFn x)=true ↔ ∃u v : V,(u.val,v.val)∈listed ∧ x u=true ∧ x v=true) : 73≤C.size := by
  apply lowerSem regular C hm
  intro x
  rw [correct]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    exact ⟨u,v,(shown u v).mpr (Or.inl h),hu,hv⟩
  · rintro ⟨u,v,h,hu,hv⟩
    rcases (shown u v).mp h with h|h
    · exact ⟨u,v,h,hu,hv⟩
    · exact ⟨v,u,h,hv,hu⟩
end Mixed9800

namespace PEqualNP.Outside.L_meta_971_aux
variable {n : ℕ} {D : Dag}
theorem cold_factor (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs N : Finset (Fin n)) (hN : N ⊆ Bs)
    (h0 : val D (sem_ins i (sem_ind (Bs \ N))) w = false)
    (h1 : ∀ a ∈ N, val D (sem_ins i (sem_ind {a})) w = true)
    (hz : ∀ a ∈ N, val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧ val D (sem_ind (Bs \ N)) (src D (j,s)) = false ∧ supp n D (src D (j, s)) ∩ Bs = N := by
  have hJ : ∀ c, sem_Chain n D i.val c → (val D (sem_ins i (sem_ind (Bs \ N))) c = true ∨
      ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ c ∧ sem_Chain n D i.val (src D (j, !s)) ∧
        fanout D (src D (j, !s)) = 1 ∧ val D (sem_ind (Bs \ N)) (src D (j, s)) = false) := by
    intro c hc
    induction hc with
    | refl => left; rw [val_input D _ _ i.isLt]; exact sem_ins_self i _
    | tail hab hbc ih =>
      obtain ⟨j, s, hj, rfl, rfl⟩ := sem_step_iff.mp hbc.1
      have hlt := sem_src_lt hS hj s
      rcases ih with hy | ⟨j', s', hj', ht', hle, hc', hf', hv'⟩
      · cases ht : tag D j
        · left
          rw [sem_val_gate_src hS _ hj s, ht, gop_false, hy]
          rfl
        · by_cases hq : val D (sem_ins i (sem_ind (Bs \ N))) (src D (j, !s)) = true
          · left
            rw [sem_val_gate_src hS _ hj s, ht, gop_true, hy, hq]
            rfl
          · right
            refine ⟨j, !s, hj, ht, le_refl _, by rw [Bool.not_not]; exact hab,
              by rw [Bool.not_not]; exact hbc.2, ?_⟩
            by_contra hc2
            rw [Bool.not_eq_false] at hc2
            exact hq (val_mono hS _ _ (sem_ins_ge i _) _ hc2)
      · right
        exact ⟨j', s', hj', ht', by omega, hc', hf', hv'⟩
  rcases hJ w hch with hy | ⟨j, s, hj, ht, hle, hc, hf, hv⟩
  · rw [h0] at hy
    exact absurd hy Bool.false_ne_true
  · refine ⟨j, s, hj, ht, hle, hc, hv, ?_⟩
    have hchg : sem_Chain n D i.val (n + j) :=
      Relation.ReflTransGen.tail hc ⟨sem_step_src hj (!s), hf⟩
    ext a
    rw [Finset.mem_inter]
    constructor
    · rintro ⟨ha1, ha2⟩
      by_contra haN
      have := sem_val_of_supp hS ha1 (x := sem_ind (Bs \ N))
        (by simp [sem_ind, ha2, haN])
      rw [hv] at this
      exact Bool.false_ne_true this
    · intro haN
      refine ⟨?_, hN haN⟩
      have hgne : val D (sem_ind {a}) (n + j) ≠ val D (sem_ins i (sem_ind {a})) (n + j) := by
        intro heq
        have h2 := sem_dom_eq_at hS _ _ i (sem_ins_agree i (sem_ind {a})) (n + j) w
          (sem_chain_dom_at hS hchg hle) heq
        rw [hz a haN, h1 a haN] at h2
        exact Bool.false_ne_true h2
      have hgy : val D (sem_ins i (sem_ind {a})) (n + j) = true := by
        by_contra hc2
        rw [Bool.not_eq_true] at hc2
        apply hgne
        rw [hc2]
        by_contra hc3
        rw [Bool.not_eq_false] at hc3
        rw [val_mono hS _ _ (sem_ins_ge i _) _ hc3] at hc2
        exact Bool.noConfusion hc2
      rw [sem_val_gate_src hS _ hj s, ht, gop_true, Bool.and_eq_true] at hgy
      have hind := sem_sibling_indep hS i hj s hc hf _ _ (sem_ins_agree i (sem_ind {a}))
      rw [hgy.1, sem_ind_single] at hind
      exact mem_supp.mpr hind


end PEqualNP.Outside.L_meta_971_aux
namespace PEqualNP.Outside.L_meta_971_aux
variable {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
theorem cold_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      val D (sem_ind (Bs \ (Bs.filter (fun a => by classical exact (decide (G i a) = true))))) (src D (j,s)) = false ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hv, hsupp⟩ := cold_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, by simpa using hv, fun a ha => ?_⟩
  constructor
  · intro has
    have : a ∈ supp n D (src D (j, s)) ∩ Bs := Finset.mem_inter.mpr ⟨has, ha⟩
    rw [hsupp, Finset.mem_filter] at this
    exact this.2
  · intro hia
    have : a ∈ Bs.filter (fun a => G i a) := Finset.mem_filter.mpr ⟨ha, hia⟩
    rw [← hsupp] at this
    exact (Finset.mem_inter.mp this).1

theorem cold_shared (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (Bs : Finset (Fin n)) (hBs : ∀ a ∈ Bs, ∀ b ∈ Bs, ¬ G a b) {i j : Fin n} {w : ℕ}
    (hch : sem_Chain n D i.val w) (hdj : sem_Dom n D w j.val)
    (hnsub : ∃ a ∈ Bs, G j a ∧ ¬ G i a) :
    ∃ k s, k < D.length ∧ tag D k = true ∧ n + k ≤ w ∧
      sem_Chain n D i.val (src D (k, !s)) ∧
      val D (sem_ind (Bs \ (Bs.filter (fun a => by classical exact (decide (G i a) = true))))) (src D (k,s)) = false ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (k, s)) ↔ G i a) := by
  classical
  have hX0 : ¬ sem_Edge G (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) := by
    intro hc
    rcases sem_ins_ind_edge hG hc with ⟨a, ha, hia⟩ | ⟨a, ha, b, hb, hab⟩
    · exact (Finset.mem_filter.mp ha).2 hia
    · exact hBs a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  obtain ⟨a0, ha0, hja0, hia0⟩ := hnsub
  have hX1 : sem_Edge G (sem_ins j (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a))))) :=
    ⟨j, a0, hja0, sem_ins_self j _, by simp [sem_ins, sem_ind, ha0, hia0]⟩
  have hwX := (sem_dom_split hS hC _ j w hdj hX0 hX1).1
  refine cold_at hS i w hch Bs (fun S hS1 hS2 => ?_) (fun a _ hia => ?_)
  · by_contra hc
    rw [Bool.not_eq_false] at hc
    have hmono := val_mono hS (sem_ins i (sem_ind S))
      (sem_ins i (sem_ind (Bs.filter (fun a => ¬ G i a)))) (fun k hk => by
        simp only [sem_ins, sem_ind, Bool.or_eq_true, decide_eq_true_eq] at hk ⊢
        rcases hk with hk | hk
        · exact Or.inl hk
        · exact Or.inr (Finset.mem_filter.mpr ⟨hS1 hk, hS2 k hk⟩)) w hc
    rw [hwX] at hmono
    exact Bool.false_ne_true hmono
  · have h2 := sem_dom_split hS hC (sem_ind {a}) i w (sem_chain_dom hS hch)
      (by rw [sem_ind_single]; exact sem_single_no_edge hG a)
      ⟨i, a, hia, sem_ins_self i _, by simp [sem_ins, sem_ind]⟩
    exact ⟨h2.2, h2.1⟩


end PEqualNP.Outside.L_meta_971_aux
namespace Exposure9800
set_option maxHeartbeats 0
set_option maxRecDepth 20000
open PEqualNP.Outside.L_meta_971_aux
variable {n : ℕ} {D : Dag}
abbrev Test (n : ℕ) := Fin n → Bool
def sees (D : Dag) (row : Fin n → Test n) (a : Fin n) (w : ℕ) := val D (row a) w = true
instance (D : Dag) (row : Fin n → Test n) (a : Fin n) (w : ℕ) : Decidable (sees D row a w) := by unfold sees; infer_instance
def credits (D : Dag) (row : Fin n → Test n) (off : Test n) (P : Finset (Fin n)) :=
  (Finset.range D.length).filter fun j => tag D j = false ∧ val D off (n+j) = false ∧
    ∃ a∈P, sees D row a (opA D j) ∧ ∃ b∈P, a≠b ∧ sees D row b (opB D j)

theorem exposure_step (hs : Strict n D) (row : Fin n → Test n) (off : Test n)
    (inputs : ∀ (i a b : Fin n), off i=false → row a i=true → row b i=true → a=b)
    {P : Finset (Fin n)} {x : Fin n} (hx : x∉P) {w : ℕ} (cold : val D off w=false)
    (sx : sees D row x w) (someP : ∃y∈P,sees D row y w) :
    (credits D row off P).card < (credits D row off (insert x P)).card := by
  classical
  let joint (v : ℕ) := val D off v=false ∧ sees D row x v ∧ ∃y∈P,sees D row y v
  have ex : ∃v, joint v := ⟨w,cold,sx,someP⟩
  have spec := Nat.find_spec ex
  have minimal : ∀ v, v < Nat.find ex → ¬joint v := fun v hv => Nat.find_min ex hv
  generalize Nat.find ex = q at spec minimal
  obtain ⟨cq,xq,y,yp,yq⟩ := spec
  have qlarge : n≤q := by
    by_contra! h
    change val D (row x) q = true at xq
    change val D (row y) q = true at yq
    rw [val_input D _ q h] at cq xq yq
    exact hx ((inputs ⟨q,h⟩ x y cq xq yq).symm ▸ yp)
  have qsmall : q < n+D.length := by
    by_contra! hr
    change val D (row x) q = true at xq
    rw [val_ge D _ q hr] at xq
    contradiction
  obtain ⟨j,rfl⟩ : ∃j,q=n+j := ⟨q-n,by omega⟩
  have hj : j<D.length := by omega
  obtain ⟨al,bl,-⟩ := hs j hj
  have sub : credits D row off P ⊆ credits D row off (insert x P) := by
    intro k hk
    obtain ⟨kr,kt,kc,a,ap,sa,b,bp,ab,sb⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨kr,kt,kc,a,Finset.mem_insert_of_mem ap,sa,
      b,Finset.mem_insert_of_mem bp,ab,sb⟩
  apply Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩)
  intro eqm
  change val D (row x) (n+j) = true at xq
  change val D (row y) (n+j) = true at yq
  have xy : x≠y := fun h => hx (h ▸ yp)
  have xr : x∈insert x P := Finset.mem_insert_self _ _
  have yr : y∈insert x P := Finset.mem_insert_of_mem yp
  cases ht : tag D j
  · rw [val_gate hs _ j hj,ht,gop_false,Bool.or_eq_true] at xq yq
    have parts : val D off (opA D j)=false ∧ val D off (opB D j)=false := by
      simpa [val_gate hs _ j hj,ht,gop_false] using cq
    have contradictionAt (now : j∈credits D row off (insert x P)) :
        (∃a∈P,sees D row a (opA D j)) ∧ (∃b∈P,sees D row b (opB D j)) := by
      rw [←eqm] at now
      obtain ⟨_,_,_,a,ap,sa,b,bp,_,sb⟩ := Finset.mem_filter.mp now
      exact ⟨⟨a,ap,sa⟩,⟨b,bp,sb⟩⟩
    rcases xq with xa|xb <;> rcases yq with ya|yb
    · exact minimal _ al ⟨parts.1,xa,y,yp,ya⟩
    · have opp := contradictionAt (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,ht,cq,x,xr,xa,y,yr,xy,yb⟩)
      exact minimal _ al ⟨parts.1,xa,opp.1⟩
    · have opp := contradictionAt (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,ht,cq,y,yr,ya,x,xr,xy.symm,xb⟩)
      exact minimal _ bl ⟨parts.2,xb,opp.2⟩
    · exact minimal _ bl ⟨parts.2,xb,y,yp,yb⟩
  · rw [val_gate hs _ j hj,ht,gop_true,Bool.and_eq_true] at xq yq
    by_cases first : val D off (opA D j)=false
    · exact minimal _ al ⟨first,xq.1,y,yp,yq.1⟩
    · have second : val D off (opB D j)=false := by
        cases hA : val D off (opA D j) <;> simp_all [val_gate hs off j hj,ht,gop_true]
      exact minimal _ bl ⟨second,xq.2,y,yp,yq.2⟩

theorem exposure_price (hs : Strict n D) (row : Fin n → Test n) (off : Test n)
    (inputs : ∀ (i a b : Fin n), off i=false → row a i=true → row b i=true → a=b)
    (P : Finset (Fin n)) (w : ℕ) (cold : val D off w=false) (seen : ∀a∈P,sees D row a w) :
    P.card ≤ (credits D row off P).card+1 := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert x P hx ih =>
    have sub (v) (hv : v∈P) := seen v (Finset.mem_insert_of_mem hv)
    by_cases ne : P.Nonempty
    · obtain ⟨y,hy⟩ := ne
      have more := exposure_step hs row off inputs hx cold (seen x (Finset.mem_insert_self _ _)) ⟨y,hy,sub y hy⟩
      have prev := ih sub
      rw [Finset.card_insert_of_notMem hx]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty.mp ne]
      simp

open Geometry9798
def lines : Finset V := Finset.univ.filter fun i => 21≤i.val
def neighborhood (l : V) : Finset V := Finset.univ.filter fun v => G l v
def pts : Finset V := Finset.univ.filter fun i => i.val<21
def outer (l : V) : Test 40 := sem_ind (pts \ neighborhood l)
def pointsOn : Test 40 := fun i => decide (i.val<21)
def withLine (l : V) : Test 40 := fun i => pointsOn i || decide (i=l)
def bankFees (D : Dag) (l : V) := credits D single (outer l) (neighborhood l)
def outputFees (D : Dag) := credits D withLine pointsOn lines
def conjunctions (D : Dag) := (Finset.range D.length).filter fun j => tag D j=true

def Bank (D : Dag) : Prop :=
  ∀ l∈lines, ∃ w, val D (outer l) w=false ∧ ∀v∈neighborhood l, sees D single v w

theorem graphData : lines.card = 19 ∧
   (∀l∈lines, (neighborhood l).card=5) ∧
   (∀l∈lines,∀i∈neighborhood l,pointsOn i=true) ∧
   (∀ l∈lines, ∀ m∈lines, l≠m → ∀a∈neighborhood l,∀b∈neighborhood l,
     a∈neighborhood m → b∈neighborhood m → a=b) ∧
   (∀ u v : V,G u v → ¬(pointsOn u=true ∧ pointsOn v=true)) ∧
   (∀l∈lines,∃p, G p l ∧ pointsOn p=true) := by decide +kernel

theorem credit_rows {row : V → Test 40} {off : Test 40} {P : Finset V}
    {D : Dag} (hs : Strict 40 D) {j : ℕ} (hj : j∈credits D row off P) :
    j<D.length ∧ tag D j=false ∧ val D off (40+j)=false ∧
      ∃a∈P, ∃b∈P, a≠b ∧ sees D row a (40+j) ∧ sees D row b (40+j) := by
  obtain ⟨bound,ht,hc,a,ha,sa,b,hb,ab,sb⟩ := Finset.mem_filter.mp hj
  have lim := Finset.mem_range.mp bound
  refine ⟨lim,ht,hc,a,ha,b,hb,ab,?_,?_⟩
  · unfold sees at *
    rw [val_gate hs _ j lim,ht,gop_false,sa]
    rfl
  · unfold sees at *
    rw [val_gate hs _ j lim,ht,gop_false,sb]
    simp

theorem supported {D : Dag} (hs : Strict 40 D) {l v : V} {w : ℕ}
    (hv : v∈pts) (cold : val D (outer l) w=false) (seen : sees D single v w) : v∈neighborhood l := by
  by_contra no
  have hot : outer l v=true := by simp [outer,sem_ind,hv,no]
  have lit := val_mono hs (single v) (outer l) (sem_single_le hot) w seen
  rw [cold] at lit
  contradiction

theorem bank_mass {D : Dag} (hs : Strict 40 D) (bank : Bank D) : 76≤(lines.biUnion (bankFees D)).card := by
  classical
  obtain ⟨nlines,degree,left,linear,offGraph,hotGraph⟩ := graphData
  have separate : ∀ l∈lines,∀ m∈lines,l≠m → Disjoint (bankFees D l) (bankFees D m) := by
    intro l hl m hm ne
    rw [Finset.disjoint_left]
    intro j jl jm
    obtain ⟨_,_,_,a,ha,b,hb,ab,sa,sb⟩ := credit_rows hs jl
    have cold := (credit_rows hs jm).2.2.1
    have pa : a∈pts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (left l hl a ha)⟩
    have pb : b∈pts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (left l hl b hb)⟩
    exact ab (linear l hl m hm ne a ha b hb (supported hs pa cold sa) (supported hs pb cold sb))
  have bankFour (l : V) (hl : l∈lines) : 4 ≤ (bankFees D l).card := by
    obtain ⟨w,cold,seen⟩ := bank l hl
    have amount := exposure_price hs single (outer l) (by
      intro i a b _ ha hb
      simp [single] at ha hb
      exact ha.symm.trans hb) (neighborhood l) w cold seen
    rw [degree l hl] at amount
    change 4≤(credits D single (outer l) (neighborhood l)).card
    omega
  let B := lines.biUnion (bankFees D)
  have bankTotal : 76≤B.card := by
    change 76 ≤ (lines.biUnion (bankFees D)).card
    rw [Finset.card_biUnion (by intro i hi j hj hne; exact separate i hi j hj hne)]
    have bound := Finset.sum_le_sum bankFour
    simpa [nlines] using bound
  exact bankTotal

theorem bank_price {D : Dag} (hs : Strict 40 D) (hc : sem_Comp 40 G D) (bank : Bank D) :
    94 + (conjunctions D).card ≤ D.length := by
  classical
  obtain ⟨nlines,degree,left,linear,offGraph,hotGraph⟩ := graphData
  let B := lines.biUnion (bankFees D)
  have bankTotal : 76≤B.card := bank_mass hs bank
  have coldOut : val D pointsOn (outW 40 D)=false := by
    cases h : val D pointsOn (outW 40 D) with
    | false => rfl
    | true =>
      obtain ⟨u,v,e,hu,hv⟩ := (hc pointsOn).mp h
      exact False.elim (offGraph u v e ⟨hu,hv⟩)
  have outCost := exposure_price hs withLine pointsOn (by
    intro i a b cold sa sb
    simp only [withLine,cold,Bool.false_or,decide_eq_true_eq] at sa sb
    exact sa.symm.trans sb) lines (outW 40 D) coldOut (by
      intro l hl
      obtain ⟨p,edge,hp⟩ := hotGraph l hl
      apply (hc _).mpr
      exact ⟨p,l,edge,by simp [withLine,hp],by simp [withLine]⟩)
  rw [nlines] at outCost
  have outLow : 18≤(outputFees D).card := by unfold outputFees; omega
  have apart : Disjoint B (outputFees D) := by
    rw [Finset.disjoint_left]
    intro j hB hO
    obtain ⟨l,hl,hj⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨_,_,_,a,ha,b,hb,ab,sa,sb⟩ := credit_rows hs hj
    have hot := val_mono hs (single a) pointsOn (sem_single_le (left l hl a ha)) (40+j) sa
    rw [(credit_rows hs hO).2.2.1] at hot
    contradiction
  have filtered (j : ℕ) (hj : j∈B∪outputFees D) : j<D.length ∧ tag D j=false := by
    rcases Finset.mem_union.mp hj with hb|ho
    · obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp hb
      exact ⟨(credit_rows hs hl).1,(credit_rows hs hl).2.1⟩
    · exact ⟨(credit_rows hs ho).1,(credit_rows hs ho).2.1⟩
  have separateAND : Disjoint (B∪outputFees D) (conjunctions D) := by
    rw [Finset.disjoint_left]
    intro j hj hp
    have ht := (filtered j hj).2
    have opp := (Finset.mem_filter.mp hp).2
    simp_all
  have sub : (B∪outputFees D)∪conjunctions D ⊆ Finset.range D.length := by
    intro j hj
    rcases Finset.mem_union.mp hj with h|h
    · exact Finset.mem_range.mpr (filtered j h).1
    · exact (Finset.mem_filter.mp h).1
  have total := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint separateAND,Finset.card_union_of_disjoint apart,Finset.card_range] at total
  omega

def LineSelector (D : Dag) (l : V) (j : ℕ) : Prop :=
   j<D.length ∧ tag D j=true ∧ ∃s : Bool, src D (j,s)=l.val ∧
     val D (outer l) (src D (j,!s))=false ∧
     (∀p∈neighborhood l,sees D single p (src D (j,!s)))

theorem selector_price {D : Dag} (hs : Strict 40 D) (hc : sem_Comp 40 G D)
    (selects : ∀l∈lines,∃j,LineSelector D l j) : 113≤D.length := by
  classical
  choose! pick selects' using selects
  have bank : Bank D := by
    intro l hl
    obtain ⟨_,_,s,_,cold,seen⟩ := selects' l hl
    exact ⟨_,cold,seen⟩
  have diff : Set.InjOn pick (↑lines) := by
    intro l hl m hm eqidx
    obtain ⟨_,_,s,raw,_,seen⟩ := selects' l hl
    obtain ⟨_,_,t,raw',_,_⟩ := selects' m hm
    rw [←eqidx] at raw'
    by_cases side : s=t
    · rw [←side] at raw'
      exact Fin.ext (raw.symm.trans raw')
    · have flip : t=(!s) := by cases s <;> cases t <;> simp_all
      rw [flip] at raw'
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by rw [graphData.2.1 l hl]; decide : 0<(neighborhood l).card)
      have hot := seen p hp
      change val D (single p) (src D (pick l,!s))=true at hot
      rw [raw',val_input D _ _ m.isLt] at hot
      have eq : m=p := of_decide_eq_true hot
      have pm := graphData.2.2.1 l hl p hp
      have small : p.val<21 := of_decide_eq_true pm
      have large := (Finset.mem_filter.mp hm).2
      change 21≤m.val at large
      rw [eq] at large
      omega
  have subset : lines.image pick ⊆ conjunctions D := by
    intro j hj
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨idx,tag,-⟩ := selects' l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr idx,tag⟩
  have lower := Finset.card_le_card subset
  rw [Finset.card_image_of_injOn diff,graphData.1] at lower
  have price := bank_price hs hc bank
  omega


theorem chainData : pts.card=21 ∧ (∀ l∈lines, neighborhood l ⊆ pts) ∧
    (∀p∈pts,∃l∈lines,G p l) ∧ (∀l∈lines,∃p∈pts,G l p) ∧
    (∀ l∈lines, ¬ sem_Edge G (sem_ins l (outer l)) ∧ ∀p∈neighborhood l,
      sem_Edge G (sem_ins l (sem_ind {p})) ∧ ¬sem_Edge G (sem_ind {p})) := by
  unfold sem_Edge
  decide +kernel

theorem chain_bank {D : Dag} (hg : sem_Gr G) (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (hz : Bzero 40 D=0) (mode : lines ⊆ ineligSet 40 D) : Bank D := by
  intro l hl
  obtain ⟨-,incl,_,_,tests⟩ := chainData
  obtain ⟨neg,pos⟩ := tests l hl
  have off : val D (sem_ins l (outer l)) (outW 40 D)=false := by
    cases v : val D (sem_ins l (outer l)) (outW 40 D) with
    | false => rfl
    | true => exact False.elim (neg ((hc _).mp v))
  obtain ⟨j,s,-,-,-,-,cold,mask⟩ := cold_factor h.1 l _ (sem_noempty_chain_out hg h hc hz (mode hl))
    pts (neighborhood l) (incl l hl) off (fun a ha => (hc _).mpr (pos a ha).1) (by
      intro a ha
      cases v : val D (sem_ind {a}) (outW 40 D) with
      | false => rfl
      | true => exact False.elim ((pos a ha).2 ((hc _).mp v)))
  refine ⟨_,cold,?_⟩
  intro p hp
  rw [←mask] at hp
  exact mem_supp.mp (Finset.mem_inter.mp hp).1

theorem chain_price {D : Dag} (hg : sem_Gr G) (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (hz : Bzero 40 D=0) (mode : lines ⊆ ineligSet 40 D) : 113≤D.length := by
  classical
  have bank := chain_bank hg h hc hz mode
  obtain ⟨pcount,pin,active,nbl,-⟩ := chainData
  have ps : pts ⊆ eligSet 40 D := by
    intro p hp
    obtain ⟨l,hl,ed⟩ := active p hp
    exact (sem_elig_cover hg h hc ed).resolve_right (Finset.mem_sdiff.mp (mode hl)).2
  have el := Finset.card_le_card ps
  rw [pcount] at el
  obtain ⟨pos,hp⟩ := k4_assigned hg h hc
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hg h.1 hc
  have slot := k4_exits_ge hp pts lines (fun l hl => ⟨mode hl,nbl l hl⟩)
  have nex := Finset.card_le_card slot.1
  rw [slot.2,graphData.1] at nex
  have sub : lines.biUnion (bankFees D) ⊆ merges 40 D (carrierT 40 D pts) := by
    intro j hj
    obtain ⟨l,hl,jl⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hr,tag,_,a,ha,sa,b,hb,_,sb⟩ := Finset.mem_filter.mp jl
    have ja := Finset.mem_range.mp hr
    have keep {v : V} {w : ℕ} (hv : v∈neighborhood l) (sw : sees D single v w) : w∈carrierT 40 D pts :=
      k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨mem_supp.mpr sw,pin l hl hv⟩⟩
    have aa : sees D single a (40+j) := by
      unfold sees at *
      rw [val_gate h.1 _ j ja,tag,gop_false,sa]
      rfl
    exact Finset.mem_filter.mpr ⟨hr,keep ha aa,keep ha sa,keep hb sb⟩
  have mergeCost := (bank_mass h.1 bank).trans (Finset.card_le_card sub)
  have budget := k4_budget hg h hc b hb pts
  rw [pcount] at budget
  have raw := surplus_identity h
  have plus := Bplus_le_total 40 D
  omega

theorem line_chain {D : Dag} (hg : sem_Gr G) (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    {l : V} (hl : l∈lines) (chain : sem_Chain 40 D l.val (outW 40 D)) :
    ∃ w, val D (outer l) w=false ∧ ∀v∈neighborhood l,sees D single v w := by
  obtain ⟨-,incl,_,_,tests⟩ := chainData
  obtain ⟨neg,pos⟩ := tests l hl
  have off : val D (sem_ins l (outer l)) (outW 40 D)=false := by
    cases v : val D (sem_ins l (outer l)) (outW 40 D) with
    | false => rfl
    | true => exact False.elim (neg ((hc _).mp v))
  obtain ⟨j,s,-,-,-,-,cold,mask⟩ := cold_factor h.1 l _ chain
    pts (neighborhood l) (incl l hl) off (fun a ha => (hc _).mpr (pos a ha).1) (by
      intro a ha
      cases v : val D (sem_ind {a}) (outW 40 D) with
      | false => rfl
      | true => exact False.elim ((pos a ha).2 ((hc _).mp v)))
  refine ⟨_,cold,?_⟩
  intro p hp
  rw [←mask] at hp
  exact mem_supp.mp (Finset.mem_inter.mp hp).1


def Ready (D : Dag) (l : V) : Prop := ∃ w, val D (outer l) w=false ∧
    ∀v∈neighborhood l,sees D single v w
noncomputable def absent (D : Dag) : Finset V := by classical exact lines.filter (fun l => ¬Ready D l)
theorem absent_mem {D : Dag} {l : V} : l∈absent D ↔ l∈lines ∧ ¬Ready D l := by classical simp [absent]

theorem incomparable : ∀ l∈lines,∀m∈lines,l≠m → ∃ a∈pts,G m a ∧ ¬G l a := by decide +kernel
theorem independent : ∀ a∈pts,∀ b∈pts,¬G a b := by decide +kernel

theorem loss {D : Dag} (hg : sem_Gr G) (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (mode : lines ⊆ ineligSet 40 D) : (absent D).card ≤ Bzero 40 D := by
  classical
  have hub : ∀ l∈absent D, ∃ w, sem_Chain 40 D l.val w ∧ 2≤fanout D w ∧ supp 40 D w=∅ := by
    intro l hl
    obtain ⟨inside,miss⟩ := absent_mem.mp hl
    rcases sem_inelig_reach hg h hc (mode inside) with chain|q
    · exact (miss (line_chain hg h hc inside chain)).elim
    · exact q
  choose! w hw using hub
  have inj : Set.InjOn w (↑(absent D)) := by
    intro l hl m hm eqw
    by_contra ne
    obtain ⟨inside,miss⟩ := absent_mem.mp hl
    obtain ⟨ch,-⟩ := hw l hl
    obtain ⟨cm,-⟩ := hw m hm
    rw [←eqw] at cm
    obtain ⟨j,t,_,_,_,_,cold,hit⟩ := cold_shared hg h.1 hc pts independent ch
      (sem_chain_dom h.1 cm) (incomparable l inside m (absent_mem.mp hm).1 ne)
    have eq : (pts.filter (fun a => by classical exact (decide (G l a) = true)))=neighborhood l := by
      ext a
      constructor
      · intro ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (Finset.mem_filter.mp ha).2⟩
      · intro ha
        exact Finset.mem_filter.mpr ⟨chainData.2.1 l inside ha,decide_eq_true (Finset.mem_filter.mp ha).2⟩
    apply miss
    refine ⟨src D (j,t),?_,?_⟩
    · simpa only [outer,eq] using cold
    · intro a ha
      exact mem_supp.mp ((hit a (chainData.2.1 l inside ha)).mpr (Finset.mem_filter.mp ha).2)
  let Z := (absent D).image w
  have sub : Z ⊆ (inner 40 D).filter (fun v => ¬ (supp 40 D v).Nonempty) := by
    intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    exact sem_bzero_mem h.1 (hw l hl).2.1 (hw l hl).2.2
  have sum : Z.card ≤ Bzero 40 D := by
    calc Z.card = ∑ _v ∈ Z, 1 := by simp
         _ ≤ ∑ v ∈ Z, (fanout D v - 1) := by
           apply Finset.sum_le_sum
           intro v hv
           obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
           have fan := (hw l hl).2.1
           omega
         _ ≤ Bzero 40 D := Finset.sum_le_sum_of_subset sub
  simpa only [Z,Finset.card_image_of_injOn inj] using sum
theorem bank_subset {D : Dag} (hs : Strict 40 D) (L : Finset V) (sub : L ⊆ lines) (bank : ∀ l∈L,Ready D l) : 4*L.card≤(L.biUnion (bankFees D)).card := by
  classical
  obtain ⟨nlines,degree,left,linear,offGraph,hotGraph⟩ := graphData
  have separate : ∀ l∈L,∀ m∈L,l≠m → Disjoint (bankFees D l) (bankFees D m) := by
    intro l hl m hm ne
    rw [Finset.disjoint_left]
    intro j jl jm
    obtain ⟨_,_,_,a,ha,b,hb,ab,sa,sb⟩ := credit_rows hs jl
    have cold := (credit_rows hs jm).2.2.1
    have pa : a∈pts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (left l (sub hl) a ha)⟩
    have pb : b∈pts := Finset.mem_filter.mpr ⟨Finset.mem_univ _,of_decide_eq_true (left l (sub hl) b hb)⟩
    exact ab (linear l (sub hl) m (sub hm) ne a ha b hb (supported hs pa cold sa) (supported hs pb cold sb))
  have bankFour (l : V) (hl : l∈L) : 4 ≤ (bankFees D l).card := by
    obtain ⟨w,cold,seen⟩ := bank l hl
    have amount := exposure_price hs single (outer l) (by
      intro i a b _ ha hb
      simp [single] at ha hb
      exact ha.symm.trans hb) (neighborhood l) w cold seen
    rw [degree l (sub hl)] at amount
    change 4≤(credits D single (outer l) (neighborhood l)).card
    omega
  let B := L.biUnion (bankFees D)
  have bankTotal : 4*L.card≤B.card := by
    change 4*L.card ≤ (L.biUnion (bankFees D)).card
    rw [Finset.card_biUnion (by intro i hi j hj hne; exact separate i hi j hj hne)]
    have bound := Finset.sum_le_sum bankFour
    simpa [Nat.mul_comm] using bound
  exact bankTotal

theorem price_with_loss {D : Dag} (hg : sem_Gr G) (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (mode : lines ⊆ ineligSet 40 D) : 113≤D.length+3*Bzero 40 D := by
  classical
  let L := lines \ absent D
  have subL : L ⊆ lines := Finset.sdiff_subset
  have bank : ∀ l∈L,Ready D l := by
    intro l hl
    obtain ⟨mem,notin⟩ := Finset.mem_sdiff.mp hl
    by_contra neg
    exact notin (absent_mem.mpr ⟨mem,neg⟩)
  have dis := loss hg h hc mode
  have toll := Finset.card_sdiff_add_card_eq_card (show absent D ⊆ lines from fun _ hv => (absent_mem.mp hv).1)
  change L.card+_=_ at toll
  rw [graphData.1] at toll
  obtain ⟨pcount,pin,active,nbl,-⟩ := chainData
  have ps : pts ⊆ eligSet 40 D := by
    intro p hp
    obtain ⟨l,hl,ed⟩ := active p hp
    exact (sem_elig_cover hg h hc ed).resolve_right (Finset.mem_sdiff.mp (mode hl)).2
  have el := Finset.card_le_card ps
  rw [pcount] at el
  obtain ⟨pos,hp⟩ := k4_assigned hg h hc
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hg h.1 hc
  have slot := k4_exits_ge hp pts lines (fun l hl => ⟨mode hl,nbl l hl⟩)
  have nex := Finset.card_le_card slot.1
  rw [slot.2,graphData.1] at nex
  have sub : L.biUnion (bankFees D) ⊆ merges 40 D (carrierT 40 D pts) := by
    intro j hj
    obtain ⟨l,hl,jl⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hr,tag,_,a,ha,sa,b,hb,_,sb⟩ := Finset.mem_filter.mp jl
    have ja := Finset.mem_range.mp hr
    have keep {v : V} {w : ℕ} (hv : v∈neighborhood l) (sw : sees D single v w) : w∈carrierT 40 D pts :=
      k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨mem_supp.mpr sw,pin l (subL hl) hv⟩⟩
    have aa : sees D single a (40+j) := by
      unfold sees at *
      rw [val_gate h.1 _ j ja,tag,gop_false,sa]
      rfl
    exact Finset.mem_filter.mpr ⟨hr,keep ha aa,keep ha sa,keep hb sb⟩
  have mergeCost := (bank_subset h.1 L subL bank).trans (Finset.card_le_card sub)
  have budget := k4_budget hg h hc b hb pts
  rw [pcount] at budget
  have raw := surplus_identity h
  have plus := totalSurplus_split 40 D
  omega


end Exposure9800

namespace Combined9800
open Geometry9798 Exposure9800 PEqualNP.Outside.L_meta_971_aux
theorem at_least_83 {D : Dag} (h : StrictLive 40 D) (hc : sem_Comp 40 G D)
    (mode : lines ⊆ ineligSet 40 D) : 83 ≤ D.length := by
  have ind : ∀i∈ineligSet 40 D,∀j∈ineligSet 40 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover Mixed9800.regular h hc ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have lo := Mixed9800.core Mixed9800.regular h hc ind
  have hi := price_with_loss Mixed9800.regular h hc mode
  omega
end Combined9800

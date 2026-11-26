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

namespace Geometry17245
set_option maxRecDepth 20000
set_option maxHeartbeats 0
abbrev V := Fin 26
abbrev R := Fin 26
abbrev L := Fin 13
abbrev K := Fin 39
def adj : Array Nat := #[0x416000,0x220a000,0x3104000,0x1882000,0x2c40000,0x1620000,0xb10000,0x588000,0x2c4000,0x162000,0x20b0000,0x1058000,0x82c000,0x20b,0x1105,0x1882,0xc41,0x1620,0xb10,0x588,0x2c4,0x162,0xb1,0x1058,0x82c,0x416]
def G (u v : V) := ((adj[u.val]?).getD 0).testBit v.val = true
instance (u v : V) : Decidable (G u v) := by unfold G; infer_instance
def left (u : V) := u.val < 13
instance (v : V) : Decidable (left v) := by unfold left; infer_instance

structure Valid (f : V → V) : Prop where
  inj : Function.Injective f
  side : ∀ v, left (f v) ↔ left v
  adj : ∀ u v, G (f u) (f v) ↔ G u v

theorem validId : Valid id := ⟨fun _ _ h => h,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩
theorem validComp {f g : V → V} (hf : Valid f) (hg : Valid g) : Valid (g ∘ f) :=
  ⟨hg.inj.comp hf.inj,fun v => (hg.side (f v)).trans (hf.side v),
   fun u v => (hg.adj (f u) (f v)).trans (hf.adj u v)⟩
def maps : Array Nat := #[0x338bdab49ca307b9ac5a928398a418820,0x317b56939460f7372062d4941cc520c41,0x2f6ad2728c1ee6e7010316a4a0e629062,0x2d5a4e5183dcdce2e20818b5250731483,0x2b49ca307b9b9c5ec31040c5a928398a4,0x2939460f73738bdaa41882062d4941cc5,0x2728c1ee6e717b568520c410316a4a0e6,0x25183dcdce2f6ad266290620818b52507,0x2307b9b9c5ed5a4e47314831040c5a928,0x20f73738bdab49ca28398a41882062d49,0x1ee6e717b56939460941cc520c410316a,0x1cdce2f6ad2728c1ea4a0e6290620818b,0x1b9c5ed5a4e5183dcb52507314831040c,0x2f48bb1593f369c1aa3902b4144c49860,0x2d3836f48bb1593f2b4144c4986051c81,0x2b27e6d3836f48bb0c4986051c815a0a2,0x291762b27e6d3836e051c815a0a2624c3,0x2706de91762b27e6c15a0a2624c3028e4,0x24fcda706de91762a2624c3028e40ad05,0x22ec564fcda706de83028e40ad0513126,0x20dbd22ec564fcda640ad051312618147,0x1f9b4e0dbd22ec5645131261814720568,0x1d8ac9f9b4e0dbd226181472056828989,0x1b7a45d8ac9f9b4e07205682898930c0a,0x3369c1b7a45d8ac9e82898930c0a3902b,0x31593f369c1b7a45c930c0a3902b4144c,0x235cc2987ceee959a443067588ca09520,0x214c3e7774acd8d7254808860ceb11941,0x1f3bba566c6b985306504a90110c19d62,0x1d2b3635cc2987cee7588ca0952022183,0x1b1ae614c3e7774ac860ceb119412a404,0x330a61f3bba566c6a90110c19d6232825,0x30f9ddd2b3635cc28a09520221833ac46,0x2ee959b1ae614c3e6b119412a40443067,0x2cd8d730a61f3bba4c19d623282548088,0x2b98530f9ddd2b3620221833ac46504a9,0x2987ceee959b1ae6012a40443067588ca,0x27774acd8d730a61e2328254808860ceb,0x2566c6b98530f9ddc33ac46504a90110c]
def action (k : K) (i : V) : V := Fin.ofNat 26 ((((maps[k.val]?).getD 0) >>> (5*i.val)) % 32)
def GoodMap (k : K) := (∀u v:V,action k u=action k v → u=v) ∧
    (∀v : V,left (action k v) ↔ left v) ∧ ∀u v:V,G (action k u) (action k v) ↔ G u v
instance (k : K) : Decidable (GoodMap k) := by unfold GoodMap; infer_instance
theorem aut0 : GoodMap 0 := by decide +kernel
theorem aut1 : GoodMap 1 := by decide +kernel
theorem aut2 : GoodMap 2 := by decide +kernel
theorem aut3 : GoodMap 3 := by decide +kernel
theorem aut4 : GoodMap 4 := by decide +kernel
theorem aut5 : GoodMap 5 := by decide +kernel
theorem aut6 : GoodMap 6 := by decide +kernel
theorem aut7 : GoodMap 7 := by decide +kernel
theorem aut8 : GoodMap 8 := by decide +kernel
theorem aut9 : GoodMap 9 := by decide +kernel
theorem aut10 : GoodMap 10 := by decide +kernel
theorem aut11 : GoodMap 11 := by decide +kernel
theorem aut12 : GoodMap 12 := by decide +kernel
theorem aut13 : GoodMap 13 := by decide +kernel
theorem aut14 : GoodMap 14 := by decide +kernel
theorem aut15 : GoodMap 15 := by decide +kernel
theorem aut16 : GoodMap 16 := by decide +kernel
theorem aut17 : GoodMap 17 := by decide +kernel
theorem aut18 : GoodMap 18 := by decide +kernel
theorem aut19 : GoodMap 19 := by decide +kernel
theorem aut20 : GoodMap 20 := by decide +kernel
theorem aut21 : GoodMap 21 := by decide +kernel
theorem aut22 : GoodMap 22 := by decide +kernel
theorem aut23 : GoodMap 23 := by decide +kernel
theorem aut24 : GoodMap 24 := by decide +kernel
theorem aut25 : GoodMap 25 := by decide +kernel
theorem aut26 : GoodMap 26 := by decide +kernel
theorem aut27 : GoodMap 27 := by decide +kernel
theorem aut28 : GoodMap 28 := by decide +kernel
theorem aut29 : GoodMap 29 := by decide +kernel
theorem aut30 : GoodMap 30 := by decide +kernel
theorem aut31 : GoodMap 31 := by decide +kernel
theorem aut32 : GoodMap 32 := by decide +kernel
theorem aut33 : GoodMap 33 := by decide +kernel
theorem aut34 : GoodMap 34 := by decide +kernel
theorem aut35 : GoodMap 35 := by decide +kernel
theorem aut36 : GoodMap 36 := by decide +kernel
theorem aut37 : GoodMap 37 := by decide +kernel
theorem aut38 : GoodMap 38 := by decide +kernel
theorem ok (k : K) : GoodMap k := by
  fin_cases k
  · exact aut0
  · exact aut1
  · exact aut2
  · exact aut3
  · exact aut4
  · exact aut5
  · exact aut6
  · exact aut7
  · exact aut8
  · exact aut9
  · exact aut10
  · exact aut11
  · exact aut12
  · exact aut13
  · exact aut14
  · exact aut15
  · exact aut16
  · exact aut17
  · exact aut18
  · exact aut19
  · exact aut20
  · exact aut21
  · exact aut22
  · exact aut23
  · exact aut24
  · exact aut25
  · exact aut26
  · exact aut27
  · exact aut28
  · exact aut29
  · exact aut30
  · exact aut31
  · exact aut32
  · exact aut33
  · exact aut34
  · exact aut35
  · exact aut36
  · exact aut37
  · exact aut38
theorem actionValid (k : K) : Valid (action k) := by
  obtain ⟨inj,side,adj⟩ := ok k
  exact ⟨fun x y h => inj x y h,side,adj⟩
noncomputable def perm (k : K) : V ≃ V :=
  Equiv.ofBijective (action k) ⟨(actionValid k).inj,Finite.injective_iff_surjective.mp (actionValid k).inj⟩
def zoneData : Array Nat := #[0x1fff,0x3df4,0x6cf0,0xa574,0xe470,0x160b0,0x1a134,0x268d0,0x2a154,0x32194,0x3a114,0x4a464,0x4e460,0x530a4,0x8e070,0xa6850,0xaa054,0xca064,0x10a530,0x10e430,0x11a130,0x143420,0x19e030,0x2ba014,0xefa004,0x3ffe000]
def switches : Array Nat := #[0x34,0x37,0x3a,0x3d,0x40,0x36,0x39,0x3c,0x3f,0x35,0x38,0x3b,0x3e,0x34,0x4e,0x75,0x68,0x67,0x82,0x8f,0x9a,0x8d,0x5b,0x74,0x80,0x5a,0x4e,0x4e,0x9c,0xc3,0x12a,0xf7,0x208,0x15b,0x1c5,0xd0,0x16c,0xf5,0xa8,0x75,0x9c,0x75,0xea,0x138,0x1ad,0x1c7,0x2d1,0x346,0x215,0x205,0x143,0xcf,0x9c,0x9c,0x9c,0x35a,0x38c,0x1d4,0x222,0x2e5,0x3a0,0x367,0x38e,0x191,0x366,0xc3,0xc3,0x35a,0xc3,0x37b,0x38b,0x35a,0x35a,0x37b,0x3df,0x38b,0x37b,0x38b,0xea,0x35a,0xea,0xea,0x186,0x380,0x1ee,0x31f,0x381,0x3a5,0x248,0x36d,0x37f,0x12a,0x12a,0x38c,0x37b,0x12a,0x365,0x262,0x3a2,0x1ec,0x398,0x371,0x1f6,0x1e0,0x138,0x38c,0x138,0x186,0x138,0x373,0x270,0x36d,0x381,0x2fe,0x3a5,0x27b,0x38a,0x175,0x37b,0x186,0x175,0x175,0x397,0x381,0x36d,0x19c,0x3a5,0x1aa,0x2ab,0x364,0x186,0x3b8,0x186,0x186,0x186,0x3be,0x381,0x36d,0x381,0x3a5,0x3a5,0x36d,0x3b9,0x1ad,0x1d4,0x1ad,0x380,0x373,0x1ad,0x2a4,0x38e,0x399,0x22f,0x27d,0x367,0x366,0x1d4,0x1d4,0x1d4,0x3b5,0x3bf,0x1d4,0x366,0x38e,0x3c0,0x367,0x38e,0x367,0x366,0x1fb,0x38b,0x380,0x1fb,0x397,0x1fb,0x23c,0x3a6,0x286,0x374,0x30b,0x395,0x25f,0x222,0x222,0x222,0x35a,0x38c,0x366,0x222,0x35a,0x3b8,0x3bf,0x3b5,0x38c,0x366,0x262,0x262,0x38c,0x3b8,0x262,0x3bf,0x262,0x3a2,0x3a2,0x398,0x3bd,0x38c,0x398,0x270,0x38c,0x270,0x381,0x270,0x373,0x270,0x3b8,0x381,0x373,0x3be,0x38c,0x3bf,0x2a4,0x366,0x2a4,0x380,0x373,0x2a4,0x2a4,0x3b5,0x3be,0x373,0x380,0x3bf,0x366,0x2d1,0x2e5,0x2d1,0x31f,0x36d,0x38e,0x35a,0x2d1,0x3a0,0x388,0x30a,0x2f8,0x37f,0x2e5,0x2e5,0x2e5,0x35a,0x3b8,0x38e,0x35a,0x2e5,0x3a0,0x3c0,0x38e,0x3a0,0x3b5,0x31f,0x35a,0x31f,0x31f,0x36d,0x3b5,0x35a,0x31f,0x3b8,0x3b9,0x37f,0x36d,0x37f,0x348,0x38e,0x38e,0x3a6,0x3df,0x348,0x3a6,0x348,0x386,0x386,0x38e,0x386,0x3a6,0x35a,0x35a,0x35a,0x35a,0x3b8,0x3b5,0x35a,0x35a,0x3b8,0x3df,0x3b5,0x3b8,0x3b5,0x381,0x3b8,0x381,0x381,0x381,0x3be,0x381,0x3b8,0x381,0x3be,0x3be,0x3b8,0x3df,0x3be,0x3df,0x3be,0x3be,0x3be,0x3be,0x3be,0x3df,0x3be,0x3be,0x3be,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df,0x3df]
def members (m : Nat) : Finset V := Finset.univ.filter fun x => m.testBit x.val
def zone (r : R) : Finset V := members ((zoneData[r.val]?).getD 0)
def line (x : L) : V := ⟨13+x.val,by omega⟩
def changeID (r : R) (x : L) := (switches[r.val*13+x.val]?).getD 0
def nextR (r : R) (x : L) : R := Fin.ofNat 26 (changeID r x / 39)
def label (r : R) (x : L) : K := Fin.ofNat 39 (changeID r x % 39)
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
theorem transitions (r : R) (x : L) (v : V) :
    v = line x ∨ (v ∈ zone r ∧ ¬ (left v ∧ G v (line x))) →
    action (label r x) v ∈ zone (nextR r x) := by
  intro h
  have ok : transOK r x v = true := by
    fin_cases r
    · exact tr0 x v
    · exact tr1 x v
    · exact tr2 x v
    · exact tr3 x v
    · exact tr4 x v
    · exact tr5 x v
    · exact tr6 x v
    · exact tr7 x v
    · exact tr8 x v
    · exact tr9 x v
    · exact tr10 x v
    · exact tr11 x v
    · exact tr12 x v
    · exact tr13 x v
    · exact tr14 x v
    · exact tr15 x v
    · exact tr16 x v
    · exact tr17 x v
    · exact tr18 x v
    · exact tr19 x v
    · exact tr20 x v
    · exact tr21 x v
    · exact tr22 x v
    · exact tr23 x v
    · exact tr24 x v
    · exact tr25 x v
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
    have low : 13≤(e w).val := by simpa [left] using right
    let l : L := ⟨(e w).val-13,by have := (e w).isLt; omega⟩
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

end Geometry17245



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

namespace Mixed17245
open Geometry17245 PEqualNP.Outside.L_meta_971_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def nbr (v : V) := Finset.univ.filter fun i => G v i

def Data (Z T U H : Finset V) (A : V → Finset V) : Prop :=
  H ⊆ T ∧ (∀i∈Z,i∉U → (∃a∈T,G i a) ∧ ∀ f∈H,∃a∈A f,G i a) ∧
  ∀ f∈H, (∀ a∈A f,∀ b∈A f,¬G a b) ∧ T.erase f ⊆ A f ∧ ∃ a∈A f,G f a
def every (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 26).all fun i => if i∈S then f i else true
def someIn (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 26).any fun i => decide (i∈S) && f i
theorem every_true (S : Finset V) (f : V → Bool) :
    every S f=true ↔ ∀i∈S,f i=true := by
  simp [every,List.all_eq_true]
  constructor
  · intro h i hi
    exact (h i).resolve_left (not_not_intro hi)
  · intro h i
    by_cases hi : i∈S
    · exact Or.inr (h i hi)
    · exact Or.inl hi
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
    refine ⟨h0.1,?_,h0.2.2⟩
    intro v hv
    obtain ⟨hne,ht⟩ := Finset.mem_erase.mp hv
    exact h0.2.1 v hne ht

inductive Good (k : ℕ) : Finset V → Prop where
 | done (Z T U H : Finset V) (A : V → Finset V) (data : Data Z T U H A)
     (price : U.card+2*T.card ≤ k+H.card) : Good k Z
 | pivot (Z T U H : Finset V) (A : V → Finset V) (z : V) (data : Data Z T U H A)
     (price : U.card+2*T.card+1 ≤ k+H.card+(nbr z ∩ T).card)
     (child : Good k (Z.erase z)) : Good k Z

theorem merges_mono {D : Dag} {T P : Finset V} (h : P ⊆ T) :
    merges 26 D (carrierT 26 D P) ⊆ merges 26 D (carrierT 26 D T) := by
  have lift {w : ℕ} (hw : w∈carrierT 26 D P) : w∈carrierT 26 D T := by
    obtain ⟨v,hv⟩ := k4_mem_carrier.mp hw
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hv
    exact k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨a,h b⟩⟩
  intro j hj
  obtain ⟨hr,out,a,b⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hr,lift out,lift a,lift b⟩

theorem charge {D : Dag} (hG : sem_Gr G) (live : StrictLive 26 D) (sem : sem_Comp 26 G D)
    {Z T U H : Finset V} {A : V → Finset V} (inc : ineligSet 26 D ⊆ Z) (dat : Data Z T U H A) :
    51+Bzero 26 D+H.card+(merges 26 D (carrierT 26 D T)).card ≤ D.length+U.card+2*T.card := by
  classical
  let I := ineligSet 26 D
  let E := eligSet 26 D
  have total : I.card+E.card=26 := by
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
  have plus := totalSurplus_split 26 D
  omega

theorem panelBound {k : ℕ} {Z : Finset V} {D : Dag} (hG : sem_Gr G) (live : StrictLive 26 D)
    (sem : sem_Comp 26 G D) (inc : ineligSet 26 D ⊆ Z) (valid : Good k Z) : 51+Bzero 26 D≤D.length+k := by
  classical
  induction valid with
  | done Z T U H A dat price =>
    have c := charge hG live sem inc dat
    omega
  | pivot Z T U H A z dat price child ih =>
    by_cases hz : z∈ineligSet 26 D
    · have c := charge hG live sem inc dat
      obtain ⟨pos,hp⟩ := k4_assigned hG live sem
      have prop : nbr z ∩ T ⊆ supp 26 D (src D (pos z)) := by
        intro a ha
        exact (hp.1 z hz).2.2.1 a (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
      have m := Merge9800.support_price live.1 (nbr z ∩ T) (src D (pos z)) prop
      have incl := Finset.card_le_card (merges_mono (D:=D) (Finset.inter_subset_right : nbr z ∩ T ⊆ T))
      omega
    · exact ih (fun i hi => Finset.mem_erase.mpr ⟨fun e => hz (e ▸ hi),inc hi⟩)
def zdata : Array Nat := #[0xc470,0x160b0,0x18134,0x248d0,0x28154,0x30194,0x38114,0x48464,0x4c460,0x510a4,0x8c070,0xa4850,0xa8054,0xc8064,0x102530,0x10c430,0x118130,0x143420,0xe470,0x1a134,0x268d0,0x2a154,0x32194,0x3a114,0x4a464,0x4e460,0x530a4,0x8e070,0xa6850,0xaa054,0xca064,0x10a530,0x10e430,0x11a130,0x19c030,0x2b8014,0xef8,0x25f4,0x6cf0,0xa574,0x19e030,0x2ba014,0xaf8004,0x1df0000,0xefa,0x2df4,0xef8004,0x1df4000,0xefe,0x3df4,0xefa004,0x1dfc000,0xffe,0x1ffc000,0x1ffe,0x3ffc000,0x1fff,0x3ffe000]
def tdata : Array Nat := #[0x1000,0x1,0x800,0x1000,0x1000,0x400,0x400,0x800,0x100,0x800,0x80,0x100,0x80,0x80,0x200,0x4,0x40,0x200,0x3,0x3,0x201,0x202,0x201,0x3,0x202,0x3,0x201,0x3,0x9,0xa,0xa,0x82,0x3,0x3,0x80,0x400,0x30000,0x180000,0x10001,0x200002,0x3,0x3,0x140,0x18,0xa000,0x50000,0x30,0x5,0x3100000,0x2c000,0xb,0x1880,0x2c0000,0x160,0x82c000,0x416,0x416000,0x20b]
def udata : Array Nat := #[0x470,0xb0,0x134,0x8d0,0x154,0x194,0x8114,0x464,0x8460,0x10a4,0x4070,0x20850,0x20054,0x40064,0x530,0x8430,0x8130,0x1420,0x470,0x134,0x8d0,0x154,0x194,0x20114,0x464,0x40460,0x10a4,0x80070,0x20850,0x20054,0x40064,0x530,0x100430,0x100130,0x14030,0x208014,0x98,0x2030,0xb0,0x414,0x180030,0xa0014,0x28004,0x130000,0x470,0x20a4,0x98004,0x8e0000,0x0,0x2050,0x60004,0x0,0x4,0x8000,0x0,0x0,0x0,0x0]
def hdata : Array Nat := #[0x1000,0x1,0x800,0x1000,0x1000,0x400,0x400,0x800,0x100,0x800,0x80,0x100,0x80,0x80,0x200,0x4,0x40,0x200,0x3,0x3,0x201,0x202,0x201,0x3,0x202,0x3,0x201,0x3,0x9,0xa,0xa,0x82,0x3,0x3,0x80,0x400,0x30000,0x180000,0x10001,0x200002,0x3,0x3,0x140,0x18,0xa000,0x50000,0x30,0x5,0x0,0x2c000,0xb,0x0,0x0,0x0,0x4000,0x2,0x0,0x0]
def adata : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x128119,0x213094,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x11403a,0x94232,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x128119,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3409a,0x0,0x0,0x0,0x0,0x401f4e,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa8055,0x0,0x93034,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x16000b,0x0,0x41420a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x328019,0x13401a,0x0,0x21c218,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3be8001,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def zset (i : Nat) := members ((zdata[i]?).getD 0)
def tset (i : Nat) := members ((tdata[i]?).getD 0)
def uset (i : Nat) := members ((udata[i]?).getD 0)
def hset (i : Nat) := members ((hdata[i]?).getD 0)
def aset (i : Nat) (f : V) := members ((adata[i*26+f.val]?).getD 0)
theorem nd0 : Data (zset 0) (tset 0) (uset 0) (hset 0) (aset 0) := verifies_sound (by decide +kernel)
theorem ng0 : Good 5 (zset 0) := .done _ _ _ _ _ nd0 (by decide +kernel)
theorem nd1 : Data (zset 1) (tset 1) (uset 1) (hset 1) (aset 1) := verifies_sound (by decide +kernel)
theorem ng1 : Good 5 (zset 1) := .done _ _ _ _ _ nd1 (by decide +kernel)
theorem nd2 : Data (zset 2) (tset 2) (uset 2) (hset 2) (aset 2) := verifies_sound (by decide +kernel)
theorem ng2 : Good 5 (zset 2) := .done _ _ _ _ _ nd2 (by decide +kernel)
theorem nd3 : Data (zset 3) (tset 3) (uset 3) (hset 3) (aset 3) := verifies_sound (by decide +kernel)
theorem ng3 : Good 5 (zset 3) := .done _ _ _ _ _ nd3 (by decide +kernel)
theorem nd4 : Data (zset 4) (tset 4) (uset 4) (hset 4) (aset 4) := verifies_sound (by decide +kernel)
theorem ng4 : Good 5 (zset 4) := .done _ _ _ _ _ nd4 (by decide +kernel)
theorem nd5 : Data (zset 5) (tset 5) (uset 5) (hset 5) (aset 5) := verifies_sound (by decide +kernel)
theorem ng5 : Good 5 (zset 5) := .done _ _ _ _ _ nd5 (by decide +kernel)
theorem nd6 : Data (zset 6) (tset 6) (uset 6) (hset 6) (aset 6) := verifies_sound (by decide +kernel)
theorem ng6 : Good 5 (zset 6) := .done _ _ _ _ _ nd6 (by decide +kernel)
theorem nd7 : Data (zset 7) (tset 7) (uset 7) (hset 7) (aset 7) := verifies_sound (by decide +kernel)
theorem ng7 : Good 5 (zset 7) := .done _ _ _ _ _ nd7 (by decide +kernel)
theorem nd8 : Data (zset 8) (tset 8) (uset 8) (hset 8) (aset 8) := verifies_sound (by decide +kernel)
theorem ng8 : Good 5 (zset 8) := .done _ _ _ _ _ nd8 (by decide +kernel)
theorem nd9 : Data (zset 9) (tset 9) (uset 9) (hset 9) (aset 9) := verifies_sound (by decide +kernel)
theorem ng9 : Good 5 (zset 9) := .done _ _ _ _ _ nd9 (by decide +kernel)
theorem nd10 : Data (zset 10) (tset 10) (uset 10) (hset 10) (aset 10) := verifies_sound (by decide +kernel)
theorem ng10 : Good 5 (zset 10) := .done _ _ _ _ _ nd10 (by decide +kernel)
theorem nd11 : Data (zset 11) (tset 11) (uset 11) (hset 11) (aset 11) := verifies_sound (by decide +kernel)
theorem ng11 : Good 5 (zset 11) := .done _ _ _ _ _ nd11 (by decide +kernel)
theorem nd12 : Data (zset 12) (tset 12) (uset 12) (hset 12) (aset 12) := verifies_sound (by decide +kernel)
theorem ng12 : Good 5 (zset 12) := .done _ _ _ _ _ nd12 (by decide +kernel)
theorem nd13 : Data (zset 13) (tset 13) (uset 13) (hset 13) (aset 13) := verifies_sound (by decide +kernel)
theorem ng13 : Good 5 (zset 13) := .done _ _ _ _ _ nd13 (by decide +kernel)
theorem nd14 : Data (zset 14) (tset 14) (uset 14) (hset 14) (aset 14) := verifies_sound (by decide +kernel)
theorem ng14 : Good 5 (zset 14) := .done _ _ _ _ _ nd14 (by decide +kernel)
theorem nd15 : Data (zset 15) (tset 15) (uset 15) (hset 15) (aset 15) := verifies_sound (by decide +kernel)
theorem ng15 : Good 5 (zset 15) := .done _ _ _ _ _ nd15 (by decide +kernel)
theorem nd16 : Data (zset 16) (tset 16) (uset 16) (hset 16) (aset 16) := verifies_sound (by decide +kernel)
theorem ng16 : Good 5 (zset 16) := .done _ _ _ _ _ nd16 (by decide +kernel)
theorem nd17 : Data (zset 17) (tset 17) (uset 17) (hset 17) (aset 17) := verifies_sound (by decide +kernel)
theorem ng17 : Good 5 (zset 17) := .done _ _ _ _ _ nd17 (by decide +kernel)
theorem nd18 : Data (zset 18) (tset 18) (uset 18) (hset 18) (aset 18) := verifies_sound (by decide +kernel)
theorem ng18 : Good 5 (zset 18) := by
  have eq : (zset 18).erase 13=zset 0 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd18 (by decide +kernel) (eq.symm ▸ ng0)
theorem nd19 : Data (zset 19) (tset 19) (uset 19) (hset 19) (aset 19) := verifies_sound (by decide +kernel)
theorem ng19 : Good 5 (zset 19) := by
  have eq : (zset 19).erase 13=zset 2 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd19 (by decide +kernel) (eq.symm ▸ ng2)
theorem nd20 : Data (zset 20) (tset 20) (uset 20) (hset 20) (aset 20) := verifies_sound (by decide +kernel)
theorem ng20 : Good 5 (zset 20) := by
  have eq : (zset 20).erase 13=zset 3 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd20 (by decide +kernel) (eq.symm ▸ ng3)
theorem nd21 : Data (zset 21) (tset 21) (uset 21) (hset 21) (aset 21) := verifies_sound (by decide +kernel)
theorem ng21 : Good 5 (zset 21) := by
  have eq : (zset 21).erase 13=zset 4 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd21 (by decide +kernel) (eq.symm ▸ ng4)
theorem nd22 : Data (zset 22) (tset 22) (uset 22) (hset 22) (aset 22) := verifies_sound (by decide +kernel)
theorem ng22 : Good 5 (zset 22) := by
  have eq : (zset 22).erase 13=zset 5 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd22 (by decide +kernel) (eq.symm ▸ ng5)
theorem nd23 : Data (zset 23) (tset 23) (uset 23) (hset 23) (aset 23) := verifies_sound (by decide +kernel)
theorem ng23 : Good 5 (zset 23) := by
  have eq : (zset 23).erase 13=zset 6 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd23 (by decide +kernel) (eq.symm ▸ ng6)
theorem nd24 : Data (zset 24) (tset 24) (uset 24) (hset 24) (aset 24) := verifies_sound (by decide +kernel)
theorem ng24 : Good 5 (zset 24) := by
  have eq : (zset 24).erase 13=zset 7 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd24 (by decide +kernel) (eq.symm ▸ ng7)
theorem nd25 : Data (zset 25) (tset 25) (uset 25) (hset 25) (aset 25) := verifies_sound (by decide +kernel)
theorem ng25 : Good 5 (zset 25) := by
  have eq : (zset 25).erase 13=zset 8 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd25 (by decide +kernel) (eq.symm ▸ ng8)
theorem nd26 : Data (zset 26) (tset 26) (uset 26) (hset 26) (aset 26) := verifies_sound (by decide +kernel)
theorem ng26 : Good 5 (zset 26) := by
  have eq : (zset 26).erase 13=zset 9 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd26 (by decide +kernel) (eq.symm ▸ ng9)
theorem nd27 : Data (zset 27) (tset 27) (uset 27) (hset 27) (aset 27) := verifies_sound (by decide +kernel)
theorem ng27 : Good 5 (zset 27) := by
  have eq : (zset 27).erase 13=zset 10 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd27 (by decide +kernel) (eq.symm ▸ ng10)
theorem nd28 : Data (zset 28) (tset 28) (uset 28) (hset 28) (aset 28) := verifies_sound (by decide +kernel)
theorem ng28 : Good 5 (zset 28) := by
  have eq : (zset 28).erase 13=zset 11 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd28 (by decide +kernel) (eq.symm ▸ ng11)
theorem nd29 : Data (zset 29) (tset 29) (uset 29) (hset 29) (aset 29) := verifies_sound (by decide +kernel)
theorem ng29 : Good 5 (zset 29) := by
  have eq : (zset 29).erase 13=zset 12 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd29 (by decide +kernel) (eq.symm ▸ ng12)
theorem nd30 : Data (zset 30) (tset 30) (uset 30) (hset 30) (aset 30) := verifies_sound (by decide +kernel)
theorem ng30 : Good 5 (zset 30) := by
  have eq : (zset 30).erase 13=zset 13 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd30 (by decide +kernel) (eq.symm ▸ ng13)
theorem nd31 : Data (zset 31) (tset 31) (uset 31) (hset 31) (aset 31) := verifies_sound (by decide +kernel)
theorem ng31 : Good 5 (zset 31) := by
  have eq : (zset 31).erase 15=zset 14 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd31 (by decide +kernel) (eq.symm ▸ ng14)
theorem nd32 : Data (zset 32) (tset 32) (uset 32) (hset 32) (aset 32) := verifies_sound (by decide +kernel)
theorem ng32 : Good 5 (zset 32) := by
  have eq : (zset 32).erase 13=zset 15 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd32 (by decide +kernel) (eq.symm ▸ ng15)
theorem nd33 : Data (zset 33) (tset 33) (uset 33) (hset 33) (aset 33) := verifies_sound (by decide +kernel)
theorem ng33 : Good 5 (zset 33) := by
  have eq : (zset 33).erase 13=zset 16 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd33 (by decide +kernel) (eq.symm ▸ ng16)
theorem nd34 : Data (zset 34) (tset 34) (uset 34) (hset 34) (aset 34) := verifies_sound (by decide +kernel)
theorem ng34 : Good 5 (zset 34) := .done _ _ _ _ _ nd34 (by decide +kernel)
theorem nd35 : Data (zset 35) (tset 35) (uset 35) (hset 35) (aset 35) := verifies_sound (by decide +kernel)
theorem ng35 : Good 5 (zset 35) := .done _ _ _ _ _ nd35 (by decide +kernel)
theorem nd36 : Data (zset 36) (tset 36) (uset 36) (hset 36) (aset 36) := verifies_sound (by decide +kernel)
theorem ng36 : Good 5 (zset 36) := .done _ _ _ _ _ nd36 (by decide +kernel)
theorem nd37 : Data (zset 37) (tset 37) (uset 37) (hset 37) (aset 37) := verifies_sound (by decide +kernel)
theorem ng37 : Good 5 (zset 37) := .done _ _ _ _ _ nd37 (by decide +kernel)
theorem nd38 : Data (zset 38) (tset 38) (uset 38) (hset 38) (aset 38) := verifies_sound (by decide +kernel)
theorem ng38 : Good 5 (zset 38) := .done _ _ _ _ _ nd38 (by decide +kernel)
theorem nd39 : Data (zset 39) (tset 39) (uset 39) (hset 39) (aset 39) := verifies_sound (by decide +kernel)
theorem ng39 : Good 5 (zset 39) := .done _ _ _ _ _ nd39 (by decide +kernel)
theorem nd40 : Data (zset 40) (tset 40) (uset 40) (hset 40) (aset 40) := verifies_sound (by decide +kernel)
theorem ng40 : Good 5 (zset 40) := by
  have eq : (zset 40).erase 13=zset 34 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd40 (by decide +kernel) (eq.symm ▸ ng34)
theorem nd41 : Data (zset 41) (tset 41) (uset 41) (hset 41) (aset 41) := verifies_sound (by decide +kernel)
theorem ng41 : Good 5 (zset 41) := by
  have eq : (zset 41).erase 13=zset 35 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd41 (by decide +kernel) (eq.symm ▸ ng35)
theorem nd42 : Data (zset 42) (tset 42) (uset 42) (hset 42) (aset 42) := verifies_sound (by decide +kernel)
theorem ng42 : Good 5 (zset 42) := .done _ _ _ _ _ nd42 (by decide +kernel)
theorem nd43 : Data (zset 43) (tset 43) (uset 43) (hset 43) (aset 43) := verifies_sound (by decide +kernel)
theorem ng43 : Good 5 (zset 43) := .done _ _ _ _ _ nd43 (by decide +kernel)
theorem nd44 : Data (zset 44) (tset 44) (uset 44) (hset 44) (aset 44) := verifies_sound (by decide +kernel)
theorem ng44 : Good 5 (zset 44) := by
  have eq : (zset 44).erase 1=zset 36 := by decide +kernel
  exact .pivot _ _ _ _ _ 1 nd44 (by decide +kernel) (eq.symm ▸ ng36)
theorem nd45 : Data (zset 45) (tset 45) (uset 45) (hset 45) (aset 45) := verifies_sound (by decide +kernel)
theorem ng45 : Good 5 (zset 45) := by
  have eq : (zset 45).erase 11=zset 37 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 nd45 (by decide +kernel) (eq.symm ▸ ng37)
theorem nd46 : Data (zset 46) (tset 46) (uset 46) (hset 46) (aset 46) := verifies_sound (by decide +kernel)
theorem ng46 : Good 5 (zset 46) := by
  have eq : (zset 46).erase 22=zset 42 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 nd46 (by decide +kernel) (eq.symm ▸ ng42)
theorem nd47 : Data (zset 47) (tset 47) (uset 47) (hset 47) (aset 47) := verifies_sound (by decide +kernel)
theorem ng47 : Good 5 (zset 47) := by
  have eq : (zset 47).erase 14=zset 43 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 nd47 (by decide +kernel) (eq.symm ▸ ng43)
theorem nd48 : Data (zset 48) (tset 48) (uset 48) (hset 48) (aset 48) := verifies_sound (by decide +kernel)
theorem ng48 : Good 5 (zset 48) := by
  have eq : (zset 48).erase 2=zset 44 := by decide +kernel
  exact .pivot _ _ _ _ _ 2 nd48 (by decide +kernel) (eq.symm ▸ ng44)
theorem nd49 : Data (zset 49) (tset 49) (uset 49) (hset 49) (aset 49) := verifies_sound (by decide +kernel)
theorem ng49 : Good 5 (zset 49) := by
  have eq : (zset 49).erase 12=zset 45 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd49 (by decide +kernel) (eq.symm ▸ ng45)
theorem nd50 : Data (zset 50) (tset 50) (uset 50) (hset 50) (aset 50) := verifies_sound (by decide +kernel)
theorem ng50 : Good 5 (zset 50) := by
  have eq : (zset 50).erase 13=zset 46 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd50 (by decide +kernel) (eq.symm ▸ ng46)
theorem nd51 : Data (zset 51) (tset 51) (uset 51) (hset 51) (aset 51) := verifies_sound (by decide +kernel)
theorem ng51 : Good 5 (zset 51) := by
  have eq : (zset 51).erase 15=zset 47 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 nd51 (by decide +kernel) (eq.symm ▸ ng47)
theorem nd52 : Data (zset 52) (tset 52) (uset 52) (hset 52) (aset 52) := verifies_sound (by decide +kernel)
theorem ng52 : Good 5 (zset 52) := by
  have eq : (zset 52).erase 8=zset 48 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 nd52 (by decide +kernel) (eq.symm ▸ ng48)
theorem nd53 : Data (zset 53) (tset 53) (uset 53) (hset 53) (aset 53) := verifies_sound (by decide +kernel)
theorem ng53 : Good 5 (zset 53) := by
  have eq : (zset 53).erase 21=zset 51 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 nd53 (by decide +kernel) (eq.symm ▸ ng51)
theorem nd54 : Data (zset 54) (tset 54) (uset 54) (hset 54) (aset 54) := verifies_sound (by decide +kernel)
theorem ng54 : Good 5 (zset 54) := by
  have eq : (zset 54).erase 12=zset 52 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 nd54 (by decide +kernel) (eq.symm ▸ ng52)
theorem nd55 : Data (zset 55) (tset 55) (uset 55) (hset 55) (aset 55) := verifies_sound (by decide +kernel)
theorem ng55 : Good 5 (zset 55) := by
  have eq : (zset 55).erase 25=zset 53 := by decide +kernel
  exact .pivot _ _ _ _ _ 25 nd55 (by decide +kernel) (eq.symm ▸ ng53)
theorem nd56 : Data (zset 56) (tset 56) (uset 56) (hset 56) (aset 56) := verifies_sound (by decide +kernel)
theorem ng56 : Good 5 (zset 56) := by
  have eq : (zset 56).erase 0=zset 54 := by decide +kernel
  exact .pivot _ _ _ _ _ 0 nd56 (by decide +kernel) (eq.symm ▸ ng54)
theorem nd57 : Data (zset 57) (tset 57) (uset 57) (hset 57) (aset 57) := verifies_sound (by decide +kernel)
theorem ng57 : Good 5 (zset 57) := by
  have eq : (zset 57).erase 13=zset 55 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 nd57 (by decide +kernel) (eq.symm ▸ ng55)
theorem allPanels (r : R) : Good 5 (zone r) := by
  fin_cases r
  · have e : zone 0=zset 56 := by decide +kernel
    exact e.symm ▸ ng56
  · have e : zone 1=zset 49 := by decide +kernel
    exact e.symm ▸ ng49
  · have e : zone 2=zset 38 := by decide +kernel
    exact e.symm ▸ ng38
  · have e : zone 3=zset 39 := by decide +kernel
    exact e.symm ▸ ng39
  · have e : zone 4=zset 18 := by decide +kernel
    exact e.symm ▸ ng18
  · have e : zone 5=zset 1 := by decide +kernel
    exact e.symm ▸ ng1
  · have e : zone 6=zset 19 := by decide +kernel
    exact e.symm ▸ ng19
  · have e : zone 7=zset 20 := by decide +kernel
    exact e.symm ▸ ng20
  · have e : zone 8=zset 21 := by decide +kernel
    exact e.symm ▸ ng21
  · have e : zone 9=zset 22 := by decide +kernel
    exact e.symm ▸ ng22
  · have e : zone 10=zset 23 := by decide +kernel
    exact e.symm ▸ ng23
  · have e : zone 11=zset 24 := by decide +kernel
    exact e.symm ▸ ng24
  · have e : zone 12=zset 25 := by decide +kernel
    exact e.symm ▸ ng25
  · have e : zone 13=zset 26 := by decide +kernel
    exact e.symm ▸ ng26
  · have e : zone 14=zset 27 := by decide +kernel
    exact e.symm ▸ ng27
  · have e : zone 15=zset 28 := by decide +kernel
    exact e.symm ▸ ng28
  · have e : zone 16=zset 29 := by decide +kernel
    exact e.symm ▸ ng29
  · have e : zone 17=zset 30 := by decide +kernel
    exact e.symm ▸ ng30
  · have e : zone 18=zset 31 := by decide +kernel
    exact e.symm ▸ ng31
  · have e : zone 19=zset 32 := by decide +kernel
    exact e.symm ▸ ng32
  · have e : zone 20=zset 33 := by decide +kernel
    exact e.symm ▸ ng33
  · have e : zone 21=zset 17 := by decide +kernel
    exact e.symm ▸ ng17
  · have e : zone 22=zset 40 := by decide +kernel
    exact e.symm ▸ ng40
  · have e : zone 23=zset 41 := by decide +kernel
    exact e.symm ▸ ng41
  · have e : zone 24=zset 50 := by decide +kernel
    exact e.symm ▸ ng50
  · have e : zone 25=zset 57 := by decide +kernel
    exact e.symm ▸ ng57
theorem core (hG : sem_Gr G) {D : Dag} (h : StrictLive 26 D) (hc : sem_Comp 26 G D)
    (ind : ∀ i∈ineligSet 26 D, ∀ j∈ineligSet 26 D, ¬G i j) : 46+Bzero 26 D≤D.length := by
  classical
  obtain ⟨r,e,valid,sub⟩ := envelope ind
  have hrel : sem_Comp 26 G (relabel e D) := by
    intro x
    rw [relabel_out e h.1 h.2.2 x, hc]
    unfold sem_Edge
    constructor
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e u,e v,(valid.adj u v).mpr huv,hu,hv⟩
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e.symm u,e.symm v,(valid.adj _ _).mp (by simpa using huv),
        by simpa using hu,by simpa using hv⟩
  have inc : ineligSet 26 (relabel e D) ⊆ zone r := by
    rw [relabel_ineligSet e h.1]
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact sub i hi
  have result := panelBound hG (relabel_strictLive e h) hrel inc (allPanels r)
  rw [relabel_length,relabel_Bzero e h.1] at result
  omega
theorem lowerSem (hG : sem_Gr G)
    (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
      C.eval (List.ofFn x)=true ↔ sem_Edge G x) : 46≤C.size := by
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
  obtain ⟨D,ld,lim,simulation⟩ := normalize_strictLive (n:=26) C hm
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
  have sem : sem_Comp 26 G D := fun x => by rw [simulation x]; exact correct x
  have ind : ∀i∈ineligSet 26 D,∀j∈ineligSet 26 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover hG ld sem ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have enriched := core hG ld sem ind
  omega

theorem regular : sem_Gr G := by unfold sem_Gr; decide +kernel
end Mixed17245


namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered

namespace Promise17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 13
abbrev W := Fin 26
def Inc (p l : V) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def vec (X Y : Finset V) (i : W) : Bool :=
  if i.val<13 then decide (Fin.ofNat 13 i.val∈X) else decide (Fin.ofNat 13 i.val∈Y)
def off (X : Finset V) := Finset.univ.filter fun l => ∀p∈X,¬Inc p l
def read (C : Circuit) (o : List Nat) (x : W → Bool) :=
  GateOp.or.eval (o.map fun k => (C.wires (List.ofFn x)).getD k false)
def Tests (C : Circuit) (o : List Nat) : Prop :=
  (∀p l : V,Inc p l → read C o (vec {p} {l})=true) ∧
   ∀S : Finset V,S.card≤3 → read C o (vec S (off S))=false ∧ read C o (vec (off S) S)=false
def Hit (X Y : Finset V) := ∃p∈X,∃l∈Y,Inc p l
theorem four : ∀ S : Finset V, S.card=4 → (off S).card≤3 := by
  set_option maxRecDepth 20000 in
    set_option maxHeartbeats 0 in
      decide +kernel
theorem small (X Y : Finset V) (hn : ¬Hit X Y) : X.card≤3 ∨ Y.card≤3 := by
  by_cases hx : X.card≤3
  · exact Or.inl hx
  right
  obtain ⟨S,sub,hs⟩ := Finset.exists_subset_card_eq (show 4≤X.card by omega)
  have incl : Y ⊆ off S := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp h => hn ⟨p,sub hp,l,hl,h⟩⟩
  exact (Finset.card_le_card incl).trans (four S hs)

theorem read_mono (C : Circuit) (hm : Monotone2 C) (o : List Nat) {x y : W → Bool} (hxy : x≤y) :
    read C o x=true → read C o y=true := by
  simp only [read,GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id]
  rintro ⟨k,hk,h⟩
  let D : Circuit := ⟨C.gates,k⟩
  have mD : Monotone2 D := hm
  exact ⟨k,hk,PlaneOrdered.cmono D mD 26 x y hxy h⟩
theorem inclVec {A B X Y : Finset V} (ha : A⊆X) (hb : B⊆Y) : vec A B ≤ vec X Y := by
  intro i
  apply Bool.le_iff_imp.mpr
  unfold vec
  split <;> simp only [decide_eq_true_eq]
  · exact fun h => ha h
  · exact fun h => hb h
theorem decodes {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o)
    (X Y : Finset V) : read C o (vec X Y)=true ↔ Hit X Y := by
  constructor
  · intro f
    by_contra no
    rcases small X Y no with px|ly
    · have incl : Y ⊆ off X := fun l hl => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun p hp h => no ⟨p,hp,l,hl,h⟩⟩
      have lit := read_mono C hm o (inclVec (A:=X) subset_rfl incl) f
      rw [(ht.2 X px).1] at lit
      contradiction
    · have incl : X ⊆ off Y := by
        intro p hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl hi => no ⟨p,hp,l,hl,?_⟩⟩
        simpa only [Inc,Nat.add_comm] using hi
      have lit := read_mono C hm o (inclVec (B:=Y) incl subset_rfl) f
      rw [(ht.2 Y ly).2] at lit
      contradiction
  · rintro ⟨p,hp,l,hl,edge⟩
    exact read_mono C hm o (inclVec (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)) (ht.1 p l edge)
def pts (x : W → Bool) := Finset.univ.filter fun p : V => x (Fin.castAdd 13 p)=true
def lns (x : W → Bool) := Finset.univ.filter fun l : V => x (Fin.natAdd 13 l)=true
theorem rebuild (x : W → Bool) : vec (pts x) (lns x)=x := by
  funext i
  unfold vec
  split <;> rename_i hi
  · have eq : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change i.val%13=i.val; omega)
    simp [pts]
    exact congrArg x eq
  · have eq : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change 13+i.val%13=i.val; have := i.isLt; omega)
    simp only [lns,Finset.mem_filter,Finset.mem_univ,true_and,eq]
    cases x i <;> rfl
theorem exact_eval {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o) (x : W → Bool) :
    read C o x=true ↔ ∃p l : V,Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  have d := decodes hm ht (pts x) (lns x)
  rw [rebuild] at d
  rw [d]
  constructor
  · rintro ⟨p,hp,l,hl,ed⟩
    exact ⟨p,l,ed,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
  · rintro ⟨p,l,ed,hp,hl⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,ed⟩

def finish (C : Circuit) (o : List Nat) : Circuit :=
  ⟨C.gates++[⟨GateOp.or,o⟩],26+C.size⟩
theorem finish_size (C : Circuit) (o : List Nat) : (finish C o).size=C.size+1 := by
  simp [finish,Circuit.size]
theorem finish_mono {C : Circuit} (hm : Monotone2 C) {o : List Nat} (small : o.length≤2) :
    Monotone2 (finish C o) := by
  intro g hg
  change g∈C.gates++[⟨GateOp.or,o⟩] at hg
  rcases List.mem_append.mp hg with old|new
  · exact hm g old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨Or.inr rfl,small⟩
theorem finish_eval (C : Circuit) (o : List Nat) (x : W → Bool) :
    (finish C o).eval (List.ofFn x)=read C o x := by
  let u := PlaneOrdered.wf C.gates (List.ofFn x)
  have sz : u.length=26+C.size := by simp [u,PlaneOrdered.wf_len,Circuit.size]
  change (PlaneOrdered.wf (C.gates++[⟨GateOp.or,o⟩]) (List.ofFn x)).getD (26+C.size) false=_
  unfold PlaneOrdered.wf
  rw [List.foldl_append]
  change (u++[GateOp.or.eval (o.map fun k => u.getD k false)]).getD (26+C.size) false=_
  rw [←sz,PlaneOrdered.getD_snoc_eq]
  rfl
end Promise17245

namespace Physical17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_971_aux
open Promise17245
abbrev G := Geometry17245.G
theorem flags : ∀p l : Fin 13, Inc p l → G (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by decide +kernel
theorem endpoints : ∀a b : W,G a b → ∃p l : V,Inc p l ∧
    ((a=Fin.castAdd 13 p ∧ b=Fin.natAdd 13 l) ∨
     (b=Fin.castAdd 13 p ∧ a=Fin.natAdd 13 l)) := by decide +kernel
theorem completed {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o) (x : W → Bool) :
    (finish C o).eval (List.ofFn x)=true ↔ sem_Edge G x := by
  rw [finish_eval,exact_eval hm ht]
  constructor
  · rintro ⟨p,l,ed,hp,hl⟩
    exact ⟨_,_,flags p l ed,hp,hl⟩
  · rintro ⟨a,b,ed,ha,hb⟩
    obtain ⟨p,l,flag,orr⟩ := endpoints a b ed
    rcases orr with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact ⟨p,l,flag,ha,hb⟩
    · exact ⟨p,l,flag,hb,ha⟩
theorem lower {C : Circuit} {o : List Nat} (hm : Monotone2 C) (bound : o.length≤2) (ht : Tests C o) :
   45≤C.size := by
  have q := Mixed17245.lowerSem Mixed17245.regular (finish C o) (finish_mono hm bound) (completed hm ht)
  rw [finish_size] at q
  omega
end Physical17245

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
noncomputable def slice (G : Fin n → Fin n → Prop) (Bs : Finset (Fin n)) (i : Fin n) : Finset (Fin n) := by
  classical exact Bs.filter fun a => G i a
theorem mem_slice {Bs : Finset (Fin n)} {i a : Fin n} : a∈slice G Bs i ↔ a∈Bs ∧ G i a := by classical simp [slice]

theorem cold_at (hS : Strict n D) (i : Fin n) (w : ℕ) (hch : sem_Chain n D i.val w)
    (Bs : Finset (Fin n))
    (h0 : ∀ S : Finset (Fin n), S ⊆ Bs → (∀ a ∈ S, ¬ G i a) →
      val D (sem_ins i (sem_ind S)) w = false)
    (h1 : ∀ a ∈ Bs, G i a →
      val D (sem_ins i (sem_ind {a})) w = true ∧ val D (sem_ind {a}) w = false) :
    ∃ j s, j < D.length ∧ tag D j = true ∧ n + j ≤ w ∧
      sem_Chain n D i.val (src D (j, !s)) ∧
      val D (sem_ind (Bs \ (slice G Bs i))) (src D (j,s)) = false ∧
      ∀ a ∈ Bs, (a ∈ supp n D (src D (j, s)) ↔ G i a) := by
  classical
  obtain ⟨j, s, hj, ht, hle, hc, hv, hsupp⟩ := cold_factor hS i w hch Bs (Bs.filter (fun a => G i a))
    (Finset.filter_subset _ _)
    (h0 _ Finset.sdiff_subset (fun a ha hia => by
      rw [Finset.mem_sdiff, Finset.mem_filter] at ha
      exact ha.2 ⟨ha.1, hia⟩))
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).1)
    (fun a ha => (h1 a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2).2)
  refine ⟨j, s, hj, ht, hle, hc, by simpa only [slice] using hv, fun a ha => ?_⟩
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
      val D (sem_ind (Bs \ (slice G Bs i))) (src D (k,s)) = false ∧
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
namespace Exposure17245
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

open Geometry17245
def lines : Finset V := Finset.univ.filter fun (i : V) => (13 : Nat) ≤ i.val
def neighborhood (l : V) : Finset V := Finset.univ.filter fun v => G l v
def pts : Finset V := Finset.univ.filter fun (i : V) => i.val < (13 : Nat)
def outer (l : V) : Test 26 := sem_ind (pts \ neighborhood l)
def pointsOn : Test 26 := fun i => decide (i.val<13)
def withLine (l : V) : Test 26 := fun i => pointsOn i || decide (i=l)
def bankFees (D : Dag) (l : V) := credits D single (outer l) (neighborhood l)
def outputFees (D : Dag) := credits D withLine pointsOn lines
def conjunctions (D : Dag) := (Finset.range D.length).filter fun j => tag D j=true

def Bank (D : Dag) : Prop :=
  ∀ l∈lines, ∃ w, val D (outer l) w=false ∧ ∀v∈neighborhood l, sees D single v w

theorem graphData : lines.card = 13 ∧
   (∀l∈lines, (neighborhood l).card=4) ∧
   (∀l∈lines,∀i∈neighborhood l,pointsOn i=true) ∧
   (∀ l∈lines, ∀ m∈lines, l≠m → ∀a∈neighborhood l,∀b∈neighborhood l,
     a∈neighborhood m → b∈neighborhood m → a=b) ∧
   (∀ u v : V,G u v → ¬(pointsOn u=true ∧ pointsOn v=true)) ∧
   (∀l∈lines,∃p, G p l ∧ pointsOn p=true) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · have isSmall : ∀l m : V,l≠m → (neighborhood l ∩ neighborhood m).card≤1 := by decide +kernel
    intro l _ m _ ne a ha b hb ham hbm
    exact Finset.card_le_one.mp (isSmall l m ne) a (Finset.mem_inter.mpr ⟨ha,ham⟩) b
      (Finset.mem_inter.mpr ⟨hb,hbm⟩)
  · decide +kernel
  · decide +kernel

theorem credit_rows {row : V → Test 26} {off : Test 26} {P : Finset V}
    {D : Dag} (hs : Strict 26 D) {j : ℕ} (hj : j∈credits D row off P) :
    j<D.length ∧ tag D j=false ∧ val D off (26+j)=false ∧
      ∃a∈P, ∃b∈P, a≠b ∧ sees D row a (26+j) ∧ sees D row b (26+j) := by
  obtain ⟨bound,ht,hc,a,ha,sa,b,hb,ab,sb⟩ := Finset.mem_filter.mp hj
  have lim := Finset.mem_range.mp bound
  refine ⟨lim,ht,hc,a,ha,b,hb,ab,?_,?_⟩
  · unfold sees at *
    rw [val_gate hs _ j lim,ht,gop_false,sa]
    rfl
  · unfold sees at *
    rw [val_gate hs _ j lim,ht,gop_false,sb]
    simp

theorem supported {D : Dag} (hs : Strict 26 D) {l v : V} {w : ℕ}
    (hv : v∈pts) (cold : val D (outer l) w=false) (seen : sees D single v w) : v∈neighborhood l := by
  by_contra no
  have hot : outer l v=true := by simp [outer,sem_ind,hv,no]
  have lit := val_mono hs (single v) (outer l) (sem_single_le hot) w seen
  rw [cold] at lit
  contradiction

theorem chainData : pts.card=13 ∧ (∀ l∈lines, neighborhood l ⊆ pts) ∧
    (∀p∈pts,∃l∈lines,G p l) ∧ (∀l∈lines,∃p∈pts,G l p) ∧
    (∀ l∈lines, ¬ sem_Edge G (sem_ins l (outer l)) ∧ ∀p∈neighborhood l,
      sem_Edge G (sem_ins l (sem_ind {p})) ∧ ¬sem_Edge G (sem_ind {p})) := by
  unfold sem_Edge
  decide +kernel

theorem line_chain {D : Dag} (hg : sem_Gr G) (h : StrictLive 26 D) (hc : sem_Comp 26 G D)
    {l : V} (hl : l∈lines) (chain : sem_Chain 26 D l.val (outW 26 D)) :
    ∃ w, val D (outer l) w=false ∧ ∀v∈neighborhood l,sees D single v w := by
  obtain ⟨-,incl,_,_,tests⟩ := chainData
  obtain ⟨neg,pos⟩ := tests l hl
  have off : val D (sem_ins l (outer l)) (outW 26 D)=false := by
    cases v : val D (sem_ins l (outer l)) (outW 26 D) with
    | false => rfl
    | true => exact False.elim (neg ((hc _).mp v))
  obtain ⟨j,s,-,-,-,-,cold,mask⟩ := cold_factor h.1 l _ chain
    pts (neighborhood l) (incl l hl) off (fun a ha => (hc _).mpr (pos a ha).1) (by
      intro a ha
      cases v : val D (sem_ind {a}) (outW 26 D) with
      | false => rfl
      | true => exact False.elim ((pos a ha).2 ((hc _).mp v)))
  refine ⟨_,cold,?_⟩
  intro p hp
  rw [←mask] at hp
  exact mem_supp.mp (Finset.mem_inter.mp hp).1


def Ready (D : Dag) (l : V) : Prop := ∃ w, val D (outer l) w=false ∧
    ∀v∈neighborhood l,sees D single v w
noncomputable def absent (J : Finset V) (D : Dag) : Finset V := by classical exact J.filter (fun l => ¬Ready D l)
theorem absent_mem {D : Dag} {J : Finset V} {l : V} : l∈absent J D ↔ l∈J ∧ ¬Ready D l := by classical simp [absent]

theorem incomparable : ∀ l∈lines,∀m∈lines,l≠m → ∃ a∈pts,G m a ∧ ¬G l a := by decide +kernel
theorem independent : ∀ a∈pts,∀ b∈pts,¬G a b := by decide +kernel

theorem loss {D : Dag} (hg : sem_Gr G) (h : StrictLive 26 D) (hc : sem_Comp 26 G D)
    {J : Finset V} (side : J ⊆ lines) (mode : J ⊆ ineligSet 26 D) : (absent J D).card ≤ Bzero 26 D := by
  classical
  have hub : ∀ l∈absent J D, ∃ w, sem_Chain 26 D l.val w ∧ 2≤fanout D w ∧ supp 26 D w=∅ := by
    intro l hl
    obtain ⟨inside,miss⟩ := absent_mem.mp hl
    rcases sem_inelig_reach hg h hc (mode inside) with chain|q
    · exact (miss (line_chain hg h hc (side inside) chain)).elim
    · exact q
  choose! w hw using hub
  have inj : Set.InjOn w (↑(absent J D)) := by
    intro l hl m hm eqw
    by_contra ne
    obtain ⟨inside,miss⟩ := absent_mem.mp hl
    obtain ⟨ch,-⟩ := hw l hl
    obtain ⟨cm,-⟩ := hw m hm
    rw [←eqw] at cm
    obtain ⟨j,t,_,_,_,_,cold,hit⟩ := cold_shared hg h.1 hc pts independent ch
      (sem_chain_dom h.1 cm) (incomparable l (side inside) m (side (absent_mem.mp hm).1) ne)
    have eq : slice G pts l = neighborhood l := by
      ext a
      rw [mem_slice]
      constructor
      · intro ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha.2⟩
      · intro ha
        exact ⟨chainData.2.1 l (side inside) ha,(Finset.mem_filter.mp ha).2⟩
    apply miss
    refine ⟨src D (j,t),?_,?_⟩
    · simpa only [outer,eq] using cold
    · intro a ha
      exact mem_supp.mp ((hit a (chainData.2.1 l (side inside) ha)).mpr (Finset.mem_filter.mp ha).2)
  let Z := (absent J D).image w
  have sub : Z ⊆ (inner 26 D).filter (fun v => ¬ (supp 26 D v).Nonempty) := by
    intro v hv
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
    exact sem_bzero_mem h.1 (hw l hl).2.1 (hw l hl).2.2
  have sum : Z.card ≤ Bzero 26 D := by
    calc Z.card = ∑ _v ∈ Z, 1 := by simp
         _ ≤ ∑ v ∈ Z, (fanout D v - 1) := by
           apply Finset.sum_le_sum
           intro v hv
           obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
           have fan := (hw l hl).2.1
           omega
         _ ≤ Bzero 26 D := Finset.sum_le_sum_of_subset sub
  simpa only [Z,Finset.card_image_of_injOn inj] using sum
theorem bank_subset {D : Dag} (hs : Strict 26 D) (L : Finset V) (sub : L ⊆ lines) (bank : ∀ l∈L,Ready D l) : 3*L.card≤(L.biUnion (bankFees D)).card := by
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
  have bankFour (l : V) (hl : l∈L) : 3 ≤ (bankFees D l).card := by
    obtain ⟨w,cold,seen⟩ := bank l hl
    have amount := exposure_price hs single (outer l) (by
      intro i a b _ ha hb
      simp [single] at ha hb
      exact ha.symm.trans hb) (neighborhood l) w cold seen
    rw [degree l (sub hl)] at amount
    change 3≤(credits D single (outer l) (neighborhood l)).card
    omega
  let B := L.biUnion (bankFees D)
  have bankTotal : 3*L.card≤B.card := by
    change 3*L.card ≤ (L.biUnion (bankFees D)).card
    rw [Finset.card_biUnion (by intro i hi j hj hne; exact separate i hi j hj hne)]
    have bound := Finset.sum_le_sum bankFour
    simpa [Nat.mul_comm] using bound
  exact bankTotal


theorem pure_charge {D : Dag} (hg : sem_Gr G) (h : StrictLive 26 D) (hc : sem_Comp 26 G D)
    (pure : ineligSet 26 D ⊆ lines) : 25+3*(ineligSet 26 D).card ≤ D.length + 2*Bzero 26 D := by
  classical
  let I := ineligSet 26 D
  let L := I \ absent I D
  have subL : L ⊆ lines := fun _ hv => pure (Finset.mem_sdiff.mp hv).1
  have bank : ∀l∈L,Ready D l := by
    intro l hl
    obtain ⟨mem,notin⟩ := Finset.mem_sdiff.mp hl
    by_contra neg
    exact notin (absent_mem.mpr ⟨mem,neg⟩)
  have dis : (absent I D).card ≤ Bzero 26 D := loss hg h hc pure (show I ⊆ ineligSet 26 D from subset_rfl)
  have toll := Finset.card_sdiff_add_card_eq_card (show absent I D ⊆ I from fun _ hv => (absent_mem.mp hv).1)
  change L.card+_=I.card at toll
  obtain ⟨pcount,pin,_,nbl,-⟩ := chainData
  have total : I.card + (eligSet 26 D).card = 26 := by
    simpa [I,ineligSet] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (eligSet 26 D))
  obtain ⟨pos,hp⟩ := k4_assigned hg h hc
  obtain ⟨b,hb⟩ := sem_exists_pureBranch hg h.1 hc
  have slot := k4_exits_ge hp pts I (fun l hl => ⟨hl,nbl _ (pure hl)⟩)
  have nex := Finset.card_le_card slot.1
  rw [slot.2] at nex
  have sub : L.biUnion (bankFees D) ⊆ merges 26 D (carrierT 26 D pts) := by
    intro j hj
    obtain ⟨l,hl,jl⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hr,tag,_,a,ha,sa,b,hb,_,sb⟩ := Finset.mem_filter.mp jl
    have ja := Finset.mem_range.mp hr
    have keep {v : V} {w : ℕ} (hv : v∈neighborhood l) (sw : sees D single v w) : w∈carrierT 26 D pts :=
      k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨mem_supp.mpr sw,pin l (subL hl) hv⟩⟩
    have aa : sees D single a (26+j) := by
      unfold sees at *
      rw [val_gate h.1 _ j ja,tag,gop_false,sa]
      rfl
    exact Finset.mem_filter.mpr ⟨hr,keep ha aa,keep ha sa,keep hb sb⟩
  have mergeCost := (bank_subset h.1 L subL bank).trans (Finset.card_le_card sub)
  have budget := k4_budget hg h hc b hb pts
  rw [pcount] at budget
  have raw := surplus_identity h
  have parts := totalSurplus_split 26 D
  change 25+3*I.card ≤ _
  have eabs : (absent (ineligSet 26 D) D).card=(absent I D).card := rfl
  have totalI : I.card=(I.image pos).card := slot.2.symm
  omega

end Exposure17245

namespace Deep17245
open Geometry17245 Mixed17245 PEqualNP.Outside.L_meta_971_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 32768
def zrows : Array Nat := #[0x2034,0xc030,0xc440,0x18014,0x18030,0x24840,0x28014,0x28104,0x48060,0x68004,0x2074,0x6450,0xc430,0x18034,0x240d0,0x30094,0x38104,0x4c440,0x500a4,0x8c030,0x98014,0x98030,0xa4840,0xa8014,0xc8060,0xe8004,0xea000,0x102430,0x10c030,0x118030,0x32c000,0x34c000,0x3a2000,0x2474,0x64d0,0xa074,0xc470,0x160b0,0x18134,0x248d0,0x28154,0x30194,0x3a104,0x48464,0x4e440,0x510a4,0x8e030,0x9c030,0xa6840,0xaa014,0xca060,0xfa000,0x102530,0x10e030,0x11a030,0x143420,0x17c000,0x1bc000,0x1da000,0x1f4000,0x27c000,0x298014,0x2bc000,0x2f8000,0x33c000,0x36c000,0x39c000,0x3a6000,0x4ea000,0x578000,0x5f0000,0x74c000,0x7c2000,0x8e8004,0x8f8000,0xab8000,0xad8000,0x2574,0x64f0,0xa474,0xe470,0x1a134,0x268d0,0x2a154,0x32194,0x3a114,0x4a464,0x4e460,0x530a4,0x8e070,0xa6850,0xaa054,0xca064,0xfe000,0x10a530,0x10e430,0x11a130,0x19c030,0x1be000,0x1de000,0x1fc000,0x2b8014,0x2fa000,0x37c000,0x39e000,0x3ae000,0x3b6000,0x3bc000,0x3da000,0x3f8000,0x4fa000,0x57c000,0x5f4000,0x67c000,0x6bc000,0x6ea000,0x6f8000,0x73c000,0x74e000,0x75c000,0x76c000,0x778000,0x7a6000,0x7d2000,0x7f0000,0x8f8004,0xaba000,0xada000,0xaf8000,0xba6000,0x25f4,0x6cf0,0xa574,0x19e030,0x1fe000,0x2ba014,0x2fe000,0x37e000,0x3be000,0x3de000,0x3ee000,0x3f6000,0x3fa000,0x4fe000,0x57e000,0x5be000,0x5de000,0x5f6000,0x5fa000,0x67e000,0x6be000,0x6fa000,0x73e000,0x75e000,0x76e000,0x77a000,0x79e000,0x7ae000,0x7b6000,0x7ce000,0x7d6000,0x7e6000,0x7ea000,0x7f2000,0xabe000,0xade000,0xaf8004,0xafa000,0xbae000,0x2df4,0xef8004,0x3df4,0xefa004]
def dz (i : Nat) := members ((zrows[i]?).getD 0)
def trows : Array Nat := #[0x400000,0x1000,0x1000,0x800,0x800,0x1000,0x1000,0x1000,0x800,0x200,0x300000,0x10001,0x21000,0x400800,0x101000,0x100400,0xc00,0x900,0x100800,0x180,0x480,0x480,0x500,0x480,0x180,0x180,0x200,0x20200,0x84,0xc0,0x1000,0x100,0x200,0x2010000,0x180001,0x500002,0x211000,0x400001,0x204800,0x51000,0x141000,0x44400,0x203,0x120800,0x203,0x24800,0xb,0x1101,0x209,0x20a,0x20a,0x600,0x280200,0x203,0x203,0x20200,0xa00,0x480,0x280,0x300,0x900,0x142,0x500,0x500,0x41,0x300,0xc0,0x101,0x81,0x280,0x280,0x81,0x180,0x1008,0xc00,0x440,0x140,0x244000,0x620000,0x2030000,0x820003,0x1040003,0x808201,0x804202,0x2080201,0x2041001,0x1010202,0x220801,0x1008201,0xa00081,0x840401,0x900402,0x1100102,0x101,0x60082,0x2020081,0x240081,0xc4,0x201,0x101,0x180,0x1420,0x102,0x140,0x3,0x82,0x41,0xc0,0x42,0xc0,0x81,0x81,0x81,0x21,0x21,0x22,0xa0,0x21,0x3,0x41,0xa0,0x60,0x21,0x41,0x60,0xc00,0xa,0xa,0x140,0x48,0x580000,0x1058000,0x2c4000,0x20b,0x203,0x20b,0x1101,0x203,0x203,0x105,0xb00,0xb00,0x203,0x91,0x203,0xa1,0x91,0x209,0x2c0,0x203,0xb,0x203,0x203,0x203,0x203,0x203,0xa1,0xa1,0xa1,0x188,0x105,0x310,0x2c0,0x203,0x1101,0x1101,0x142,0x20a,0x1082,0x1050000,0xb0,0x82c000,0x20b]
def dt (i : Nat) := members ((trows[i]?).getD 0)
def urows : Array Nat := #[0x2004,0x30,0x440,0x14,0x30,0x840,0x14,0x104,0x60,0x8004,0x2010,0x10,0x10,0x4,0x10,0x10,0x104,0x440,0x20,0x30,0x14,0x30,0x840,0x14,0x60,0x20004,0x88000,0x10,0x30,0x30,0x300000,0x108000,0x280000,0x2020,0x10,0x0,0x10,0x0,0x10,0x80,0x0,0x80,0x104,0x0,0x440,0x80,0x30,0x30,0x840,0x14,0x60,0x8000,0x10,0x30,0x30,0x0,0x4000,0x4000,0x10000,0x10000,0x20000,0x14,0x8000,0x8000,0x28000,0x8000,0x4000,0x120000,0x60000,0x10000,0x10000,0x240000,0x2000,0x40004,0x800000,0x8000,0x8000,0x2400,0x6000,0xa000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28000,0x0,0x0,0x0,0x30,0x88000,0x108000,0x30000,0x14,0x30000,0x28000,0x180000,0x24000,0xa0000,0x24000,0xc0000,0x60000,0x60000,0x60000,0x60000,0x48000,0x88000,0xc0000,0x50000,0x108000,0x140000,0x48000,0x44000,0x48000,0x180000,0xc0000,0xc0000,0x800004,0x30000,0x50000,0x28000,0x24000,0x2000,0x6000,0xa000,0x30,0x80000,0x14,0x0,0x0,0x80000,0x8000,0x0,0x0,0x80000,0x20000,0x0,0x0,0x0,0x0,0x0,0x0,0x20000,0x80000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x80000,0x0,0x0,0x20004,0x10000,0x0,0x2080,0x10004,0x2000,0x4]
def du (i : Nat) := members ((urows[i]?).getD 0)
def hrows : Array Nat := #[0x400000,0x1000,0x1000,0x800,0x800,0x1000,0x1000,0x1000,0x800,0x200,0x300000,0x10001,0x21000,0x400800,0x101000,0x100400,0xc00,0x900,0x100800,0x180,0x480,0x480,0x500,0x480,0x180,0x180,0x200,0x20200,0x84,0xc0,0x1000,0x100,0x200,0x2010000,0x180001,0x500002,0x211000,0x400001,0x204800,0x51000,0x141000,0x44400,0x203,0x120800,0x203,0x24800,0xb,0x1101,0x209,0x20a,0x20a,0x600,0x280200,0x203,0x203,0x20200,0xa00,0x480,0x280,0x300,0x900,0x142,0x500,0x500,0x41,0x300,0xc0,0x101,0x81,0x280,0x280,0x81,0x180,0x1008,0xc00,0x440,0x140,0x244000,0x620000,0x2030000,0x820003,0x1040003,0x808201,0x804202,0x2080201,0x2041001,0x1010202,0x220801,0x1008201,0xa00081,0x840401,0x900402,0x1100102,0x101,0x60082,0x2020081,0x240081,0xc4,0x201,0x101,0x180,0x1420,0x102,0x140,0x3,0x82,0x41,0xc0,0x42,0xc0,0x81,0x81,0x81,0x21,0x21,0x22,0xa0,0x21,0x3,0x41,0xa0,0x60,0x21,0x41,0x60,0xc00,0xa,0xa,0x140,0x48,0x580000,0x1058000,0x2c4000,0x20b,0x3,0x20b,0x1001,0x3,0x203,0x5,0x800,0x800,0x3,0x90,0x2,0x20,0x10,0x8,0x40,0x202,0xa,0x203,0x202,0x202,0x3,0x3,0x20,0x21,0xa0,0x8,0x4,0x10,0x40,0x3,0x101,0x1001,0x142,0x20a,0x82,0x1050000,0xb0,0x82c000,0x20b]
def dh (i : Nat) := members ((hrows[i]?).getD 0)
def arows : Array Nat := #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x600cf,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x204e98,0x12091b,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x12091b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x21129c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x44144e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820987,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x108539,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x91236,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x181833,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc678,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x108539,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x84a72,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x21129c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2101929,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x540aa,0x191032,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x12091b,0x281a15,0x0,0x0,0x0,0x0,0x0,0x0,0x701c08,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41420a,0x0,0x16000b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x23009c,0x0,0x0,0x0,0x281a15,0x0,0x0,0x0,0x0,0x41130e,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x6804d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x244488,0x0,0x0,0x301c19,0x0,0x0,0x0,0x0,0x0,0x0,0x248da,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x5802c,0x0,0x0,0x0,0x14142b,0x0,0x41130e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x14442a,0x0,0x0,0x0,0x0,0x0,0x581802,0x0,0x1051082,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xc4062,0x0,0x0,0x0,0x14142b,0x0,0x0,0x0,0x404e4a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x13011a,0x0,0x0,0x0,0x0,0x0,0x381811,0x0,0x0,0x224898,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2c058,0x0,0x0,0x12091b,0x0,0x0,0x204e98,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2a0815,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x21129c,0x0,0x481a46,0x0,0x0,0x0,0x0,0x113be,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x214298,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x341409,0x0,0x0,0x0,0x604e08,0x0,0x0,0x7408a,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x61120c,0x0,0x0,0x0,0x43010e,0x26800d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2120909,0x2211288,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x7408a,0x830186,0xa20885,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x16000b,0x0,0x0,0x10444c2,0x1241481,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x16000b,0x0,0x818324,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x848425,0x0,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2208209,0x0,0x0,0x0,0xa04e80,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x8444a2,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41420a,0x0,0x0,0x2084a60,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x20c1061,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2208209,0x0,0x0,0x0,0x0,0x0,0x1880203,0x2441048,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28400a1,0x0,0x0,0x0,0x0,0x0,0x2081a61,0x0,0x0,0x0,0x0,0x0,0x0,0x14142b,0x0,0x1211290,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1030192,0x0,0x0,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x41420a,0x0,0x62080c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1220091,0x0,0x0,0x0,0x0,0x0,0x281a15,0x0,0x0,0x0,0x12091b,0x0,0x0,0x0,0x0,0x100c650,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1028151,0x0,0x0,0x0,0x0,0x0,0x1880203,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2208209,0x0,0xa10284,0x0,0x0,0x0,0x0,0x0,0x0,0xb00c01,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x820987,0x0,0x24148d,0x0,0x0,0xc40406,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x28400a1,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x808725,0x0,0x0,0x0,0x0,0x14142b,0x0,0x0,0x0,0xb00c01,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x910122,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x804ea2,0x0,0x0,0x14142b,0x0,0x0,0x0,0x3101101,0x0,0x0,0x0,0x0,0x0,0x0,0x1104412,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1011392,0x0,0x0,0x0,0x12091b,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x26008d,0x0,0x0,0x0,0x0,0x0,0xe0047,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1051082,0x824882,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2030188,0x0,0x0,0x0,0x0,0x0,0x0,0x20a0841,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2201a89,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x600cf,0x244488,0x0,0x0,0x0,0x0,0x0,0x0,0x2c1005,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0xa00e85,0x0,0x0,0x600cf,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x201e9d,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x81a77,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x52480a,0xc84a02,0x0,0x9a0803,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x15d1002,0x3be8001,0x0,0x3c18300,0x0,0x0,0x0,0x0,0x0,0x67800c,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x33c1001,0x0,0x0,0x0,0x2e84a00,0x2274088,0x0,0x1df4002,0x0,0x0,0x0,0x0,0x401f4e,0x201e9d,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x201e9d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x800fa7,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x113be,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x4efa,0x877d,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x414ef,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x209df,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3df4,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x4efa,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x0,0x0,0x0,0x0,0x0,0x401f4e,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x11c1003,0x0,0x1491202,0x0,0x0,0x0,0x0,0x0,0x7408a,0x0,0x0,0x0,0x0,0x0,0x2001be9,0x10017d3,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3be8001,0x1df4002,0x0,0x3e9c200,0x0,0x0,0x0,0x0,0x0,0x277c008,0x0,0x0,0x4efa,0x2001be9,0x0,0x10017d3,0x0,0x0,0x0,0x0,0x0,0x101d3b,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]
def da (i : Nat) (f : V) := members ((arows[i*26+f.val]?).getD 0)
theorem dd0 : Data (dz 0) (dt 0) (du 0) (dh 0) (da 0) := verifies_sound (by decide +kernel)
theorem dp0 : Good 3 (dz 0) := .done _ _ _ _ _ dd0 (by decide +kernel)
theorem dd1 : Data (dz 1) (dt 1) (du 1) (dh 1) (da 1) := verifies_sound (by decide +kernel)
theorem dp1 : Good 3 (dz 1) := .done _ _ _ _ _ dd1 (by decide +kernel)
theorem dd2 : Data (dz 2) (dt 2) (du 2) (dh 2) (da 2) := verifies_sound (by decide +kernel)
theorem dp2 : Good 3 (dz 2) := .done _ _ _ _ _ dd2 (by decide +kernel)
theorem dd3 : Data (dz 3) (dt 3) (du 3) (dh 3) (da 3) := verifies_sound (by decide +kernel)
theorem dp3 : Good 3 (dz 3) := .done _ _ _ _ _ dd3 (by decide +kernel)
theorem dd4 : Data (dz 4) (dt 4) (du 4) (dh 4) (da 4) := verifies_sound (by decide +kernel)
theorem dp4 : Good 3 (dz 4) := .done _ _ _ _ _ dd4 (by decide +kernel)
theorem dd5 : Data (dz 5) (dt 5) (du 5) (dh 5) (da 5) := verifies_sound (by decide +kernel)
theorem dp5 : Good 3 (dz 5) := .done _ _ _ _ _ dd5 (by decide +kernel)
theorem dd6 : Data (dz 6) (dt 6) (du 6) (dh 6) (da 6) := verifies_sound (by decide +kernel)
theorem dp6 : Good 3 (dz 6) := .done _ _ _ _ _ dd6 (by decide +kernel)
theorem dd7 : Data (dz 7) (dt 7) (du 7) (dh 7) (da 7) := verifies_sound (by decide +kernel)
theorem dp7 : Good 3 (dz 7) := .done _ _ _ _ _ dd7 (by decide +kernel)
theorem dd8 : Data (dz 8) (dt 8) (du 8) (dh 8) (da 8) := verifies_sound (by decide +kernel)
theorem dp8 : Good 3 (dz 8) := .done _ _ _ _ _ dd8 (by decide +kernel)
theorem dd9 : Data (dz 9) (dt 9) (du 9) (dh 9) (da 9) := verifies_sound (by decide +kernel)
theorem dp9 : Good 3 (dz 9) := .done _ _ _ _ _ dd9 (by decide +kernel)
theorem dd10 : Data (dz 10) (dt 10) (du 10) (dh 10) (da 10) := verifies_sound (by decide +kernel)
theorem dp10 : Good 3 (dz 10) := by
  have eq : (dz 10).erase 6=dz 0 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 dd10 (by decide +kernel) (eq.symm ▸ dp0)
theorem dd11 : Data (dz 11) (dt 11) (du 11) (dh 11) (da 11) := verifies_sound (by decide +kernel)
theorem dp11 : Good 3 (dz 11) := .done _ _ _ _ _ dd11 (by decide +kernel)
theorem dd12 : Data (dz 12) (dt 12) (du 12) (dh 12) (da 12) := verifies_sound (by decide +kernel)
theorem dp12 : Good 3 (dz 12) := .done _ _ _ _ _ dd12 (by decide +kernel)
theorem dd13 : Data (dz 13) (dt 13) (du 13) (dh 13) (da 13) := verifies_sound (by decide +kernel)
theorem dp13 : Good 3 (dz 13) := .done _ _ _ _ _ dd13 (by decide +kernel)
theorem dd14 : Data (dz 14) (dt 14) (du 14) (dh 14) (da 14) := verifies_sound (by decide +kernel)
theorem dp14 : Good 3 (dz 14) := .done _ _ _ _ _ dd14 (by decide +kernel)
theorem dd15 : Data (dz 15) (dt 15) (du 15) (dh 15) (da 15) := verifies_sound (by decide +kernel)
theorem dp15 : Good 3 (dz 15) := .done _ _ _ _ _ dd15 (by decide +kernel)
theorem dd16 : Data (dz 16) (dt 16) (du 16) (dh 16) (da 16) := verifies_sound (by decide +kernel)
theorem dp16 : Good 3 (dz 16) := by
  have eq : (dz 16).erase 16=dz 7 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd16 (by decide +kernel) (eq.symm ▸ dp7)
theorem dd17 : Data (dz 17) (dt 17) (du 17) (dh 17) (da 17) := verifies_sound (by decide +kernel)
theorem dp17 : Good 3 (dz 17) := by
  have eq : (dz 17).erase 18=dz 2 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 dd17 (by decide +kernel) (eq.symm ▸ dp2)
theorem dd18 : Data (dz 18) (dt 18) (du 18) (dh 18) (da 18) := verifies_sound (by decide +kernel)
theorem dp18 : Good 3 (dz 18) := .done _ _ _ _ _ dd18 (by decide +kernel)
theorem dd19 : Data (dz 19) (dt 19) (du 19) (dh 19) (da 19) := verifies_sound (by decide +kernel)
theorem dp19 : Good 3 (dz 19) := by
  have eq : (dz 19).erase 19=dz 1 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd19 (by decide +kernel) (eq.symm ▸ dp1)
theorem dd20 : Data (dz 20) (dt 20) (du 20) (dh 20) (da 20) := verifies_sound (by decide +kernel)
theorem dp20 : Good 3 (dz 20) := by
  have eq : (dz 20).erase 19=dz 3 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd20 (by decide +kernel) (eq.symm ▸ dp3)
theorem dd21 : Data (dz 21) (dt 21) (du 21) (dh 21) (da 21) := verifies_sound (by decide +kernel)
theorem dp21 : Good 3 (dz 21) := by
  have eq : (dz 21).erase 19=dz 4 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd21 (by decide +kernel) (eq.symm ▸ dp4)
theorem dd22 : Data (dz 22) (dt 22) (du 22) (dh 22) (da 22) := verifies_sound (by decide +kernel)
theorem dp22 : Good 3 (dz 22) := by
  have eq : (dz 22).erase 19=dz 5 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd22 (by decide +kernel) (eq.symm ▸ dp5)
theorem dd23 : Data (dz 23) (dt 23) (du 23) (dh 23) (da 23) := verifies_sound (by decide +kernel)
theorem dp23 : Good 3 (dz 23) := by
  have eq : (dz 23).erase 19=dz 6 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd23 (by decide +kernel) (eq.symm ▸ dp6)
theorem dd24 : Data (dz 24) (dt 24) (du 24) (dh 24) (da 24) := verifies_sound (by decide +kernel)
theorem dp24 : Good 3 (dz 24) := by
  have eq : (dz 24).erase 19=dz 8 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd24 (by decide +kernel) (eq.symm ▸ dp8)
theorem dd25 : Data (dz 25) (dt 25) (du 25) (dh 25) (da 25) := verifies_sound (by decide +kernel)
theorem dp25 : Good 3 (dz 25) := by
  have eq : (dz 25).erase 19=dz 9 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd25 (by decide +kernel) (eq.symm ▸ dp9)
theorem dd26 : Data (dz 26) (dt 26) (du 26) (dh 26) (da 26) := verifies_sound (by decide +kernel)
theorem dp26 : Good 3 (dz 26) := .done _ _ _ _ _ dd26 (by decide +kernel)
theorem dd27 : Data (dz 27) (dt 27) (du 27) (dh 27) (da 27) := verifies_sound (by decide +kernel)
theorem dp27 : Good 3 (dz 27) := .done _ _ _ _ _ dd27 (by decide +kernel)
theorem dd28 : Data (dz 28) (dt 28) (du 28) (dh 28) (da 28) := verifies_sound (by decide +kernel)
theorem dp28 : Good 3 (dz 28) := by
  have eq : (dz 28).erase 20=dz 1 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd28 (by decide +kernel) (eq.symm ▸ dp1)
theorem dd29 : Data (dz 29) (dt 29) (du 29) (dh 29) (da 29) := verifies_sound (by decide +kernel)
theorem dp29 : Good 3 (dz 29) := by
  have eq : (dz 29).erase 20=dz 4 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd29 (by decide +kernel) (eq.symm ▸ dp4)
theorem dd30 : Data (dz 30) (dt 30) (du 30) (dh 30) (da 30) := verifies_sound (by decide +kernel)
theorem dp30 : Good 3 (dz 30) := .done _ _ _ _ _ dd30 (by decide +kernel)
theorem dd31 : Data (dz 31) (dt 31) (du 31) (dh 31) (da 31) := verifies_sound (by decide +kernel)
theorem dp31 : Good 3 (dz 31) := .done _ _ _ _ _ dd31 (by decide +kernel)
theorem dd32 : Data (dz 32) (dt 32) (du 32) (dh 32) (da 32) := verifies_sound (by decide +kernel)
theorem dp32 : Good 3 (dz 32) := .done _ _ _ _ _ dd32 (by decide +kernel)
theorem dd33 : Data (dz 33) (dt 33) (du 33) (dh 33) (da 33) := verifies_sound (by decide +kernel)
theorem dp33 : Good 3 (dz 33) := by
  have eq : (dz 33).erase 10=dz 10 := by decide +kernel
  exact .pivot _ _ _ _ _ 10 dd33 (by decide +kernel) (eq.symm ▸ dp10)
theorem dd34 : Data (dz 34) (dt 34) (du 34) (dh 34) (da 34) := verifies_sound (by decide +kernel)
theorem dp34 : Good 3 (dz 34) := by
  have eq : (dz 34).erase 7=dz 11 := by decide +kernel
  exact .pivot _ _ _ _ _ 7 dd34 (by decide +kernel) (eq.symm ▸ dp11)
theorem dd35 : Data (dz 35) (dt 35) (du 35) (dh 35) (da 35) := verifies_sound (by decide +kernel)
theorem dp35 : Good 3 (dz 35) := .done _ _ _ _ _ dd35 (by decide +kernel)
theorem dd36 : Data (dz 36) (dt 36) (du 36) (dh 36) (da 36) := verifies_sound (by decide +kernel)
theorem dp36 : Good 3 (dz 36) := by
  have eq : (dz 36).erase 6=dz 12 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 dd36 (by decide +kernel) (eq.symm ▸ dp12)
theorem dd37 : Data (dz 37) (dt 37) (du 37) (dh 37) (da 37) := verifies_sound (by decide +kernel)
theorem dp37 : Good 3 (dz 37) := .done _ _ _ _ _ dd37 (by decide +kernel)
theorem dd38 : Data (dz 38) (dt 38) (du 38) (dh 38) (da 38) := verifies_sound (by decide +kernel)
theorem dp38 : Good 3 (dz 38) := by
  have eq : (dz 38).erase 8=dz 13 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd38 (by decide +kernel) (eq.symm ▸ dp13)
theorem dd39 : Data (dz 39) (dt 39) (du 39) (dh 39) (da 39) := verifies_sound (by decide +kernel)
theorem dp39 : Good 3 (dz 39) := by
  have eq : (dz 39).erase 11=dz 14 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 dd39 (by decide +kernel) (eq.symm ▸ dp14)
theorem dd40 : Data (dz 40) (dt 40) (du 40) (dh 40) (da 40) := verifies_sound (by decide +kernel)
theorem dp40 : Good 3 (dz 40) := .done _ _ _ _ _ dd40 (by decide +kernel)
theorem dd41 : Data (dz 41) (dt 41) (du 41) (dh 41) (da 41) := verifies_sound (by decide +kernel)
theorem dp41 : Good 3 (dz 41) := by
  have eq : (dz 41).erase 8=dz 15 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd41 (by decide +kernel) (eq.symm ▸ dp15)
theorem dd42 : Data (dz 42) (dt 42) (du 42) (dh 42) (da 42) := verifies_sound (by decide +kernel)
theorem dp42 : Good 3 (dz 42) := by
  have eq : (dz 42).erase 13=dz 16 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd42 (by decide +kernel) (eq.symm ▸ dp16)
theorem dd43 : Data (dz 43) (dt 43) (du 43) (dh 43) (da 43) := verifies_sound (by decide +kernel)
theorem dp43 : Good 3 (dz 43) := .done _ _ _ _ _ dd43 (by decide +kernel)
theorem dd44 : Data (dz 44) (dt 44) (du 44) (dh 44) (da 44) := verifies_sound (by decide +kernel)
theorem dp44 : Good 3 (dz 44) := by
  have eq : (dz 44).erase 13=dz 17 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd44 (by decide +kernel) (eq.symm ▸ dp17)
theorem dd45 : Data (dz 45) (dt 45) (du 45) (dh 45) (da 45) := verifies_sound (by decide +kernel)
theorem dp45 : Good 3 (dz 45) := by
  have eq : (dz 45).erase 12=dz 18 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 dd45 (by decide +kernel) (eq.symm ▸ dp18)
theorem dd46 : Data (dz 46) (dt 46) (du 46) (dh 46) (da 46) := verifies_sound (by decide +kernel)
theorem dp46 : Good 3 (dz 46) := by
  have eq : (dz 46).erase 13=dz 19 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd46 (by decide +kernel) (eq.symm ▸ dp19)
theorem dd47 : Data (dz 47) (dt 47) (du 47) (dh 47) (da 47) := verifies_sound (by decide +kernel)
theorem dp47 : Good 3 (dz 47) := by
  have eq : (dz 47).erase 14=dz 21 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd47 (by decide +kernel) (eq.symm ▸ dp21)
theorem dd48 : Data (dz 48) (dt 48) (du 48) (dh 48) (da 48) := verifies_sound (by decide +kernel)
theorem dp48 : Good 3 (dz 48) := by
  have eq : (dz 48).erase 13=dz 22 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd48 (by decide +kernel) (eq.symm ▸ dp22)
theorem dd49 : Data (dz 49) (dt 49) (du 49) (dh 49) (da 49) := verifies_sound (by decide +kernel)
theorem dp49 : Good 3 (dz 49) := by
  have eq : (dz 49).erase 13=dz 23 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd49 (by decide +kernel) (eq.symm ▸ dp23)
theorem dd50 : Data (dz 50) (dt 50) (du 50) (dh 50) (da 50) := verifies_sound (by decide +kernel)
theorem dp50 : Good 3 (dz 50) := by
  have eq : (dz 50).erase 13=dz 24 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd50 (by decide +kernel) (eq.symm ▸ dp24)
theorem dd51 : Data (dz 51) (dt 51) (du 51) (dh 51) (da 51) := verifies_sound (by decide +kernel)
theorem dp51 : Good 3 (dz 51) := .done _ _ _ _ _ dd51 (by decide +kernel)
theorem dd52 : Data (dz 52) (dt 52) (du 52) (dh 52) (da 52) := verifies_sound (by decide +kernel)
theorem dp52 : Good 3 (dz 52) := by
  have eq : (dz 52).erase 8=dz 27 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd52 (by decide +kernel) (eq.symm ▸ dp27)
theorem dd53 : Data (dz 53) (dt 53) (du 53) (dh 53) (da 53) := verifies_sound (by decide +kernel)
theorem dp53 : Good 3 (dz 53) := by
  have eq : (dz 53).erase 13=dz 28 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd53 (by decide +kernel) (eq.symm ▸ dp28)
theorem dd54 : Data (dz 54) (dt 54) (du 54) (dh 54) (da 54) := verifies_sound (by decide +kernel)
theorem dp54 : Good 3 (dz 54) := by
  have eq : (dz 54).erase 13=dz 29 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd54 (by decide +kernel) (eq.symm ▸ dp29)
theorem dd55 : Data (dz 55) (dt 55) (du 55) (dh 55) (da 55) := verifies_sound (by decide +kernel)
theorem dp55 : Good 3 (dz 55) := .done _ _ _ _ _ dd55 (by decide +kernel)
theorem dd56 : Data (dz 56) (dt 56) (du 56) (dh 56) (da 56) := verifies_sound (by decide +kernel)
theorem dp56 : Good 3 (dz 56) := .done _ _ _ _ _ dd56 (by decide +kernel)
theorem dd57 : Data (dz 57) (dt 57) (du 57) (dh 57) (da 57) := verifies_sound (by decide +kernel)
theorem dp57 : Good 3 (dz 57) := .done _ _ _ _ _ dd57 (by decide +kernel)
theorem dd58 : Data (dz 58) (dt 58) (du 58) (dh 58) (da 58) := verifies_sound (by decide +kernel)
theorem dp58 : Good 3 (dz 58) := .done _ _ _ _ _ dd58 (by decide +kernel)
theorem dd59 : Data (dz 59) (dt 59) (du 59) (dh 59) (da 59) := verifies_sound (by decide +kernel)
theorem dp59 : Good 3 (dz 59) := .done _ _ _ _ _ dd59 (by decide +kernel)
theorem dd60 : Data (dz 60) (dt 60) (du 60) (dh 60) (da 60) := verifies_sound (by decide +kernel)
theorem dp60 : Good 3 (dz 60) := .done _ _ _ _ _ dd60 (by decide +kernel)
theorem dd61 : Data (dz 61) (dt 61) (du 61) (dh 61) (da 61) := verifies_sound (by decide +kernel)
theorem dp61 : Good 3 (dz 61) := by
  have eq : (dz 61).erase 21=dz 20 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd61 (by decide +kernel) (eq.symm ▸ dp20)
theorem dd62 : Data (dz 62) (dt 62) (du 62) (dh 62) (da 62) := verifies_sound (by decide +kernel)
theorem dp62 : Good 3 (dz 62) := .done _ _ _ _ _ dd62 (by decide +kernel)
theorem dd63 : Data (dz 63) (dt 63) (du 63) (dh 63) (da 63) := verifies_sound (by decide +kernel)
theorem dp63 : Good 3 (dz 63) := .done _ _ _ _ _ dd63 (by decide +kernel)
theorem dd64 : Data (dz 64) (dt 64) (du 64) (dh 64) (da 64) := verifies_sound (by decide +kernel)
theorem dp64 : Good 3 (dz 64) := by
  have eq : (dz 64).erase 16=dz 30 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd64 (by decide +kernel) (eq.symm ▸ dp30)
theorem dd65 : Data (dz 65) (dt 65) (du 65) (dh 65) (da 65) := verifies_sound (by decide +kernel)
theorem dp65 : Good 3 (dz 65) := .done _ _ _ _ _ dd65 (by decide +kernel)
theorem dd66 : Data (dz 66) (dt 66) (du 66) (dh 66) (da 66) := verifies_sound (by decide +kernel)
theorem dp66 : Good 3 (dz 66) := .done _ _ _ _ _ dd66 (by decide +kernel)
theorem dd67 : Data (dz 67) (dt 67) (du 67) (dh 67) (da 67) := verifies_sound (by decide +kernel)
theorem dp67 : Good 3 (dz 67) := by
  have eq : (dz 67).erase 14=dz 32 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd67 (by decide +kernel) (eq.symm ▸ dp32)
theorem dd68 : Data (dz 68) (dt 68) (du 68) (dh 68) (da 68) := verifies_sound (by decide +kernel)
theorem dp68 : Good 3 (dz 68) := by
  have eq : (dz 68).erase 22=dz 26 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd68 (by decide +kernel) (eq.symm ▸ dp26)
theorem dd69 : Data (dz 69) (dt 69) (du 69) (dh 69) (da 69) := verifies_sound (by decide +kernel)
theorem dp69 : Good 3 (dz 69) := .done _ _ _ _ _ dd69 (by decide +kernel)
theorem dd70 : Data (dz 70) (dt 70) (du 70) (dh 70) (da 70) := verifies_sound (by decide +kernel)
theorem dp70 : Good 3 (dz 70) := .done _ _ _ _ _ dd70 (by decide +kernel)
theorem dd71 : Data (dz 71) (dt 71) (du 71) (dh 71) (da 71) := verifies_sound (by decide +kernel)
theorem dp71 : Good 3 (dz 71) := by
  have eq : (dz 71).erase 22=dz 31 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd71 (by decide +kernel) (eq.symm ▸ dp31)
theorem dd72 : Data (dz 72) (dt 72) (du 72) (dh 72) (da 72) := verifies_sound (by decide +kernel)
theorem dp72 : Good 3 (dz 72) := .done _ _ _ _ _ dd72 (by decide +kernel)
theorem dd73 : Data (dz 73) (dt 73) (du 73) (dh 73) (da 73) := verifies_sound (by decide +kernel)
theorem dp73 : Good 3 (dz 73) := by
  have eq : (dz 73).erase 23=dz 25 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 dd73 (by decide +kernel) (eq.symm ▸ dp25)
theorem dd74 : Data (dz 74) (dt 74) (du 74) (dh 74) (da 74) := verifies_sound (by decide +kernel)
theorem dp74 : Good 3 (dz 74) := .done _ _ _ _ _ dd74 (by decide +kernel)
theorem dd75 : Data (dz 75) (dt 75) (du 75) (dh 75) (da 75) := verifies_sound (by decide +kernel)
theorem dp75 : Good 3 (dz 75) := .done _ _ _ _ _ dd75 (by decide +kernel)
theorem dd76 : Data (dz 76) (dt 76) (du 76) (dh 76) (da 76) := verifies_sound (by decide +kernel)
theorem dp76 : Good 3 (dz 76) := .done _ _ _ _ _ dd76 (by decide +kernel)
theorem dd77 : Data (dz 77) (dt 77) (du 77) (dh 77) (da 77) := verifies_sound (by decide +kernel)
theorem dp77 : Good 3 (dz 77) := by
  have eq : (dz 77).erase 8=dz 33 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd77 (by decide +kernel) (eq.symm ▸ dp33)
theorem dd78 : Data (dz 78) (dt 78) (du 78) (dh 78) (da 78) := verifies_sound (by decide +kernel)
theorem dp78 : Good 3 (dz 78) := by
  have eq : (dz 78).erase 5=dz 34 := by decide +kernel
  exact .pivot _ _ _ _ _ 5 dd78 (by decide +kernel) (eq.symm ▸ dp34)
theorem dd79 : Data (dz 79) (dt 79) (du 79) (dh 79) (da 79) := verifies_sound (by decide +kernel)
theorem dp79 : Good 3 (dz 79) := by
  have eq : (dz 79).erase 10=dz 35 := by decide +kernel
  exact .pivot _ _ _ _ _ 10 dd79 (by decide +kernel) (eq.symm ▸ dp35)
theorem dd80 : Data (dz 80) (dt 80) (du 80) (dh 80) (da 80) := verifies_sound (by decide +kernel)
theorem dp80 : Good 3 (dz 80) := by
  have eq : (dz 80).erase 13=dz 36 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd80 (by decide +kernel) (eq.symm ▸ dp36)
theorem dd81 : Data (dz 81) (dt 81) (du 81) (dh 81) (da 81) := verifies_sound (by decide +kernel)
theorem dp81 : Good 3 (dz 81) := by
  have eq : (dz 81).erase 13=dz 38 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd81 (by decide +kernel) (eq.symm ▸ dp38)
theorem dd82 : Data (dz 82) (dt 82) (du 82) (dh 82) (da 82) := verifies_sound (by decide +kernel)
theorem dp82 : Good 3 (dz 82) := by
  have eq : (dz 82).erase 13=dz 39 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd82 (by decide +kernel) (eq.symm ▸ dp39)
theorem dd83 : Data (dz 83) (dt 83) (du 83) (dh 83) (da 83) := verifies_sound (by decide +kernel)
theorem dp83 : Good 3 (dz 83) := by
  have eq : (dz 83).erase 13=dz 40 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd83 (by decide +kernel) (eq.symm ▸ dp40)
theorem dd84 : Data (dz 84) (dt 84) (du 84) (dh 84) (da 84) := verifies_sound (by decide +kernel)
theorem dp84 : Good 3 (dz 84) := by
  have eq : (dz 84).erase 13=dz 41 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd84 (by decide +kernel) (eq.symm ▸ dp41)
theorem dd85 : Data (dz 85) (dt 85) (du 85) (dh 85) (da 85) := verifies_sound (by decide +kernel)
theorem dp85 : Good 3 (dz 85) := by
  have eq : (dz 85).erase 4=dz 42 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 dd85 (by decide +kernel) (eq.symm ▸ dp42)
theorem dd86 : Data (dz 86) (dt 86) (du 86) (dh 86) (da 86) := verifies_sound (by decide +kernel)
theorem dp86 : Good 3 (dz 86) := by
  have eq : (dz 86).erase 13=dz 43 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd86 (by decide +kernel) (eq.symm ▸ dp43)
theorem dd87 : Data (dz 87) (dt 87) (du 87) (dh 87) (da 87) := verifies_sound (by decide +kernel)
theorem dp87 : Good 3 (dz 87) := by
  have eq : (dz 87).erase 5=dz 44 := by decide +kernel
  exact .pivot _ _ _ _ _ 5 dd87 (by decide +kernel) (eq.symm ▸ dp44)
theorem dd88 : Data (dz 88) (dt 88) (du 88) (dh 88) (da 88) := verifies_sound (by decide +kernel)
theorem dp88 : Good 3 (dz 88) := by
  have eq : (dz 88).erase 13=dz 45 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd88 (by decide +kernel) (eq.symm ▸ dp45)
theorem dd89 : Data (dz 89) (dt 89) (du 89) (dh 89) (da 89) := verifies_sound (by decide +kernel)
theorem dp89 : Good 3 (dz 89) := by
  have eq : (dz 89).erase 6=dz 46 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 dd89 (by decide +kernel) (eq.symm ▸ dp46)
theorem dd90 : Data (dz 90) (dt 90) (du 90) (dh 90) (da 90) := verifies_sound (by decide +kernel)
theorem dp90 : Good 3 (dz 90) := by
  have eq : (dz 90).erase 4=dz 48 := by decide +kernel
  exact .pivot _ _ _ _ _ 4 dd90 (by decide +kernel) (eq.symm ▸ dp48)
theorem dd91 : Data (dz 91) (dt 91) (du 91) (dh 91) (da 91) := verifies_sound (by decide +kernel)
theorem dp91 : Good 3 (dz 91) := by
  have eq : (dz 91).erase 6=dz 49 := by decide +kernel
  exact .pivot _ _ _ _ _ 6 dd91 (by decide +kernel) (eq.symm ▸ dp49)
theorem dd92 : Data (dz 92) (dt 92) (du 92) (dh 92) (da 92) := verifies_sound (by decide +kernel)
theorem dp92 : Good 3 (dz 92) := by
  have eq : (dz 92).erase 2=dz 50 := by decide +kernel
  exact .pivot _ _ _ _ _ 2 dd92 (by decide +kernel) (eq.symm ▸ dp50)
theorem dd93 : Data (dz 93) (dt 93) (du 93) (dh 93) (da 93) := verifies_sound (by decide +kernel)
theorem dp93 : Good 3 (dz 93) := by
  have eq : (dz 93).erase 14=dz 51 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd93 (by decide +kernel) (eq.symm ▸ dp51)
theorem dd94 : Data (dz 94) (dt 94) (du 94) (dh 94) (da 94) := verifies_sound (by decide +kernel)
theorem dp94 : Good 3 (dz 94) := by
  have eq : (dz 94).erase 15=dz 52 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 dd94 (by decide +kernel) (eq.symm ▸ dp52)
theorem dd95 : Data (dz 95) (dt 95) (du 95) (dh 95) (da 95) := verifies_sound (by decide +kernel)
theorem dp95 : Good 3 (dz 95) := by
  have eq : (dz 95).erase 10=dz 53 := by decide +kernel
  exact .pivot _ _ _ _ _ 10 dd95 (by decide +kernel) (eq.symm ▸ dp53)
theorem dd96 : Data (dz 96) (dt 96) (du 96) (dh 96) (da 96) := verifies_sound (by decide +kernel)
theorem dp96 : Good 3 (dz 96) := by
  have eq : (dz 96).erase 8=dz 54 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd96 (by decide +kernel) (eq.symm ▸ dp54)
theorem dd97 : Data (dz 97) (dt 97) (du 97) (dh 97) (da 97) := verifies_sound (by decide +kernel)
theorem dp97 : Good 3 (dz 97) := by
  have eq : (dz 97).erase 20=dz 47 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd97 (by decide +kernel) (eq.symm ▸ dp47)
theorem dd98 : Data (dz 98) (dt 98) (du 98) (dh 98) (da 98) := verifies_sound (by decide +kernel)
theorem dp98 : Good 3 (dz 98) := by
  have eq : (dz 98).erase 13=dz 57 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd98 (by decide +kernel) (eq.symm ▸ dp57)
theorem dd99 : Data (dz 99) (dt 99) (du 99) (dh 99) (da 99) := verifies_sound (by decide +kernel)
theorem dp99 : Good 3 (dz 99) := by
  have eq : (dz 99).erase 14=dz 58 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd99 (by decide +kernel) (eq.symm ▸ dp58)
theorem dd100 : Data (dz 100) (dt 100) (du 100) (dh 100) (da 100) := verifies_sound (by decide +kernel)
theorem dp100 : Good 3 (dz 100) := by
  have eq : (dz 100).erase 19=dz 56 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd100 (by decide +kernel) (eq.symm ▸ dp56)
theorem dd101 : Data (dz 101) (dt 101) (du 101) (dh 101) (da 101) := verifies_sound (by decide +kernel)
theorem dp101 : Good 3 (dz 101) := by
  have eq : (dz 101).erase 17=dz 61 := by decide +kernel
  exact .pivot _ _ _ _ _ 17 dd101 (by decide +kernel) (eq.symm ▸ dp61)
theorem dd102 : Data (dz 102) (dt 102) (du 102) (dh 102) (da 102) := verifies_sound (by decide +kernel)
theorem dp102 : Good 3 (dz 102) := by
  have eq : (dz 102).erase 21=dz 51 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd102 (by decide +kernel) (eq.symm ▸ dp51)
theorem dd103 : Data (dz 103) (dt 103) (du 103) (dh 103) (da 103) := verifies_sound (by decide +kernel)
theorem dp103 : Good 3 (dz 103) := by
  have eq : (dz 103).erase 21=dz 56 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd103 (by decide +kernel) (eq.symm ▸ dp56)
theorem dd104 : Data (dz 104) (dt 104) (du 104) (dh 104) (da 104) := verifies_sound (by decide +kernel)
theorem dp104 : Good 3 (dz 104) := by
  have eq : (dz 104).erase 13=dz 66 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd104 (by decide +kernel) (eq.symm ▸ dp66)
theorem dd105 : Data (dz 105) (dt 105) (du 105) (dh 105) (da 105) := verifies_sound (by decide +kernel)
theorem dp105 : Good 3 (dz 105) := by
  have eq : (dz 105).erase 15=dz 67 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 dd105 (by decide +kernel) (eq.symm ▸ dp67)
theorem dd106 : Data (dz 106) (dt 106) (du 106) (dh 106) (da 106) := verifies_sound (by decide +kernel)
theorem dp106 : Good 3 (dz 106) := by
  have eq : (dz 106).erase 16=dz 67 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd106 (by decide +kernel) (eq.symm ▸ dp67)
theorem dd107 : Data (dz 107) (dt 107) (du 107) (dh 107) (da 107) := verifies_sound (by decide +kernel)
theorem dp107 : Good 3 (dz 107) := by
  have eq : (dz 107).erase 20=dz 62 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd107 (by decide +kernel) (eq.symm ▸ dp62)
theorem dd108 : Data (dz 108) (dt 108) (du 108) (dh 108) (da 108) := verifies_sound (by decide +kernel)
theorem dp108 : Good 3 (dz 108) := by
  have eq : (dz 108).erase 21=dz 58 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd108 (by decide +kernel) (eq.symm ▸ dp58)
theorem dd109 : Data (dz 109) (dt 109) (du 109) (dh 109) (da 109) := verifies_sound (by decide +kernel)
theorem dp109 : Good 3 (dz 109) := by
  have eq : (dz 109).erase 20=dz 63 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd109 (by decide +kernel) (eq.symm ▸ dp63)
theorem dd110 : Data (dz 110) (dt 110) (du 110) (dh 110) (da 110) := verifies_sound (by decide +kernel)
theorem dp110 : Good 3 (dz 110) := by
  have eq : (dz 110).erase 22=dz 51 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd110 (by decide +kernel) (eq.symm ▸ dp51)
theorem dd111 : Data (dz 111) (dt 111) (du 111) (dh 111) (da 111) := verifies_sound (by decide +kernel)
theorem dp111 : Good 3 (dz 111) := by
  have eq : (dz 111).erase 22=dz 56 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd111 (by decide +kernel) (eq.symm ▸ dp56)
theorem dd112 : Data (dz 112) (dt 112) (du 112) (dh 112) (da 112) := verifies_sound (by decide +kernel)
theorem dp112 : Good 3 (dz 112) := by
  have eq : (dz 112).erase 22=dz 59 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd112 (by decide +kernel) (eq.symm ▸ dp59)
theorem dd113 : Data (dz 113) (dt 113) (du 113) (dh 113) (da 113) := verifies_sound (by decide +kernel)
theorem dp113 : Good 3 (dz 113) := by
  have eq : (dz 113).erase 22=dz 60 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd113 (by decide +kernel) (eq.symm ▸ dp60)
theorem dd114 : Data (dz 114) (dt 114) (du 114) (dh 114) (da 114) := verifies_sound (by decide +kernel)
theorem dp114 : Good 3 (dz 114) := by
  have eq : (dz 114).erase 22=dz 62 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd114 (by decide +kernel) (eq.symm ▸ dp62)
theorem dd115 : Data (dz 115) (dt 115) (du 115) (dh 115) (da 115) := verifies_sound (by decide +kernel)
theorem dp115 : Good 3 (dz 115) := by
  have eq : (dz 115).erase 21=dz 68 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd115 (by decide +kernel) (eq.symm ▸ dp68)
theorem dd116 : Data (dz 116) (dt 116) (du 116) (dh 116) (da 116) := verifies_sound (by decide +kernel)
theorem dp116 : Good 3 (dz 116) := by
  have eq : (dz 116).erase 22=dz 63 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd116 (by decide +kernel) (eq.symm ▸ dp63)
theorem dd117 : Data (dz 117) (dt 117) (du 117) (dh 117) (da 117) := verifies_sound (by decide +kernel)
theorem dp117 : Good 3 (dz 117) := by
  have eq : (dz 117).erase 22=dz 64 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd117 (by decide +kernel) (eq.symm ▸ dp64)
theorem dd118 : Data (dz 118) (dt 118) (du 118) (dh 118) (da 118) := verifies_sound (by decide +kernel)
theorem dp118 : Good 3 (dz 118) := by
  have eq : (dz 118).erase 13=dz 71 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd118 (by decide +kernel) (eq.symm ▸ dp71)
theorem dd119 : Data (dz 119) (dt 119) (du 119) (dh 119) (da 119) := verifies_sound (by decide +kernel)
theorem dp119 : Good 3 (dz 119) := by
  have eq : (dz 119).erase 16=dz 71 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd119 (by decide +kernel) (eq.symm ▸ dp71)
theorem dd120 : Data (dz 120) (dt 120) (du 120) (dh 120) (da 120) := verifies_sound (by decide +kernel)
theorem dp120 : Good 3 (dz 120) := by
  have eq : (dz 120).erase 22=dz 65 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd120 (by decide +kernel) (eq.symm ▸ dp65)
theorem dd121 : Data (dz 121) (dt 121) (du 121) (dh 121) (da 121) := verifies_sound (by decide +kernel)
theorem dp121 : Good 3 (dz 121) := by
  have eq : (dz 121).erase 21=dz 69 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd121 (by decide +kernel) (eq.symm ▸ dp69)
theorem dd122 : Data (dz 122) (dt 122) (du 122) (dh 122) (da 122) := verifies_sound (by decide +kernel)
theorem dp122 : Good 3 (dz 122) := by
  have eq : (dz 122).erase 22=dz 67 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd122 (by decide +kernel) (eq.symm ▸ dp67)
theorem dd123 : Data (dz 123) (dt 123) (du 123) (dh 123) (da 123) := verifies_sound (by decide +kernel)
theorem dp123 : Good 3 (dz 123) := by
  have eq : (dz 123).erase 16=dz 72 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd123 (by decide +kernel) (eq.symm ▸ dp72)
theorem dd124 : Data (dz 124) (dt 124) (du 124) (dh 124) (da 124) := verifies_sound (by decide +kernel)
theorem dp124 : Good 3 (dz 124) := by
  have eq : (dz 124).erase 21=dz 70 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd124 (by decide +kernel) (eq.symm ▸ dp70)
theorem dd125 : Data (dz 125) (dt 125) (du 125) (dh 125) (da 125) := verifies_sound (by decide +kernel)
theorem dp125 : Good 3 (dz 125) := by
  have eq : (dz 125).erase 16=dz 73 := by decide +kernel
  exact .pivot _ _ _ _ _ 16 dd125 (by decide +kernel) (eq.symm ▸ dp73)
theorem dd126 : Data (dz 126) (dt 126) (du 126) (dh 126) (da 126) := verifies_sound (by decide +kernel)
theorem dp126 : Good 3 (dz 126) := by
  have eq : (dz 126).erase 13=dz 75 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd126 (by decide +kernel) (eq.symm ▸ dp75)
theorem dd127 : Data (dz 127) (dt 127) (du 127) (dh 127) (da 127) := verifies_sound (by decide +kernel)
theorem dp127 : Good 3 (dz 127) := by
  have eq : (dz 127).erase 13=dz 76 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd127 (by decide +kernel) (eq.symm ▸ dp76)
theorem dd128 : Data (dz 128) (dt 128) (du 128) (dh 128) (da 128) := verifies_sound (by decide +kernel)
theorem dp128 : Good 3 (dz 128) := by
  have eq : (dz 128).erase 21=dz 74 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd128 (by decide +kernel) (eq.symm ▸ dp74)
theorem dd129 : Data (dz 129) (dt 129) (du 129) (dh 129) (da 129) := verifies_sound (by decide +kernel)
theorem dp129 : Good 3 (dz 129) := by
  have eq : (dz 129).erase 23=dz 67 := by decide +kernel
  exact .pivot _ _ _ _ _ 23 dd129 (by decide +kernel) (eq.symm ▸ dp67)
theorem dd130 : Data (dz 130) (dt 130) (du 130) (dh 130) (da 130) := verifies_sound (by decide +kernel)
theorem dp130 : Good 3 (dz 130) := by
  have eq : (dz 130).erase 7=dz 77 := by decide +kernel
  exact .pivot _ _ _ _ _ 7 dd130 (by decide +kernel) (eq.symm ▸ dp77)
theorem dd131 : Data (dz 131) (dt 131) (du 131) (dh 131) (da 131) := verifies_sound (by decide +kernel)
theorem dp131 : Good 3 (dz 131) := by
  have eq : (dz 131).erase 11=dz 78 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 dd131 (by decide +kernel) (eq.symm ▸ dp78)
theorem dd132 : Data (dz 132) (dt 132) (du 132) (dh 132) (da 132) := verifies_sound (by decide +kernel)
theorem dp132 : Good 3 (dz 132) := by
  have eq : (dz 132).erase 8=dz 79 := by decide +kernel
  exact .pivot _ _ _ _ _ 8 dd132 (by decide +kernel) (eq.symm ▸ dp79)
theorem dd133 : Data (dz 133) (dt 133) (du 133) (dh 133) (da 133) := verifies_sound (by decide +kernel)
theorem dp133 : Good 3 (dz 133) := by
  have eq : (dz 133).erase 13=dz 97 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd133 (by decide +kernel) (eq.symm ▸ dp97)
theorem dd134 : Data (dz 134) (dt 134) (du 134) (dh 134) (da 134) := verifies_sound (by decide +kernel)
theorem dp134 : Good 3 (dz 134) := by
  have eq : (dz 134).erase 13=dz 100 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd134 (by decide +kernel) (eq.symm ▸ dp100)
theorem dd135 : Data (dz 135) (dt 135) (du 135) (dh 135) (da 135) := verifies_sound (by decide +kernel)
theorem dp135 : Good 3 (dz 135) := by
  have eq : (dz 135).erase 13=dz 101 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd135 (by decide +kernel) (eq.symm ▸ dp101)
theorem dd136 : Data (dz 136) (dt 136) (du 136) (dh 136) (da 136) := verifies_sound (by decide +kernel)
theorem dp136 : Good 3 (dz 136) := by
  have eq : (dz 136).erase 14=dz 102 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd136 (by decide +kernel) (eq.symm ▸ dp102)
theorem dd137 : Data (dz 137) (dt 137) (du 137) (dh 137) (da 137) := verifies_sound (by decide +kernel)
theorem dp137 : Good 3 (dz 137) := by
  have eq : (dz 137).erase 13=dz 103 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd137 (by decide +kernel) (eq.symm ▸ dp103)
theorem dd138 : Data (dz 138) (dt 138) (du 138) (dh 138) (da 138) := verifies_sound (by decide +kernel)
theorem dp138 : Good 3 (dz 138) := by
  have eq : (dz 138).erase 13=dz 107 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd138 (by decide +kernel) (eq.symm ▸ dp107)
theorem dd139 : Data (dz 139) (dt 139) (du 139) (dh 139) (da 139) := verifies_sound (by decide +kernel)
theorem dp139 : Good 3 (dz 139) := by
  have eq : (dz 139).erase 14=dz 108 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd139 (by decide +kernel) (eq.symm ▸ dp108)
theorem dd140 : Data (dz 140) (dt 140) (du 140) (dh 140) (da 140) := verifies_sound (by decide +kernel)
theorem dp140 : Good 3 (dz 140) := by
  have eq : (dz 140).erase 18=dz 105 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 dd140 (by decide +kernel) (eq.symm ▸ dp105)
theorem dd141 : Data (dz 141) (dt 141) (du 141) (dh 141) (da 141) := verifies_sound (by decide +kernel)
theorem dp141 : Good 3 (dz 141) := by
  have eq : (dz 141).erase 18=dz 106 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 dd141 (by decide +kernel) (eq.symm ▸ dp106)
theorem dd142 : Data (dz 142) (dt 142) (du 142) (dh 142) (da 142) := verifies_sound (by decide +kernel)
theorem dp142 : Good 3 (dz 142) := by
  have eq : (dz 142).erase 13=dz 109 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd142 (by decide +kernel) (eq.symm ▸ dp109)
theorem dd143 : Data (dz 143) (dt 143) (du 143) (dh 143) (da 143) := verifies_sound (by decide +kernel)
theorem dp143 : Good 3 (dz 143) := by
  have eq : (dz 143).erase 22=dz 93 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd143 (by decide +kernel) (eq.symm ▸ dp93)
theorem dd144 : Data (dz 144) (dt 144) (du 144) (dh 144) (da 144) := verifies_sound (by decide +kernel)
theorem dp144 : Good 3 (dz 144) := by
  have eq : (dz 144).erase 13=dz 111 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd144 (by decide +kernel) (eq.symm ▸ dp111)
theorem dd145 : Data (dz 145) (dt 145) (du 145) (dh 145) (da 145) := verifies_sound (by decide +kernel)
theorem dp145 : Good 3 (dz 145) := by
  have eq : (dz 145).erase 22=dz 98 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd145 (by decide +kernel) (eq.symm ▸ dp98)
theorem dd146 : Data (dz 146) (dt 146) (du 146) (dh 146) (da 146) := verifies_sound (by decide +kernel)
theorem dp146 : Good 3 (dz 146) := by
  have eq : (dz 146).erase 22=dz 99 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd146 (by decide +kernel) (eq.symm ▸ dp99)
theorem dd147 : Data (dz 147) (dt 147) (du 147) (dh 147) (da 147) := verifies_sound (by decide +kernel)
theorem dp147 : Good 3 (dz 147) := by
  have eq : (dz 147).erase 13=dz 112 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd147 (by decide +kernel) (eq.symm ▸ dp112)
theorem dd148 : Data (dz 148) (dt 148) (du 148) (dh 148) (da 148) := verifies_sound (by decide +kernel)
theorem dp148 : Good 3 (dz 148) := by
  have eq : (dz 148).erase 20=dz 110 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd148 (by decide +kernel) (eq.symm ▸ dp110)
theorem dd149 : Data (dz 149) (dt 149) (du 149) (dh 149) (da 149) := verifies_sound (by decide +kernel)
theorem dp149 : Good 3 (dz 149) := by
  have eq : (dz 149).erase 13=dz 113 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd149 (by decide +kernel) (eq.symm ▸ dp113)
theorem dd150 : Data (dz 150) (dt 150) (du 150) (dh 150) (da 150) := verifies_sound (by decide +kernel)
theorem dp150 : Good 3 (dz 150) := by
  have eq : (dz 150).erase 13=dz 114 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd150 (by decide +kernel) (eq.symm ▸ dp114)
theorem dd151 : Data (dz 151) (dt 151) (du 151) (dh 151) (da 151) := verifies_sound (by decide +kernel)
theorem dp151 : Good 3 (dz 151) := by
  have eq : (dz 151).erase 13=dz 116 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd151 (by decide +kernel) (eq.symm ▸ dp116)
theorem dd152 : Data (dz 152) (dt 152) (du 152) (dh 152) (da 152) := verifies_sound (by decide +kernel)
theorem dp152 : Good 3 (dz 152) := by
  have eq : (dz 152).erase 13=dz 117 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd152 (by decide +kernel) (eq.symm ▸ dp117)
theorem dd153 : Data (dz 153) (dt 153) (du 153) (dh 153) (da 153) := verifies_sound (by decide +kernel)
theorem dp153 : Good 3 (dz 153) := by
  have eq : (dz 153).erase 13=dz 119 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd153 (by decide +kernel) (eq.symm ▸ dp119)
theorem dd154 : Data (dz 154) (dt 154) (du 154) (dh 154) (da 154) := verifies_sound (by decide +kernel)
theorem dp154 : Good 3 (dz 154) := by
  have eq : (dz 154).erase 13=dz 120 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd154 (by decide +kernel) (eq.symm ▸ dp120)
theorem dd155 : Data (dz 155) (dt 155) (du 155) (dh 155) (da 155) := verifies_sound (by decide +kernel)
theorem dp155 : Good 3 (dz 155) := by
  have eq : (dz 155).erase 13=dz 121 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd155 (by decide +kernel) (eq.symm ▸ dp121)
theorem dd156 : Data (dz 156) (dt 156) (du 156) (dh 156) (da 156) := verifies_sound (by decide +kernel)
theorem dp156 : Good 3 (dz 156) := by
  have eq : (dz 156).erase 22=dz 104 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd156 (by decide +kernel) (eq.symm ▸ dp104)
theorem dd157 : Data (dz 157) (dt 157) (du 157) (dh 157) (da 157) := verifies_sound (by decide +kernel)
theorem dp157 : Good 3 (dz 157) := by
  have eq : (dz 157).erase 22=dz 105 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd157 (by decide +kernel) (eq.symm ▸ dp105)
theorem dd158 : Data (dz 158) (dt 158) (du 158) (dh 158) (da 158) := verifies_sound (by decide +kernel)
theorem dp158 : Good 3 (dz 158) := by
  have eq : (dz 158).erase 22=dz 106 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd158 (by decide +kernel) (eq.symm ▸ dp106)
theorem dd159 : Data (dz 159) (dt 159) (du 159) (dh 159) (da 159) := verifies_sound (by decide +kernel)
theorem dp159 : Good 3 (dz 159) := by
  have eq : (dz 159).erase 19=dz 118 := by decide +kernel
  exact .pivot _ _ _ _ _ 19 dd159 (by decide +kernel) (eq.symm ▸ dp118)
theorem dd160 : Data (dz 160) (dt 160) (du 160) (dh 160) (da 160) := verifies_sound (by decide +kernel)
theorem dp160 : Good 3 (dz 160) := by
  have eq : (dz 160).erase 14=dz 123 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd160 (by decide +kernel) (eq.symm ▸ dp123)
theorem dd161 : Data (dz 161) (dt 161) (du 161) (dh 161) (da 161) := verifies_sound (by decide +kernel)
theorem dp161 : Good 3 (dz 161) := by
  have eq : (dz 161).erase 18=dz 122 := by decide +kernel
  exact .pivot _ _ _ _ _ 18 dd161 (by decide +kernel) (eq.symm ▸ dp122)
theorem dd162 : Data (dz 162) (dt 162) (du 162) (dh 162) (da 162) := verifies_sound (by decide +kernel)
theorem dp162 : Good 3 (dz 162) := by
  have eq : (dz 162).erase 20=dz 115 := by decide +kernel
  exact .pivot _ _ _ _ _ 20 dd162 (by decide +kernel) (eq.symm ▸ dp115)
theorem dd163 : Data (dz 163) (dt 163) (du 163) (dh 163) (da 163) := verifies_sound (by decide +kernel)
theorem dp163 : Good 3 (dz 163) := by
  have eq : (dz 163).erase 13=dz 124 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd163 (by decide +kernel) (eq.symm ▸ dp124)
theorem dd164 : Data (dz 164) (dt 164) (du 164) (dh 164) (da 164) := verifies_sound (by decide +kernel)
theorem dp164 : Good 3 (dz 164) := by
  have eq : (dz 164).erase 14=dz 126 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd164 (by decide +kernel) (eq.symm ▸ dp126)
theorem dd165 : Data (dz 165) (dt 165) (du 165) (dh 165) (da 165) := verifies_sound (by decide +kernel)
theorem dp165 : Good 3 (dz 165) := by
  have eq : (dz 165).erase 14=dz 127 := by decide +kernel
  exact .pivot _ _ _ _ _ 14 dd165 (by decide +kernel) (eq.symm ▸ dp127)
theorem dd166 : Data (dz 166) (dt 166) (du 166) (dh 166) (da 166) := verifies_sound (by decide +kernel)
theorem dp166 : Good 3 (dz 166) := by
  have eq : (dz 166).erase 21=dz 125 := by decide +kernel
  exact .pivot _ _ _ _ _ 21 dd166 (by decide +kernel) (eq.symm ▸ dp125)
theorem dd167 : Data (dz 167) (dt 167) (du 167) (dh 167) (da 167) := verifies_sound (by decide +kernel)
theorem dp167 : Good 3 (dz 167) := by
  have eq : (dz 167).erase 13=dz 128 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd167 (by decide +kernel) (eq.symm ▸ dp128)
theorem dd168 : Data (dz 168) (dt 168) (du 168) (dh 168) (da 168) := verifies_sound (by decide +kernel)
theorem dp168 : Good 3 (dz 168) := by
  have eq : (dz 168).erase 15=dz 129 := by decide +kernel
  exact .pivot _ _ _ _ _ 15 dd168 (by decide +kernel) (eq.symm ▸ dp129)
theorem dd169 : Data (dz 169) (dt 169) (du 169) (dh 169) (da 169) := verifies_sound (by decide +kernel)
theorem dp169 : Good 3 (dz 169) := by
  have eq : (dz 169).erase 11=dz 130 := by decide +kernel
  exact .pivot _ _ _ _ _ 11 dd169 (by decide +kernel) (eq.symm ▸ dp130)
theorem dd170 : Data (dz 170) (dt 170) (du 170) (dh 170) (da 170) := verifies_sound (by decide +kernel)
theorem dp170 : Good 3 (dz 170) := by
  have eq : (dz 170).erase 22=dz 166 := by decide +kernel
  exact .pivot _ _ _ _ _ 22 dd170 (by decide +kernel) (eq.symm ▸ dp166)
theorem dd171 : Data (dz 171) (dt 171) (du 171) (dh 171) (da 171) := verifies_sound (by decide +kernel)
theorem dp171 : Good 3 (dz 171) := by
  have eq : (dz 171).erase 12=dz 169 := by decide +kernel
  exact .pivot _ _ _ _ _ 12 dd171 (by decide +kernel) (eq.symm ▸ dp169)
theorem dd172 : Data (dz 172) (dt 172) (du 172) (dh 172) (da 172) := verifies_sound (by decide +kernel)
theorem dp172 : Good 3 (dz 172) := by
  have eq : (dz 172).erase 13=dz 170 := by decide +kernel
  exact .pivot _ _ _ _ _ 13 dd172 (by decide +kernel) (eq.symm ▸ dp170)

def Strong (Z : Finset V) := ∀ D : Dag, StrictLive 26 D → sem_Comp 26 G D → ineligSet 26 D ⊆ Z → 48≤D.length
theorem goodStrong {Z : Finset V} (c : Good 3 Z) : Strong Z := by
  intro D h sem bound
  have hh := panelBound regular h sem bound c
  omega
theorem transport {Z Y : Finset V} (e : V ≃ V) (adj : ∀u v,G (e u) (e v) ↔ G u v)
    (sub : ∀i∈Z,e i∈Y) (gold : Strong Y) : Strong Z := by
  intro D h hc subset
  have hrel : sem_Comp 26 G (relabel e D) := by
    intro x
    rw [relabel_out e h.1 h.2.2 x, hc]
    unfold sem_Edge
    constructor
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e u,e v,(adj u v).mpr huv,hu,hv⟩
    · rintro ⟨u,v,huv,hu,hv⟩
      exact ⟨e.symm u,e.symm v,(adj _ _).mp (by simpa using huv),by simpa using hu,by simpa using hv⟩
  have inc : ineligSet 26 (relabel e D) ⊆ Y := by
    rw [relabel_ineligSet e h.1]
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact sub i (subset hi)
  simpa only [relabel_length] using gold _ (relabel_strictLive e h) hrel inc
theorem fromChildren {Z : Finset V} (pure : Z ⊆ Exposure17245.lines) (large : 9≤Z.card)
    (children : ∀v∈Z,Strong (Z.erase v)) : Strong Z := by
  classical
  intro D live sem incl
  by_cases most : 9≤(ineligSet 26 D).card
  · have ind : ∀i∈ineligSet 26 D,∀j∈ineligSet 26 D,¬G i j := by
      intro i hi j hj ed
      exact (sem_elig_cover regular live sem ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
    have weak := core regular live sem ind
    have key := Exposure17245.pure_charge regular live sem (incl.trans pure)
    omega
  · obtain ⟨v,hz,hm⟩ : ∃v∈Z,v∉ineligSet 26 D := by
      by_contra! subset
      have c := Finset.card_le_card (show Z ⊆ ineligSet 26 D from subset)
      omega
    exact children v hz D live sem (fun i hi => Finset.mem_erase.mpr ⟨fun eq => hm (eq ▸ hi),incl hi⟩)
def largeRows : Array Nat := #[0x1fe000,0x2fe000,0x37e000,0x3be000,0x3de000,0x3ee000,0x3f6000,0x3fa000,0x4fe000,0x57e000,0x5be000,0x5de000,0x5f6000,0x5fa000,0x67e000,0x6be000,0x6fa000,0x73e000,0x75e000,0x76e000,0x77a000,0x79e000,0x7ae000,0x7b6000,0x7ce000,0x7d6000,0x7e6000,0x7ea000,0x7f2000,0xabe000,0xade000,0xafa000,0xbae000,0x3fe000,0x5fe000,0x6fe000,0x77e000,0x7be000,0x7de000,0x7ee000,0x7f6000,0x7fa000,0x9fe000,0xafe000,0xbbe000,0xbde000,0xbee000,0xbfa000,0xd7e000,0xebe000,0xefa000,0xf3e000,0xf5e000,0xfd6000,0x7fe000,0xbfe000,0xdfe000,0xefe000,0xf7e000,0xfbe000,0xfde000,0xff6000,0x17be000,0x17de000,0xffe000,0x17fe000,0x1ffe000,0x3ffe000]
def bulk (i : Nat) := members ((largeRows[i]?).getD 0)
theorem b0 : Strong (bulk 0) := by
  rw [show bulk 0=dz 134 by decide +kernel]
  exact goodStrong dp134
theorem b1 : Strong (bulk 1) := by
  rw [show bulk 1=dz 136 by decide +kernel]
  exact goodStrong dp136
theorem b2 : Strong (bulk 2) := by
  rw [show bulk 2=dz 137 by decide +kernel]
  exact goodStrong dp137
theorem b3 : Strong (bulk 3) := by
  rw [show bulk 3=dz 138 by decide +kernel]
  exact goodStrong dp138
theorem b4 : Strong (bulk 4) := by
  rw [show bulk 4=dz 139 by decide +kernel]
  exact goodStrong dp139
theorem b5 : Strong (bulk 5) := by
  rw [show bulk 5=dz 140 by decide +kernel]
  exact goodStrong dp140
theorem b6 : Strong (bulk 6) := by
  rw [show bulk 6=dz 141 by decide +kernel]
  exact goodStrong dp141
theorem b7 : Strong (bulk 7) := by
  rw [show bulk 7=dz 142 by decide +kernel]
  exact goodStrong dp142
theorem b8 : Strong (bulk 8) := by
  rw [show bulk 8=dz 143 by decide +kernel]
  exact goodStrong dp143
theorem b9 : Strong (bulk 9) := by
  rw [show bulk 9=dz 144 by decide +kernel]
  exact goodStrong dp144
theorem b10 : Strong (bulk 10) := by
  rw [show bulk 10=dz 145 by decide +kernel]
  exact goodStrong dp145
theorem b11 : Strong (bulk 11) := by
  rw [show bulk 11=dz 146 by decide +kernel]
  exact goodStrong dp146
theorem b12 : Strong (bulk 12) := by
  rw [show bulk 12=dz 147 by decide +kernel]
  exact goodStrong dp147
theorem b13 : Strong (bulk 13) := by
  rw [show bulk 13=dz 148 by decide +kernel]
  exact goodStrong dp148
theorem b14 : Strong (bulk 14) := by
  rw [show bulk 14=dz 149 by decide +kernel]
  exact goodStrong dp149
theorem b15 : Strong (bulk 15) := by
  rw [show bulk 15=dz 150 by decide +kernel]
  exact goodStrong dp150
theorem b16 : Strong (bulk 16) := by
  rw [show bulk 16=dz 151 by decide +kernel]
  exact goodStrong dp151
theorem b17 : Strong (bulk 17) := by
  rw [show bulk 17=dz 152 by decide +kernel]
  exact goodStrong dp152
theorem b18 : Strong (bulk 18) := by
  rw [show bulk 18=dz 153 by decide +kernel]
  exact goodStrong dp153
theorem b19 : Strong (bulk 19) := by
  rw [show bulk 19=dz 154 by decide +kernel]
  exact goodStrong dp154
theorem b20 : Strong (bulk 20) := by
  rw [show bulk 20=dz 155 by decide +kernel]
  exact goodStrong dp155
theorem b21 : Strong (bulk 21) := by
  rw [show bulk 21=dz 156 by decide +kernel]
  exact goodStrong dp156
theorem b22 : Strong (bulk 22) := by
  rw [show bulk 22=dz 157 by decide +kernel]
  exact goodStrong dp157
theorem b23 : Strong (bulk 23) := by
  rw [show bulk 23=dz 158 by decide +kernel]
  exact goodStrong dp158
theorem b24 : Strong (bulk 24) := by
  rw [show bulk 24=dz 159 by decide +kernel]
  exact goodStrong dp159
theorem b25 : Strong (bulk 25) := by
  rw [show bulk 25=dz 160 by decide +kernel]
  exact goodStrong dp160
theorem b26 : Strong (bulk 26) := by
  rw [show bulk 26=dz 161 by decide +kernel]
  exact goodStrong dp161
theorem b27 : Strong (bulk 27) := by
  rw [show bulk 27=dz 162 by decide +kernel]
  exact goodStrong dp162
theorem b28 : Strong (bulk 28) := by
  rw [show bulk 28=dz 163 by decide +kernel]
  exact goodStrong dp163
theorem b29 : Strong (bulk 29) := by
  rw [show bulk 29=dz 164 by decide +kernel]
  exact goodStrong dp164
theorem b30 : Strong (bulk 30) := by
  rw [show bulk 30=dz 165 by decide +kernel]
  exact goodStrong dp165
theorem b31 : Strong (bulk 31) := by
  rw [show bulk 31=dz 167 by decide +kernel]
  exact goodStrong dp167
theorem b32 : Strong (bulk 32) := by
  rw [show bulk 32=dz 168 by decide +kernel]
  exact goodStrong dp168
theorem b33 : Strong (bulk 33) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 33) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b0
    change ∀i∈(bulk 33).erase 13, action 1 i∈bulk 0
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b7
    change ∀i∈(bulk 33).erase 14, action 0 i∈bulk 7
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b6
    change ∀i∈(bulk 33).erase 15, action 0 i∈bulk 6
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b5
    change ∀i∈(bulk 33).erase 16, action 0 i∈bulk 5
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b4
    change ∀i∈(bulk 33).erase 17, action 0 i∈bulk 4
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b3
    change ∀i∈(bulk 33).erase 18, action 0 i∈bulk 3
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b2
    change ∀i∈(bulk 33).erase 19, action 0 i∈bulk 2
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b1
    change ∀i∈(bulk 33).erase 20, action 0 i∈bulk 1
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b0
    change ∀i∈(bulk 33).erase 21, action 0 i∈bulk 0
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 33) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 33) hv)
theorem b34 : Strong (bulk 34) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 34) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b1
    change ∀i∈(bulk 34).erase 13, action 1 i∈bulk 1
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b13
    change ∀i∈(bulk 34).erase 14, action 0 i∈bulk 13
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b12
    change ∀i∈(bulk 34).erase 15, action 0 i∈bulk 12
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b10
    change ∀i∈(bulk 34).erase 16, action 25 i∈bulk 10
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b11
    change ∀i∈(bulk 34).erase 17, action 0 i∈bulk 11
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b10
    change ∀i∈(bulk 34).erase 18, action 0 i∈bulk 10
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b9
    change ∀i∈(bulk 34).erase 19, action 0 i∈bulk 9
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b8
    change ∀i∈(bulk 34).erase 20, action 0 i∈bulk 8
    decide +kernel
  · exact False.elim ((by decide +kernel : (21:V)∉bulk 34) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b0
    change ∀i∈(bulk 34).erase 22, action 0 i∈bulk 0
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 34) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 34) hv)
theorem b35 : Strong (bulk 35) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 35) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b2
    change ∀i∈(bulk 35).erase 13, action 1 i∈bulk 2
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b16
    change ∀i∈(bulk 35).erase 14, action 0 i∈bulk 16
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b13
    change ∀i∈(bulk 35).erase 15, action 22 i∈bulk 13
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b2
    change ∀i∈(bulk 35).erase 16, action 24 i∈bulk 2
    decide +kernel
  · apply transport (perm 26) (actionValid 26).adj _ b11
    change ∀i∈(bulk 35).erase 17, action 26 i∈bulk 11
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b15
    change ∀i∈(bulk 35).erase 18, action 0 i∈bulk 15
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b14
    change ∀i∈(bulk 35).erase 19, action 0 i∈bulk 14
    decide +kernel
  · exact False.elim ((by decide +kernel : (20:V)∉bulk 35) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b8
    change ∀i∈(bulk 35).erase 21, action 0 i∈bulk 8
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b1
    change ∀i∈(bulk 35).erase 22, action 0 i∈bulk 1
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 35) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 35) hv)
theorem b36 : Strong (bulk 36) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 36) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b3
    change ∀i∈(bulk 36).erase 13, action 1 i∈bulk 3
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b20
    change ∀i∈(bulk 36).erase 14, action 0 i∈bulk 20
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b6
    change ∀i∈(bulk 36).erase 15, action 21 i∈bulk 6
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b19
    change ∀i∈(bulk 36).erase 16, action 0 i∈bulk 19
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b18
    change ∀i∈(bulk 36).erase 17, action 0 i∈bulk 18
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b17
    change ∀i∈(bulk 36).erase 18, action 0 i∈bulk 17
    decide +kernel
  · exact False.elim ((by decide +kernel : (19:V)∉bulk 36) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b14
    change ∀i∈(bulk 36).erase 20, action 0 i∈bulk 14
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b9
    change ∀i∈(bulk 36).erase 21, action 0 i∈bulk 9
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b2
    change ∀i∈(bulk 36).erase 22, action 0 i∈bulk 2
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 36) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 36) hv)
theorem b37 : Strong (bulk 37) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 37) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b4
    change ∀i∈(bulk 37).erase 13, action 1 i∈bulk 4
    decide +kernel
  · apply transport (perm 18) (actionValid 18).adj _ b23
    change ∀i∈(bulk 37).erase 14, action 18 i∈bulk 23
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b23
    change ∀i∈(bulk 37).erase 15, action 0 i∈bulk 23
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b22
    change ∀i∈(bulk 37).erase 16, action 0 i∈bulk 22
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b21
    change ∀i∈(bulk 37).erase 17, action 0 i∈bulk 21
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 37) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b17
    change ∀i∈(bulk 37).erase 19, action 0 i∈bulk 17
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b15
    change ∀i∈(bulk 37).erase 20, action 0 i∈bulk 15
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b10
    change ∀i∈(bulk 37).erase 21, action 0 i∈bulk 10
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b3
    change ∀i∈(bulk 37).erase 22, action 0 i∈bulk 3
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 37) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 37) hv)
theorem b38 : Strong (bulk 38) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 38) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b5
    change ∀i∈(bulk 38).erase 13, action 1 i∈bulk 5
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b20
    change ∀i∈(bulk 38).erase 14, action 37 i∈bulk 20
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b25
    change ∀i∈(bulk 38).erase 15, action 0 i∈bulk 25
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b24
    change ∀i∈(bulk 38).erase 16, action 0 i∈bulk 24
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 38) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b21
    change ∀i∈(bulk 38).erase 18, action 0 i∈bulk 21
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b18
    change ∀i∈(bulk 38).erase 19, action 0 i∈bulk 18
    decide +kernel
  · apply transport (perm 26) (actionValid 26).adj _ b11
    change ∀i∈(bulk 38).erase 20, action 26 i∈bulk 11
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b11
    change ∀i∈(bulk 38).erase 21, action 0 i∈bulk 11
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b4
    change ∀i∈(bulk 38).erase 22, action 0 i∈bulk 4
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 38) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 38) hv)
theorem b39 : Strong (bulk 39) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 39) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b6
    change ∀i∈(bulk 39).erase 13, action 1 i∈bulk 6
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b27
    change ∀i∈(bulk 39).erase 14, action 0 i∈bulk 27
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b26
    change ∀i∈(bulk 39).erase 15, action 0 i∈bulk 26
    decide +kernel
  · exact False.elim ((by decide +kernel : (16:V)∉bulk 39) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b24
    change ∀i∈(bulk 39).erase 17, action 0 i∈bulk 24
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b22
    change ∀i∈(bulk 39).erase 18, action 0 i∈bulk 22
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b19
    change ∀i∈(bulk 39).erase 19, action 0 i∈bulk 19
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b2
    change ∀i∈(bulk 39).erase 20, action 24 i∈bulk 2
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b10
    change ∀i∈(bulk 39).erase 21, action 25 i∈bulk 10
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b5
    change ∀i∈(bulk 39).erase 22, action 0 i∈bulk 5
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 39) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 39) hv)
theorem b40 : Strong (bulk 40) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 40) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b7
    change ∀i∈(bulk 40).erase 13, action 1 i∈bulk 7
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b28
    change ∀i∈(bulk 40).erase 14, action 0 i∈bulk 28
    decide +kernel
  · exact False.elim ((by decide +kernel : (15:V)∉bulk 40) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b26
    change ∀i∈(bulk 40).erase 16, action 0 i∈bulk 26
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b25
    change ∀i∈(bulk 40).erase 17, action 0 i∈bulk 25
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b23
    change ∀i∈(bulk 40).erase 18, action 0 i∈bulk 23
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b6
    change ∀i∈(bulk 40).erase 19, action 21 i∈bulk 6
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b13
    change ∀i∈(bulk 40).erase 20, action 22 i∈bulk 13
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b12
    change ∀i∈(bulk 40).erase 21, action 0 i∈bulk 12
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b6
    change ∀i∈(bulk 40).erase 22, action 0 i∈bulk 6
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 40) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 40) hv)
theorem b41 : Strong (bulk 41) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 41) hv)
  · apply transport (perm 2) (actionValid 2).adj _ b0
    change ∀i∈(bulk 41).erase 13, action 2 i∈bulk 0
    decide +kernel
  · exact False.elim ((by decide +kernel : (14:V)∉bulk 41) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b28
    change ∀i∈(bulk 41).erase 15, action 0 i∈bulk 28
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b27
    change ∀i∈(bulk 41).erase 16, action 0 i∈bulk 27
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b20
    change ∀i∈(bulk 41).erase 17, action 37 i∈bulk 20
    decide +kernel
  · apply transport (perm 18) (actionValid 18).adj _ b23
    change ∀i∈(bulk 41).erase 18, action 18 i∈bulk 23
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b20
    change ∀i∈(bulk 41).erase 19, action 0 i∈bulk 20
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b16
    change ∀i∈(bulk 41).erase 20, action 0 i∈bulk 16
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b13
    change ∀i∈(bulk 41).erase 21, action 0 i∈bulk 13
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b7
    change ∀i∈(bulk 41).erase 22, action 0 i∈bulk 7
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 41) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 41) hv)
theorem b42 : Strong (bulk 42) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 42) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b8
    change ∀i∈(bulk 42).erase 13, action 1 i∈bulk 8
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b14
    change ∀i∈(bulk 42).erase 14, action 36 i∈bulk 14
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b28
    change ∀i∈(bulk 42).erase 15, action 32 i∈bulk 28
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b12
    change ∀i∈(bulk 42).erase 16, action 25 i∈bulk 12
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b16
    change ∀i∈(bulk 42).erase 17, action 13 i∈bulk 16
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b8
    change ∀i∈(bulk 42).erase 18, action 35 i∈bulk 8
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b26
    change ∀i∈(bulk 42).erase 19, action 31 i∈bulk 26
    decide +kernel
  · apply transport (perm 10) (actionValid 10).adj _ b28
    change ∀i∈(bulk 42).erase 20, action 10 i∈bulk 28
    decide +kernel
  · exact False.elim ((by decide +kernel : (21:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 42) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b0
    change ∀i∈(bulk 42).erase 23, action 0 i∈bulk 0
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 42) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 42) hv)
theorem b43 : Strong (bulk 43) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 43) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b9
    change ∀i∈(bulk 43).erase 13, action 1 i∈bulk 9
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b31
    change ∀i∈(bulk 43).erase 14, action 0 i∈bulk 31
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b23
    change ∀i∈(bulk 43).erase 15, action 32 i∈bulk 23
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b5
    change ∀i∈(bulk 43).erase 16, action 24 i∈bulk 5
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b30
    change ∀i∈(bulk 43).erase 17, action 0 i∈bulk 30
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b29
    change ∀i∈(bulk 43).erase 18, action 0 i∈bulk 29
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b19
    change ∀i∈(bulk 43).erase 19, action 31 i∈bulk 19
    decide +kernel
  · exact False.elim ((by decide +kernel : (20:V)∉bulk 43) hv)
  · apply transport (perm 10) (actionValid 10).adj _ b28
    change ∀i∈(bulk 43).erase 21, action 10 i∈bulk 28
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 43) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b1
    change ∀i∈(bulk 43).erase 23, action 0 i∈bulk 1
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 43) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 43) hv)
theorem b44 : Strong (bulk 44) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 44) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b11
    change ∀i∈(bulk 44).erase 13, action 1 i∈bulk 11
    decide +kernel
  · apply transport (perm 17) (actionValid 17).adj _ b19
    change ∀i∈(bulk 44).erase 14, action 17 i∈bulk 19
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b7
    change ∀i∈(bulk 44).erase 15, action 33 i∈bulk 7
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b32
    change ∀i∈(bulk 44).erase 16, action 0 i∈bulk 32
    decide +kernel
  · apply transport (perm 16) (actionValid 16).adj _ b30
    change ∀i∈(bulk 44).erase 17, action 16 i∈bulk 30
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 44) hv)
  · apply transport (perm 31) (actionValid 31).adj _ b27
    change ∀i∈(bulk 44).erase 19, action 31 i∈bulk 27
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b29
    change ∀i∈(bulk 44).erase 20, action 0 i∈bulk 29
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b8
    change ∀i∈(bulk 44).erase 21, action 35 i∈bulk 8
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 44) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b3
    change ∀i∈(bulk 44).erase 23, action 0 i∈bulk 3
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 44) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 44) hv)
theorem b45 : Strong (bulk 45) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 45) hv)
  · apply transport (perm 15) (actionValid 15).adj _ b10
    change ∀i∈(bulk 45).erase 13, action 15 i∈bulk 10
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b17
    change ∀i∈(bulk 45).erase 14, action 37 i∈bulk 17
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b25
    change ∀i∈(bulk 45).erase 15, action 32 i∈bulk 25
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b32
    change ∀i∈(bulk 45).erase 16, action 31 i∈bulk 32
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 45) hv)
  · apply transport (perm 16) (actionValid 16).adj _ b30
    change ∀i∈(bulk 45).erase 18, action 16 i∈bulk 30
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b22
    change ∀i∈(bulk 45).erase 19, action 31 i∈bulk 22
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b30
    change ∀i∈(bulk 45).erase 20, action 0 i∈bulk 30
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b16
    change ∀i∈(bulk 45).erase 21, action 13 i∈bulk 16
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 45) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b4
    change ∀i∈(bulk 45).erase 23, action 0 i∈bulk 4
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 45) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 45) hv)
theorem b46 : Strong (bulk 46) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 46) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b12
    change ∀i∈(bulk 46).erase 13, action 1 i∈bulk 12
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b32
    change ∀i∈(bulk 46).erase 14, action 24 i∈bulk 32
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b12
    change ∀i∈(bulk 46).erase 15, action 32 i∈bulk 12
    decide +kernel
  · exact False.elim ((by decide +kernel : (16:V)∉bulk 46) hv)
  · apply transport (perm 31) (actionValid 31).adj _ b32
    change ∀i∈(bulk 46).erase 17, action 31 i∈bulk 32
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b32
    change ∀i∈(bulk 46).erase 18, action 0 i∈bulk 32
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b5
    change ∀i∈(bulk 46).erase 19, action 31 i∈bulk 5
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b5
    change ∀i∈(bulk 46).erase 20, action 24 i∈bulk 5
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b12
    change ∀i∈(bulk 46).erase 21, action 25 i∈bulk 12
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 46) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b5
    change ∀i∈(bulk 46).erase 23, action 0 i∈bulk 5
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 46) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 46) hv)
theorem b47 : Strong (bulk 47) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 47) hv)
  · apply transport (perm 2) (actionValid 2).adj _ b1
    change ∀i∈(bulk 47).erase 13, action 2 i∈bulk 1
    decide +kernel
  · exact False.elim ((by decide +kernel : (14:V)∉bulk 47) hv)
  · apply transport (perm 32) (actionValid 32).adj _ b26
    change ∀i∈(bulk 47).erase 15, action 32 i∈bulk 26
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b32
    change ∀i∈(bulk 47).erase 16, action 24 i∈bulk 32
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b17
    change ∀i∈(bulk 47).erase 17, action 37 i∈bulk 17
    decide +kernel
  · apply transport (perm 17) (actionValid 17).adj _ b19
    change ∀i∈(bulk 47).erase 18, action 17 i∈bulk 19
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b24
    change ∀i∈(bulk 47).erase 19, action 31 i∈bulk 24
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b31
    change ∀i∈(bulk 47).erase 20, action 0 i∈bulk 31
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b14
    change ∀i∈(bulk 47).erase 21, action 36 i∈bulk 14
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 47) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b7
    change ∀i∈(bulk 47).erase 23, action 0 i∈bulk 7
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 47) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 47) hv)
theorem b48 : Strong (bulk 48) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 48) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b15
    change ∀i∈(bulk 48).erase 13, action 1 i∈bulk 15
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b15
    change ∀i∈(bulk 48).erase 14, action 36 i∈bulk 15
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b26
    change ∀i∈(bulk 48).erase 15, action 21 i∈bulk 26
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b9
    change ∀i∈(bulk 48).erase 16, action 25 i∈bulk 9
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b15
    change ∀i∈(bulk 48).erase 17, action 13 i∈bulk 15
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b9
    change ∀i∈(bulk 48).erase 18, action 35 i∈bulk 9
    decide +kernel
  · exact False.elim ((by decide +kernel : (19:V)∉bulk 48) hv)
  · apply transport (perm 9) (actionValid 9).adj _ b26
    change ∀i∈(bulk 48).erase 20, action 9 i∈bulk 26
    decide +kernel
  · exact False.elim ((by decide +kernel : (21:V)∉bulk 48) hv)
  · apply transport (perm 31) (actionValid 31).adj _ b26
    change ∀i∈(bulk 48).erase 22, action 31 i∈bulk 26
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b9
    change ∀i∈(bulk 48).erase 23, action 0 i∈bulk 9
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 48) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 48) hv)
theorem b49 : Strong (bulk 49) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 49) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b18
    change ∀i∈(bulk 49).erase 13, action 1 i∈bulk 18
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b31
    change ∀i∈(bulk 49).erase 14, action 36 i∈bulk 31
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b20
    change ∀i∈(bulk 49).erase 15, action 22 i∈bulk 20
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b4
    change ∀i∈(bulk 49).erase 16, action 24 i∈bulk 4
    decide +kernel
  · apply transport (perm 38) (actionValid 38).adj _ b29
    change ∀i∈(bulk 49).erase 17, action 38 i∈bulk 29
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 49) hv)
  · apply transport (perm 8) (actionValid 8).adj _ b24
    change ∀i∈(bulk 49).erase 19, action 8 i∈bulk 24
    decide +kernel
  · exact False.elim ((by decide +kernel : (20:V)∉bulk 49) hv)
  · apply transport (perm 35) (actionValid 35).adj _ b12
    change ∀i∈(bulk 49).erase 21, action 35 i∈bulk 12
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b29
    change ∀i∈(bulk 49).erase 22, action 0 i∈bulk 29
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b15
    change ∀i∈(bulk 49).erase 23, action 0 i∈bulk 15
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 49) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 49) hv)
theorem b50 : Strong (bulk 50) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 50) hv)
  · apply transport (perm 2) (actionValid 2).adj _ b3
    change ∀i∈(bulk 50).erase 13, action 2 i∈bulk 3
    decide +kernel
  · exact False.elim ((by decide +kernel : (14:V)∉bulk 50) hv)
  · apply transport (perm 22) (actionValid 22).adj _ b16
    change ∀i∈(bulk 50).erase 15, action 22 i∈bulk 16
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b3
    change ∀i∈(bulk 50).erase 16, action 24 i∈bulk 3
    decide +kernel
  · apply transport (perm 38) (actionValid 38).adj _ b3
    change ∀i∈(bulk 50).erase 17, action 38 i∈bulk 3
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b31
    change ∀i∈(bulk 50).erase 18, action 36 i∈bulk 31
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b31
    change ∀i∈(bulk 50).erase 19, action 22 i∈bulk 31
    decide +kernel
  · exact False.elim ((by decide +kernel : (20:V)∉bulk 50) hv)
  · apply transport (perm 36) (actionValid 36).adj _ b16
    change ∀i∈(bulk 50).erase 21, action 36 i∈bulk 16
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b31
    change ∀i∈(bulk 50).erase 22, action 0 i∈bulk 31
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b16
    change ∀i∈(bulk 50).erase 23, action 0 i∈bulk 16
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 50) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 50) hv)
theorem b51 : Strong (bulk 51) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 51) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b21
    change ∀i∈(bulk 51).erase 13, action 1 i∈bulk 21
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b29
    change ∀i∈(bulk 51).erase 14, action 36 i∈bulk 29
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b13
    change ∀i∈(bulk 51).erase 15, action 33 i∈bulk 13
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b30
    change ∀i∈(bulk 51).erase 16, action 24 i∈bulk 30
    decide +kernel
  · apply transport (perm 7) (actionValid 7).adj _ b21
    change ∀i∈(bulk 51).erase 17, action 7 i∈bulk 21
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (19:V)∉bulk 51) hv)
  · apply transport (perm 8) (actionValid 8).adj _ b24
    change ∀i∈(bulk 51).erase 20, action 8 i∈bulk 24
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b9
    change ∀i∈(bulk 51).erase 21, action 35 i∈bulk 9
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b27
    change ∀i∈(bulk 51).erase 22, action 31 i∈bulk 27
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b17
    change ∀i∈(bulk 51).erase 23, action 0 i∈bulk 17
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 51) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 51) hv)
theorem b52 : Strong (bulk 52) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 52) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b22
    change ∀i∈(bulk 52).erase 13, action 1 i∈bulk 22
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b18
    change ∀i∈(bulk 52).erase 14, action 37 i∈bulk 18
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b25
    change ∀i∈(bulk 52).erase 15, action 21 i∈bulk 25
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b31
    change ∀i∈(bulk 52).erase 16, action 24 i∈bulk 31
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 52) hv)
  · apply transport (perm 7) (actionValid 7).adj _ b21
    change ∀i∈(bulk 52).erase 18, action 7 i∈bulk 21
    decide +kernel
  · exact False.elim ((by decide +kernel : (19:V)∉bulk 52) hv)
  · apply transport (perm 38) (actionValid 38).adj _ b32
    change ∀i∈(bulk 52).erase 20, action 38 i∈bulk 32
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b15
    change ∀i∈(bulk 52).erase 21, action 13 i∈bulk 15
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b22
    change ∀i∈(bulk 52).erase 22, action 31 i∈bulk 22
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b18
    change ∀i∈(bulk 52).erase 23, action 0 i∈bulk 18
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 52) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 52) hv)
theorem b53 : Strong (bulk 53) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 53) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b27
    change ∀i∈(bulk 53).erase 13, action 1 i∈bulk 27
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b14
    change ∀i∈(bulk 53).erase 14, action 37 i∈bulk 14
    decide +kernel
  · exact False.elim ((by decide +kernel : (15:V)∉bulk 53) hv)
  · apply transport (perm 5) (actionValid 5).adj _ b14
    change ∀i∈(bulk 53).erase 16, action 5 i∈bulk 14
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 53) hv)
  · apply transport (perm 33) (actionValid 33).adj _ b27
    change ∀i∈(bulk 53).erase 18, action 33 i∈bulk 27
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b25
    change ∀i∈(bulk 53).erase 19, action 21 i∈bulk 25
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b27
    change ∀i∈(bulk 53).erase 20, action 22 i∈bulk 27
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b14
    change ∀i∈(bulk 53).erase 21, action 13 i∈bulk 14
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b25
    change ∀i∈(bulk 53).erase 22, action 32 i∈bulk 25
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b25
    change ∀i∈(bulk 53).erase 23, action 0 i∈bulk 25
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 53) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 53) hv)
theorem b54 : Strong (bulk 54) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 54) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b33
    change ∀i∈(bulk 54).erase 13, action 1 i∈bulk 33
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b41
    change ∀i∈(bulk 54).erase 14, action 0 i∈bulk 41
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b40
    change ∀i∈(bulk 54).erase 15, action 0 i∈bulk 40
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b39
    change ∀i∈(bulk 54).erase 16, action 0 i∈bulk 39
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b38
    change ∀i∈(bulk 54).erase 17, action 0 i∈bulk 38
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b37
    change ∀i∈(bulk 54).erase 18, action 0 i∈bulk 37
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b36
    change ∀i∈(bulk 54).erase 19, action 0 i∈bulk 36
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b35
    change ∀i∈(bulk 54).erase 20, action 0 i∈bulk 35
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b34
    change ∀i∈(bulk 54).erase 21, action 0 i∈bulk 34
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b33
    change ∀i∈(bulk 54).erase 22, action 0 i∈bulk 33
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 54) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 54) hv)
theorem b55 : Strong (bulk 55) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 55) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b34
    change ∀i∈(bulk 55).erase 13, action 1 i∈bulk 34
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b47
    change ∀i∈(bulk 55).erase 14, action 0 i∈bulk 47
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b40
    change ∀i∈(bulk 55).erase 15, action 32 i∈bulk 40
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b46
    change ∀i∈(bulk 55).erase 16, action 0 i∈bulk 46
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b45
    change ∀i∈(bulk 55).erase 17, action 0 i∈bulk 45
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b44
    change ∀i∈(bulk 55).erase 18, action 0 i∈bulk 44
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b39
    change ∀i∈(bulk 55).erase 19, action 31 i∈bulk 39
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b43
    change ∀i∈(bulk 55).erase 20, action 0 i∈bulk 43
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b42
    change ∀i∈(bulk 55).erase 21, action 0 i∈bulk 42
    decide +kernel
  · exact False.elim ((by decide +kernel : (22:V)∉bulk 55) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b33
    change ∀i∈(bulk 55).erase 23, action 0 i∈bulk 33
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 55) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 55) hv)
theorem b56 : Strong (bulk 56) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 56) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b35
    change ∀i∈(bulk 56).erase 13, action 1 i∈bulk 35
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b35
    change ∀i∈(bulk 56).erase 14, action 36 i∈bulk 35
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b42
    change ∀i∈(bulk 56).erase 15, action 35 i∈bulk 42
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b34
    change ∀i∈(bulk 56).erase 16, action 25 i∈bulk 34
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b35
    change ∀i∈(bulk 56).erase 17, action 13 i∈bulk 35
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b34
    change ∀i∈(bulk 56).erase 18, action 35 i∈bulk 34
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b48
    change ∀i∈(bulk 56).erase 19, action 0 i∈bulk 48
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b42
    change ∀i∈(bulk 56).erase 20, action 25 i∈bulk 42
    decide +kernel
  · exact False.elim ((by decide +kernel : (21:V)∉bulk 56) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b42
    change ∀i∈(bulk 56).erase 22, action 0 i∈bulk 42
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b34
    change ∀i∈(bulk 56).erase 23, action 0 i∈bulk 34
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 56) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 56) hv)
theorem b57 : Strong (bulk 57) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 57) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b36
    change ∀i∈(bulk 57).erase 13, action 1 i∈bulk 36
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b50
    change ∀i∈(bulk 57).erase 14, action 0 i∈bulk 50
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b41
    change ∀i∈(bulk 57).erase 15, action 22 i∈bulk 41
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b33
    change ∀i∈(bulk 57).erase 16, action 24 i∈bulk 33
    decide +kernel
  · apply transport (perm 38) (actionValid 38).adj _ b44
    change ∀i∈(bulk 57).erase 17, action 38 i∈bulk 44
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b49
    change ∀i∈(bulk 57).erase 18, action 0 i∈bulk 49
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b47
    change ∀i∈(bulk 57).erase 19, action 22 i∈bulk 47
    decide +kernel
  · exact False.elim ((by decide +kernel : (20:V)∉bulk 57) hv)
  · apply transport (perm 25) (actionValid 25).adj _ b42
    change ∀i∈(bulk 57).erase 21, action 25 i∈bulk 42
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b43
    change ∀i∈(bulk 57).erase 22, action 0 i∈bulk 43
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b35
    change ∀i∈(bulk 57).erase 23, action 0 i∈bulk 35
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 57) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 57) hv)
theorem b58 : Strong (bulk 58) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 58) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b37
    change ∀i∈(bulk 58).erase 13, action 1 i∈bulk 37
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b49
    change ∀i∈(bulk 58).erase 14, action 36 i∈bulk 49
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b40
    change ∀i∈(bulk 58).erase 15, action 21 i∈bulk 40
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b43
    change ∀i∈(bulk 58).erase 16, action 24 i∈bulk 43
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b52
    change ∀i∈(bulk 58).erase 17, action 0 i∈bulk 52
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b51
    change ∀i∈(bulk 58).erase 18, action 0 i∈bulk 51
    decide +kernel
  · exact False.elim ((by decide +kernel : (19:V)∉bulk 58) hv)
  · apply transport (perm 22) (actionValid 22).adj _ b47
    change ∀i∈(bulk 58).erase 20, action 22 i∈bulk 47
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b48
    change ∀i∈(bulk 58).erase 21, action 0 i∈bulk 48
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b39
    change ∀i∈(bulk 58).erase 22, action 31 i∈bulk 39
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b36
    change ∀i∈(bulk 58).erase 23, action 0 i∈bulk 36
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 58) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 58) hv)
theorem b59 : Strong (bulk 59) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 59) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b38
    change ∀i∈(bulk 59).erase 13, action 1 i∈bulk 38
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b43
    change ∀i∈(bulk 59).erase 14, action 36 i∈bulk 43
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b41
    change ∀i∈(bulk 59).erase 15, action 33 i∈bulk 41
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b45
    change ∀i∈(bulk 59).erase 16, action 24 i∈bulk 45
    decide +kernel
  · apply transport (perm 6) (actionValid 6).adj _ b51
    change ∀i∈(bulk 59).erase 17, action 6 i∈bulk 51
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 59) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b51
    change ∀i∈(bulk 59).erase 19, action 0 i∈bulk 51
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b49
    change ∀i∈(bulk 59).erase 20, action 0 i∈bulk 49
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b34
    change ∀i∈(bulk 59).erase 21, action 35 i∈bulk 34
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b44
    change ∀i∈(bulk 59).erase 22, action 0 i∈bulk 44
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b37
    change ∀i∈(bulk 59).erase 23, action 0 i∈bulk 37
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 59) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 59) hv)
theorem b60 : Strong (bulk 60) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 60) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b39
    change ∀i∈(bulk 60).erase 13, action 1 i∈bulk 39
    decide +kernel
  · apply transport (perm 37) (actionValid 37).adj _ b36
    change ∀i∈(bulk 60).erase 14, action 37 i∈bulk 36
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b53
    change ∀i∈(bulk 60).erase 15, action 0 i∈bulk 53
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b47
    change ∀i∈(bulk 60).erase 16, action 24 i∈bulk 47
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 60) hv)
  · apply transport (perm 6) (actionValid 6).adj _ b51
    change ∀i∈(bulk 60).erase 18, action 6 i∈bulk 51
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b52
    change ∀i∈(bulk 60).erase 19, action 0 i∈bulk 52
    decide +kernel
  · apply transport (perm 38) (actionValid 38).adj _ b44
    change ∀i∈(bulk 60).erase 20, action 38 i∈bulk 44
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b35
    change ∀i∈(bulk 60).erase 21, action 13 i∈bulk 35
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b45
    change ∀i∈(bulk 60).erase 22, action 0 i∈bulk 45
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b38
    change ∀i∈(bulk 60).erase 23, action 0 i∈bulk 38
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 60) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 60) hv)
theorem b61 : Strong (bulk 61) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 61) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b41
    change ∀i∈(bulk 61).erase 13, action 1 i∈bulk 41
    decide +kernel
  · apply transport (perm 3) (actionValid 3).adj _ b42
    change ∀i∈(bulk 61).erase 14, action 3 i∈bulk 42
    decide +kernel
  · exact False.elim ((by decide +kernel : (15:V)∉bulk 61) hv)
  · apply transport (perm 24) (actionValid 24).adj _ b42
    change ∀i∈(bulk 61).erase 16, action 24 i∈bulk 42
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b53
    change ∀i∈(bulk 61).erase 17, action 0 i∈bulk 53
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b41
    change ∀i∈(bulk 61).erase 18, action 33 i∈bulk 41
    decide +kernel
  · apply transport (perm 21) (actionValid 21).adj _ b40
    change ∀i∈(bulk 61).erase 19, action 21 i∈bulk 40
    decide +kernel
  · apply transport (perm 22) (actionValid 22).adj _ b41
    change ∀i∈(bulk 61).erase 20, action 22 i∈bulk 41
    decide +kernel
  · apply transport (perm 35) (actionValid 35).adj _ b42
    change ∀i∈(bulk 61).erase 21, action 35 i∈bulk 42
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b40
    change ∀i∈(bulk 61).erase 22, action 32 i∈bulk 40
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b40
    change ∀i∈(bulk 61).erase 23, action 0 i∈bulk 40
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 61) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 61) hv)
theorem b62 : Strong (bulk 62) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 62) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 62) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b45
    change ∀i∈(bulk 62).erase 13, action 1 i∈bulk 45
    decide +kernel
  · apply transport (perm 18) (actionValid 18).adj _ b37
    change ∀i∈(bulk 62).erase 14, action 18 i∈bulk 37
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b37
    change ∀i∈(bulk 62).erase 15, action 33 i∈bulk 37
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b52
    change ∀i∈(bulk 62).erase 16, action 24 i∈bulk 52
    decide +kernel
  · apply transport (perm 6) (actionValid 6).adj _ b52
    change ∀i∈(bulk 62).erase 17, action 6 i∈bulk 52
    decide +kernel
  · exact False.elim ((by decide +kernel : (18:V)∉bulk 62) hv)
  · apply transport (perm 19) (actionValid 19).adj _ b45
    change ∀i∈(bulk 62).erase 19, action 19 i∈bulk 45
    decide +kernel
  · apply transport (perm 26) (actionValid 26).adj _ b52
    change ∀i∈(bulk 62).erase 20, action 26 i∈bulk 52
    decide +kernel
  · apply transport (perm 34) (actionValid 34).adj _ b45
    change ∀i∈(bulk 62).erase 21, action 34 i∈bulk 45
    decide +kernel
  · apply transport (perm 11) (actionValid 11).adj _ b50
    change ∀i∈(bulk 62).erase 22, action 11 i∈bulk 50
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 62) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b37
    change ∀i∈(bulk 62).erase 24, action 0 i∈bulk 37
    decide +kernel
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 62) hv)
theorem b63 : Strong (bulk 63) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 63) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 63) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b46
    change ∀i∈(bulk 63).erase 13, action 1 i∈bulk 46
    decide +kernel
  · apply transport (perm 18) (actionValid 18).adj _ b49
    change ∀i∈(bulk 63).erase 14, action 18 i∈bulk 49
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b52
    change ∀i∈(bulk 63).erase 15, action 32 i∈bulk 52
    decide +kernel
  · apply transport (perm 5) (actionValid 5).adj _ b49
    change ∀i∈(bulk 63).erase 16, action 5 i∈bulk 49
    decide +kernel
  · exact False.elim ((by decide +kernel : (17:V)∉bulk 63) hv)
  · apply transport (perm 6) (actionValid 6).adj _ b52
    change ∀i∈(bulk 63).erase 18, action 6 i∈bulk 52
    decide +kernel
  · apply transport (perm 19) (actionValid 19).adj _ b52
    change ∀i∈(bulk 63).erase 19, action 19 i∈bulk 52
    decide +kernel
  · apply transport (perm 26) (actionValid 26).adj _ b38
    change ∀i∈(bulk 63).erase 20, action 26 i∈bulk 38
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b38
    change ∀i∈(bulk 63).erase 21, action 13 i∈bulk 38
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b49
    change ∀i∈(bulk 63).erase 22, action 31 i∈bulk 49
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 63) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b38
    change ∀i∈(bulk 63).erase 24, action 0 i∈bulk 38
    decide +kernel
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 63) hv)
theorem b64 : Strong (bulk 64) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 64) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b54
    change ∀i∈(bulk 64).erase 13, action 1 i∈bulk 54
    decide +kernel
  · apply transport (perm 36) (actionValid 36).adj _ b57
    change ∀i∈(bulk 64).erase 14, action 36 i∈bulk 57
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b61
    change ∀i∈(bulk 64).erase 15, action 0 i∈bulk 61
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b55
    change ∀i∈(bulk 64).erase 16, action 24 i∈bulk 55
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b60
    change ∀i∈(bulk 64).erase 17, action 0 i∈bulk 60
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b59
    change ∀i∈(bulk 64).erase 18, action 0 i∈bulk 59
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b58
    change ∀i∈(bulk 64).erase 19, action 0 i∈bulk 58
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b57
    change ∀i∈(bulk 64).erase 20, action 0 i∈bulk 57
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b56
    change ∀i∈(bulk 64).erase 21, action 0 i∈bulk 56
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b55
    change ∀i∈(bulk 64).erase 22, action 0 i∈bulk 55
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b54
    change ∀i∈(bulk 64).erase 23, action 0 i∈bulk 54
    decide +kernel
  · exact False.elim ((by decide +kernel : (24:V)∉bulk 64) hv)
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 64) hv)
theorem b65 : Strong (bulk 65) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 65) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 65) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b55
    change ∀i∈(bulk 65).erase 13, action 1 i∈bulk 55
    decide +kernel
  · apply transport (perm 18) (actionValid 18).adj _ b59
    change ∀i∈(bulk 65).erase 14, action 18 i∈bulk 59
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b58
    change ∀i∈(bulk 65).erase 15, action 32 i∈bulk 58
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b58
    change ∀i∈(bulk 65).erase 16, action 24 i∈bulk 58
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b63
    change ∀i∈(bulk 65).erase 17, action 0 i∈bulk 63
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b62
    change ∀i∈(bulk 65).erase 18, action 0 i∈bulk 62
    decide +kernel
  · apply transport (perm 19) (actionValid 19).adj _ b60
    change ∀i∈(bulk 65).erase 19, action 19 i∈bulk 60
    decide +kernel
  · apply transport (perm 26) (actionValid 26).adj _ b60
    change ∀i∈(bulk 65).erase 20, action 26 i∈bulk 60
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b59
    change ∀i∈(bulk 65).erase 21, action 25 i∈bulk 59
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b57
    change ∀i∈(bulk 65).erase 22, action 31 i∈bulk 57
    decide +kernel
  · exact False.elim ((by decide +kernel : (23:V)∉bulk 65) hv)
  · apply transport (perm 0) (actionValid 0).adj _ b54
    change ∀i∈(bulk 65).erase 24, action 0 i∈bulk 54
    decide +kernel
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 65) hv)
theorem b66 : Strong (bulk 66) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 66) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 66) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b64
    change ∀i∈(bulk 66).erase 13, action 1 i∈bulk 64
    decide +kernel
  · apply transport (perm 2) (actionValid 2).adj _ b65
    change ∀i∈(bulk 66).erase 14, action 2 i∈bulk 65
    decide +kernel
  · apply transport (perm 32) (actionValid 32).adj _ b64
    change ∀i∈(bulk 66).erase 15, action 32 i∈bulk 64
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b64
    change ∀i∈(bulk 66).erase 16, action 24 i∈bulk 64
    decide +kernel
  · apply transport (perm 13) (actionValid 13).adj _ b65
    change ∀i∈(bulk 66).erase 17, action 13 i∈bulk 65
    decide +kernel
  · apply transport (perm 33) (actionValid 33).adj _ b65
    change ∀i∈(bulk 66).erase 18, action 33 i∈bulk 65
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b65
    change ∀i∈(bulk 66).erase 19, action 31 i∈bulk 65
    decide +kernel
  · apply transport (perm 24) (actionValid 24).adj _ b65
    change ∀i∈(bulk 66).erase 20, action 24 i∈bulk 65
    decide +kernel
  · apply transport (perm 25) (actionValid 25).adj _ b64
    change ∀i∈(bulk 66).erase 21, action 25 i∈bulk 64
    decide +kernel
  · apply transport (perm 31) (actionValid 31).adj _ b64
    change ∀i∈(bulk 66).erase 22, action 31 i∈bulk 64
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b65
    change ∀i∈(bulk 66).erase 23, action 0 i∈bulk 65
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b64
    change ∀i∈(bulk 66).erase 24, action 0 i∈bulk 64
    decide +kernel
  · exact False.elim ((by decide +kernel : (25:V)∉bulk 66) hv)
theorem b67 : Strong (bulk 67) := by
  apply fromChildren (by decide +kernel) (by decide +kernel)
  intro v hv
  fin_cases v
  · exact False.elim ((by decide +kernel : (0:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (1:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (2:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (3:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (4:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (5:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (6:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (7:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (8:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (9:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (10:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (11:V)∉bulk 67) hv)
  · exact False.elim ((by decide +kernel : (12:V)∉bulk 67) hv)
  · apply transport (perm 1) (actionValid 1).adj _ b66
    change ∀i∈(bulk 67).erase 13, action 1 i∈bulk 66
    decide +kernel
  · apply transport (perm 2) (actionValid 2).adj _ b66
    change ∀i∈(bulk 67).erase 14, action 2 i∈bulk 66
    decide +kernel
  · apply transport (perm 3) (actionValid 3).adj _ b66
    change ∀i∈(bulk 67).erase 15, action 3 i∈bulk 66
    decide +kernel
  · apply transport (perm 4) (actionValid 4).adj _ b66
    change ∀i∈(bulk 67).erase 16, action 4 i∈bulk 66
    decide +kernel
  · apply transport (perm 5) (actionValid 5).adj _ b66
    change ∀i∈(bulk 67).erase 17, action 5 i∈bulk 66
    decide +kernel
  · apply transport (perm 6) (actionValid 6).adj _ b66
    change ∀i∈(bulk 67).erase 18, action 6 i∈bulk 66
    decide +kernel
  · apply transport (perm 7) (actionValid 7).adj _ b66
    change ∀i∈(bulk 67).erase 19, action 7 i∈bulk 66
    decide +kernel
  · apply transport (perm 8) (actionValid 8).adj _ b66
    change ∀i∈(bulk 67).erase 20, action 8 i∈bulk 66
    decide +kernel
  · apply transport (perm 9) (actionValid 9).adj _ b66
    change ∀i∈(bulk 67).erase 21, action 9 i∈bulk 66
    decide +kernel
  · apply transport (perm 10) (actionValid 10).adj _ b66
    change ∀i∈(bulk 67).erase 22, action 10 i∈bulk 66
    decide +kernel
  · apply transport (perm 11) (actionValid 11).adj _ b66
    change ∀i∈(bulk 67).erase 23, action 11 i∈bulk 66
    decide +kernel
  · apply transport (perm 12) (actionValid 12).adj _ b66
    change ∀i∈(bulk 67).erase 24, action 12 i∈bulk 66
    decide +kernel
  · apply transport (perm 0) (actionValid 0).adj _ b66
    change ∀i∈(bulk 67).erase 25, action 0 i∈bulk 66
    decide +kernel

def sideSwap (v : V) : V := Fin.ofNat 26 (13+v.val)
theorem dualMap : (∀i j:V,sideSwap i=sideSwap j → i=j) ∧
    ∀i j:V,G (sideSwap i) (sideSwap j) ↔ G i j := by decide +kernel
noncomputable def dual : V ≃ V := Equiv.ofBijective sideSwap
  ⟨fun x y h => dualMap.1 x y h,Finite.injective_iff_surjective.mp (fun x y h => dualMap.1 x y h)⟩
theorem allStrong (r : R) : Strong (zone r) := by
  fin_cases r
  · apply transport dual dualMap.2 _ b67
    change ∀i∈zone 0,sideSwap i∈bulk 67
    decide +kernel
  · have e : zone 1=dz 171 := by decide +kernel
    exact e.symm ▸ (goodStrong dp171)
  · have e : zone 2=dz 131 := by decide +kernel
    exact e.symm ▸ (goodStrong dp131)
  · have e : zone 3=dz 132 := by decide +kernel
    exact e.symm ▸ (goodStrong dp132)
  · have e : zone 4=dz 80 := by decide +kernel
    exact e.symm ▸ (goodStrong dp80)
  · have e : zone 5=dz 37 := by decide +kernel
    exact e.symm ▸ (goodStrong dp37)
  · have e : zone 6=dz 81 := by decide +kernel
    exact e.symm ▸ (goodStrong dp81)
  · have e : zone 7=dz 82 := by decide +kernel
    exact e.symm ▸ (goodStrong dp82)
  · have e : zone 8=dz 83 := by decide +kernel
    exact e.symm ▸ (goodStrong dp83)
  · have e : zone 9=dz 84 := by decide +kernel
    exact e.symm ▸ (goodStrong dp84)
  · have e : zone 10=dz 85 := by decide +kernel
    exact e.symm ▸ (goodStrong dp85)
  · have e : zone 11=dz 86 := by decide +kernel
    exact e.symm ▸ (goodStrong dp86)
  · have e : zone 12=dz 87 := by decide +kernel
    exact e.symm ▸ (goodStrong dp87)
  · have e : zone 13=dz 88 := by decide +kernel
    exact e.symm ▸ (goodStrong dp88)
  · have e : zone 14=dz 89 := by decide +kernel
    exact e.symm ▸ (goodStrong dp89)
  · have e : zone 15=dz 90 := by decide +kernel
    exact e.symm ▸ (goodStrong dp90)
  · have e : zone 16=dz 91 := by decide +kernel
    exact e.symm ▸ (goodStrong dp91)
  · have e : zone 17=dz 92 := by decide +kernel
    exact e.symm ▸ (goodStrong dp92)
  · have e : zone 18=dz 94 := by decide +kernel
    exact e.symm ▸ (goodStrong dp94)
  · have e : zone 19=dz 95 := by decide +kernel
    exact e.symm ▸ (goodStrong dp95)
  · have e : zone 20=dz 96 := by decide +kernel
    exact e.symm ▸ (goodStrong dp96)
  · have e : zone 21=dz 55 := by decide +kernel
    exact e.symm ▸ (goodStrong dp55)
  · have e : zone 22=dz 133 := by decide +kernel
    exact e.symm ▸ (goodStrong dp133)
  · have e : zone 23=dz 135 := by decide +kernel
    exact e.symm ▸ (goodStrong dp135)
  · have e : zone 24=dz 172 := by decide +kernel
    exact e.symm ▸ (goodStrong dp172)
  · have e : zone 25=bulk 67 := by decide +kernel
    exact e.symm ▸ (b67)

theorem deepCore {D : Dag} (h : StrictLive 26 D) (hc : sem_Comp 26 G D)
    (ind : ∀i∈ineligSet 26 D,∀j∈ineligSet 26 D,¬G i j) : 48≤D.length := by
  obtain ⟨r,e,valid,sub⟩ := envelope ind
  exact transport e valid.adj sub (allStrong r) D h hc subset_rfl
theorem lower48 (hG : sem_Gr G)
    (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
      C.eval (List.ofFn x)=true ↔ sem_Edge G x) : 48≤C.size := by
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
  obtain ⟨D,ld,lim,simulation⟩ := normalize_strictLive (n:=26) C hm
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
  have sem : sem_Comp 26 G D := fun x => by rw [simulation x]; exact correct x
  have ind : ∀i∈ineligSet 26 D,∀j∈ineligSet 26 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover hG ld sem ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have enriched := deepCore ld sem ind
  omega


theorem boundary47 {C : Circuit} {o : List Nat} (hm : Monotone2 C) (out : o.length≤2)
    (ht : Promise17245.Tests C o) : 47≤C.size := by
  have h := lower48 regular (Promise17245.finish C o) (Promise17245.finish_mono hm out) (Physical17245.completed hm ht)
  rw [Promise17245.finish_size] at h
  omega
end Deep17245
namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := Fin 13
abbrev W := Fin 26
abbrev pt (p : V) : W := Fin.castAdd 13 p
abbrev ln (l : V) : W := Fin.natAdd 13 l
def offs : Finset V := {0,1,3,9}
def Inc (p l : V) : Prop := ∃ a ∈ offs, p = l+a
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def Avoid (S : Finset V) (l : V) := ∀ p ∈ S, ¬ Inc p l
instance (S : Finset V) (l : V) : Decidable (Avoid S l) := by unfold Avoid; infer_instance
def Closed (S : Finset V) := ∀ p ∉ S, ∃ l, Avoid S l ∧ Inc p l
def frame (S : Finset V) (i : W) : Bool :=
  decide ((∃ p ∈ S, i=pt p) ∨ ∃ l, i=ln l ∧ Avoid S l)
def pos (p l : V) (i : W) : Bool := decide (i=pt p ∨ i=ln l)
def Hit (x : W → Bool) := ∃ p l, Inc p l ∧ x (pt p)=true ∧ x (ln l)=true
def Tests (C : Circuit) : Prop :=
  (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) ∧
  ∀ S, Closed S → circuitFun 26 C (frame S)=false
def Exact (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ Hit x

theorem parts : ∀ i : W, (∃ p, i=pt p) ∨ ∃ l, i=ln l := by decide
theorem disj : ∀ p l : V, pt p ≠ ln l := by decide
theorem pp : ∀ p q : V, pt p=pt q → p=q := by decide
theorem ll : ∀ p q : V, ln p=ln q → p=q := by decide

theorem frame_pt (S : Finset V) (p : V) : frame S (pt p)=true ↔ p∈S := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨q,hq,e⟩|⟨l,e,_⟩)
    · exact (pp _ _ e) ▸ hq
    · exact (disj _ _ e).elim
  · exact fun h => Or.inl ⟨p,h,rfl⟩
theorem frame_ln (S : Finset V) (l : V) : frame S (ln l)=true ↔ Avoid S l := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨p,_,e⟩|⟨k,e,h⟩)
    · exact (disj _ _ e.symm).elim
    · exact (ll _ _ e) ▸ h
  · exact fun h => Or.inr ⟨l,rfl,h⟩
theorem complete {C : Circuit} (hm : Monotone2 C) : Tests C ↔ Exact C := by
  constructor
  · intro h x
    constructor
    · intro live
      by_contra empty
      let S := Finset.univ.filter fun p : V => ∀ l : V, x (ln l)=true → ¬ Inc p l
      have mem (p : V) : p∈S ↔ ∀ l, x (ln l)=true → ¬Inc p l := by simp [S]
      have avoid (l : V) (selected : x (ln l)=true) : Avoid S l :=
        fun p hp => (mem p).mp hp l selected
      have closed : Closed S := by
        intro p hp
        rw [mem] at hp
        push_neg at hp
        obtain ⟨l,hl,edge⟩ := hp
        exact ⟨l,avoid l hl,edge⟩
      have below : x≤frame S := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        rcases parts i with ⟨p,rfl⟩|⟨l,rfl⟩
        · exact (frame_pt S p).mpr ((mem p).mpr (fun l hl edge => empty ⟨p,l,edge,hi,hl⟩))
        · exact (frame_ln S l).mpr (avoid l hi)
      have bad : circuitFun 26 C (frame S)=true := PlaneOrdered.cmono C hm 26 _ _ below live
      rw [h.2 S closed] at bad
      contradiction
    · rintro ⟨p,l,edge,hp,hl⟩
      apply PlaneOrdered.cmono C hm 26 (pos p l) x _ (h.1 p l edge)
      intro i
      apply Bool.le_iff_imp.mpr
      simp only [pos,decide_eq_true_eq]
      rintro (rfl|rfl)
      · exact hp
      · exact hl
  · intro h
    constructor
    · intro p l edge
      exact (h _).mpr ⟨p,l,edge,by simp [pos],by simp [pos]⟩
    · intro S _
      cases hv : circuitFun 26 C (frame S) with
      | false => rfl
      | true =>
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp hv
        exact ((frame_ln S l).mp hl p ((frame_pt S p).mp hp) edge).elim

theorem exact_lower_iff :
    (∀ C : Circuit, Monotone2 C → C.size≤63 →
      (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) →
      (∀ S, Closed S → circuitFun 26 C (frame S)=false) → False) ↔
    ∀ C : Circuit, Monotone2 C → Exact C → 64≤C.size := by
  constructor
  · intro h C hm exactC
    obtain ⟨hp,hn⟩ := (complete hm).mpr exactC
    by_contra! small
    exact h C hm (by omega) hp hn
  · intro h C hm small hp hn
    have := h C hm ((complete hm).mp ⟨hp,hn⟩)
    omega
end Full5741
namespace Rel5741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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
    rw [he, hw, PlaneOrdered.getD_snoc_eq, PlaneOrdered.getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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

end Rel5741
namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flip (i : W) : W :=
  if i.val<13 then i else ln (-(Fin.ofNat 13 i.val))
theorem flip_pt : ∀ p : V, flip (pt p)=pt p := by decide
theorem flip_ln : ∀ l : V, flip (ln l)=ln (-l) := by decide
theorem inc_plus : ∀ p l : V, Inc p l ↔ Promise17245.Inc p (-l) := by decide +kernel
theorem plus_inc : ∀ p l : V, Promise17245.Inc p l ↔ Inc p (-l) := by decide +kernel

def renamed (C : Circuit) := Rel5741.relabel 26 26 flip C
theorem rename_size (C : Circuit) : (renamed C).size=C.size := by
  simp [renamed,Rel5741.relabel,Circuit.size]
theorem rename_mono {C : Circuit} (hm : Monotone2 C) : Monotone2 (renamed C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
  exact ⟨(hm old mem).1,by simpa [Rel5741.relGate] using (hm old mem).2⟩
theorem rename_eval (C : Circuit) (x : W → Bool) :
    circuitFun 26 (renamed C) x = circuitFun 26 C (x ∘ flip) :=
  (Rel5741.rel_fold 26 26 flip C.gates _ _ (Rel5741.rel_init 26 26 flip x)).2.2 C.output
def PlusHit (x : W → Bool) :=
  ∃ p l : V, Promise17245.Inc p l ∧ x (pt p)=true ∧ x (ln l)=true
def PlusExact (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ PlusHit x

theorem forward {C : Circuit} (h : Exact C) : PlusExact (renamed C) := by
  intro x
  rw [rename_eval,h]
  constructor
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(inc_plus p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa only [Function.comp_apply,flip_ln,neg_neg] using hl⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(plus_inc p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa only [Function.comp_apply,flip_ln,neg_neg] using hl⟩
theorem backward {C : Circuit} (h : PlusExact C) : Exact (renamed C) := by
  intro x
  rw [rename_eval,h]
  constructor
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(plus_inc p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa only [Function.comp_apply,flip_ln,neg_neg] using hl⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(inc_plus p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa only [Function.comp_apply,flip_ln,neg_neg] using hl⟩

open Promise17245 in
def Old (C : Circuit) :=
  (∀ p l : V, Promise17245.Inc p l → C.eval (List.ofFn (vec {p} {l}))=true) ∧
  ∀ S : Finset V, S.card≤3 →
    C.eval (List.ofFn (vec S (off S)))=false ∧ C.eval (List.ofFn (vec (off S) S))=false

theorem read_scalar (C : Circuit) (x : W → Bool) : Promise17245.read C [C.output] x=circuitFun 26 C x := by
  change GateOp.or.eval [((C.wires (List.ofFn x)).getD C.output false)] =
    ((C.wires (List.ofFn x)).getD C.output false)
  cases (C.wires (List.ofFn x)).getD C.output false <;> rfl

theorem vecpt (S T : Finset V) (p : V) : Promise17245.vec S T (pt p)=true ↔ p∈S := by
  have e : Fin.ofNat 13 (pt p).val=p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
  simp [Promise17245.vec,show (pt p).val<13 from p.isLt,e]
theorem vecln (S T : Finset V) (l : V) : Promise17245.vec S T (ln l)=true ↔ l∈T := by
  have e : Fin.ofNat 13 (ln l).val=l := Fin.ext (by change (13+l.val)%13=l.val; omega)
  have hi : ¬(ln l).val<13 := by change ¬13+l.val<13; omega
  simp only [Promise17245.vec,if_neg hi,e,decide_eq_true_eq]

open Promise17245 in
theorem old_iff {C : Circuit} (hm : Monotone2 C) : Old C ↔ PlusExact C := by
  constructor
  · intro h x
    have ht : Promise17245.Tests C [C.output] := by
      unfold Promise17245.Tests
      simp only [read_scalar]
      exact h
    simpa only [read_scalar,PlusHit,pt,ln] using exact_eval hm ht x
  · intro h
    constructor
    · intro p l edge
      exact (h _).mpr ⟨p,l,edge,(vecpt _ _ _).mpr (by simp),(vecln _ _ _).mpr (by simp)⟩
    · intro S _
      constructor
      · apply Bool.eq_false_iff.mpr
        intro y
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp y
        exact (Finset.mem_filter.mp ((vecln _ _ _).mp hl)).2 p ((vecpt _ _ _).mp hp) edge
      · apply Bool.eq_false_iff.mpr
        intro y
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp y
        apply (Finset.mem_filter.mp ((vecpt _ _ _).mp hp)).2 l ((vecln _ _ _).mp hl)
        simpa only [Promise17245.Inc, Nat.add_comm l.val p.val] using edge

theorem equivalent_twins :
    (∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧ Tests C) ↔
    ∃ D : Circuit, Monotone2 D ∧ D.size≤63 ∧ Old D := by
  constructor
  · rintro ⟨C,hm,hs,ht⟩
    exact ⟨renamed C,rename_mono hm,by simpa [rename_size] using hs,
      (old_iff (rename_mono hm)).mpr (forward ((complete hm).mp ht))⟩
  · rintro ⟨D,hm,hs,ht⟩
    exact ⟨renamed D,rename_mono hm,by simpa [rename_size] using hs,
      (complete (rename_mono hm)).mpr (backward ((old_iff hm).mp ht))⟩
end Full5741

namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_971_aux
theorem lower48 {C : Circuit} (hm : Monotone2 C) (h : Tests C) : 48≤C.size := by
  let D := renamed C
  have ex : PlusExact D := forward ((complete hm).mp h)
  have correct (x : W → Bool) : D.eval (List.ofFn x)=true ↔ sem_Edge Geometry17245.G x := by
    change circuitFun 26 D x=true ↔ _
    rw [ex]
    constructor
    · rintro ⟨p,l,e,hp,hl⟩
      exact ⟨pt p,ln l,Physical17245.flags p l e,hp,hl⟩
    · rintro ⟨a,b,e,ha,hb⟩
      obtain ⟨p,l,edge,pair⟩ := Physical17245.endpoints a b e
      rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨p,l,edge,ha,hb⟩
      · exact ⟨p,l,edge,hb,ha⟩
  have low := Deep17245.lower48 Mixed17245.regular D (rename_mono hm) correct
  simpa [D,rename_size] using low
end Full5741

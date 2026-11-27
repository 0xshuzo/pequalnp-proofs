import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18910

namespace DagProof

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

theorem marked_live_aux {n : ℕ} (F : (Fin n → Bool) → Bool)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ F x ≠ F y) :
    ∀ (s : ℕ) (D : Dag), D.length = s → Strict n D → D ≠ [] →
      (∀ x : Fin n → Bool, val D x (outW n D) = F x) →
      ∃ D' : Dag, StrictLive n D' ∧ D'.length ≤ s ∧ (D'=D ∨ D'.length < s) ∧
        ∀ x : Fin n → Bool, val D' x (outW n D') = F x := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro D hlen hS hne hD
    have hpos : 0 < D.length := List.length_pos_iff.mpr hne
    by_cases hL : Live n D
    · exact ⟨D, ⟨hS, hL, hne⟩, hlen.le, Or.inl rfl, hD⟩
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
        obtain ⟨D', h1, h2, _, h3⟩ := ih (D.length - 1) (by omega) (na_del n j D) hl
          (na_del_strict hS j hj hf0)
          (fun h => by rw [h] at hl; simp at hl; omega)
          (fun x => by
            have ho : outW n (na_del n j D) = n + (D.length - 1) - 1 := by unfold outW; rw [hl]
            have hu : na_up (n + j) (n + (D.length - 1) - 1) = outW n D := by
              unfold na_up outW; split_ifs <;> omega
            rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
            exact hD x)
        exact ⟨D', h1, by omega, Or.inr (by omega), h3⟩


theorem preserve_marks {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (hnc : ∀ b : Bool, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ b)
    (hnp : ∀ i : Fin n, ∃ x : Fin n → Bool, C.eval (List.ofFn x) ≠ x i)
    (hess : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧ C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (least : ∀ D : Dag, StrictLive n D → (∀x : Fin n → Bool,val D x (outW n D)=C.eval (List.ofFn x)) → C.size≤D.length)
    (k : Nat) (nc : ∀ b : Bool, ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD k false ≠ b) :
    ∃ D : Dag, StrictLive n D ∧ D.length=C.size ∧
      (∀ x : Fin n → Bool,val D x (outW n D)=C.eval (List.ofFn x)) ∧
      ∃w,∀x : Fin n → Bool,val D x w=(C.wires (List.ofFn x)).getD k false := by
  have h0 : na_Good n ((List.range n).map Sum.inr, ([] : Dag)) := by
    refine ⟨fun j hj => absurd hj (by simp), fun r hr => ?_⟩
    simp only [List.mem_map, List.mem_range] at hr
    obtain ⟨k, hk, rfl⟩ := hr
    simpa [na_ok] using hk
  obtain ⟨⟨hS, hok⟩, hlen, hsem⟩ := na_fold_spec n C.gates hm _ h0
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

  have hlen' : D.length≤C.size := by simpa [Circuit.size] using hlen
  have wires (x : Fin n → Bool) : (C.wires (List.ofFn x)).getD k false =
      refVal (wl D (List.ofFn x)) (na_look m k) := by
    rw [na_look_val,hsem x (List.ofFn x) (na_init n x)]
    rfl
  rcases hr : na_look m C.output with b|j
  · obtain ⟨x,hx⟩ := hnc b
    exact (hx (by rw [hev,hr]; rfl)).elim
  · rw [hr] at hk
    have hj : j < n+D.length := hk
    by_cases raw : j < n
    · obtain ⟨x,hx⟩ := hnp ⟨j,raw⟩
      exact (hx (by rw [hev,hr]; exact val_input D x j raw)).elim
    · let P := D.take (j-n+1)
      have lp : P.length=j-n+1 := by dsimp [P]; rw [List.length_take]; omega
      have ne : P≠[] := fun eq => by rw [eq] at lp; simp at lp
      have g : Strict n P := na_strict_take hS _
      have sem : ∀ x : Fin n → Bool,val P x (outW n P)=C.eval (List.ofFn x) := by
        intro x
        have o : outW n P=j := by unfold outW; rw [lp]; omega
        rw [o,val_take D x (j-n+1) j (by omega) (by omega),hev x,hr];rfl
      obtain ⟨L,live,len,cl,ok⟩ := marked_live_aux _ hess _ P rfl g ne sem
      have floor := least L live ok
      have lp' : P.length≤D.length := by omega
      have sz : L.length=C.size := by omega
      have same : L=P := cl.resolve_right (by omega)
      have dp : P=D := List.take_of_length_le (by omega)
      subst L
      refine ⟨P,live,sz,ok,?_⟩
      rcases ref : na_look m k with b|w
      · obtain ⟨x,hx⟩ := nc b
        exact (hx (by rw [wires,ref];rfl)).elim
      · refine ⟨w,fun x => ?_⟩
        rw [dp,wires,ref];rfl

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
end DagProof

namespace DagProof
variable {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag}
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



end DagProof
namespace Merge
open PEqualNP.Outside.L_meta_18910.DagProof
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
end Merge
namespace Main
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18910.DagProof
abbrev V := Fin 17
def E (u v : V) := ([33216,36352,61440,70208,74880,84224]:List Nat).getD u.val 0 |>.testBit v.val
def G (u v : V) := E u v=true ∨ E v u=true
instance (u v : V) : Decidable (G u v) := by unfold G; infer_instance
theorem regular : sem_Gr G := by unfold sem_Gr; decide +kernel
abbrev L := Fin 6
def line (l : L) : V := ⟨l.val,by omega⟩
def key (s : Finset L) : Nat := ∑ l∈s, 2^l.val
def panel (s : Finset L) : Finset V := Finset.univ.filter fun v =>
    (∃ l∈s,v=line l) ∨ (6≤v.val ∧ ∀ l∈s,¬G v (line l))
def nbr (v : V) := Finset.univ.filter fun i => G v i

def Data (Z T U H : Finset V) (A : V → Finset V) : Prop :=
  H ⊆ T ∧ (∀i∈Z,i∉U → (∃a∈T,G i a) ∧ ∀ f∈H,∃a∈A f,G i a) ∧
  ∀ f∈H, (∀ a∈A f,∀ b∈A f,¬G a b) ∧ T.erase f ⊆ A f ∧ ∃ a∈A f,G f a
def every (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 17).all fun i => if i∈S then f i else true
def someIn (S : Finset V) (f : V → Bool) : Bool :=
  (List.finRange 17).any fun i => decide (i∈S) && f i
theorem every_true (S : Finset V) (f : V → Bool) :
    every S f=true ↔ ∀i∈S,f i=true := by
  simp [every,List.all_eq_true] <;> grind
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
    exact ⟨h0.1,fun x hx => h0.2.1 x (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hx).2,h0.2.2⟩

inductive Good (k : ℕ) : Finset V → Prop where
 | done (Z T U H : Finset V) (A : V → Finset V) (data : Data Z T U H A)
     (price : U.card+2*T.card ≤ k+H.card) : Good k Z
 | pivot (Z T U H : Finset V) (A : V → Finset V) (z : V) (data : Data Z T U H A)
     (price : U.card+2*T.card+1 ≤ k+H.card+(nbr z ∩ T).card)
     (child : Good k (Z.erase z)) : Good k Z

theorem merges_mono {D : Dag} {T P : Finset V} (h : P ⊆ T) :
    merges 17 D (carrierT 17 D P) ⊆ merges 17 D (carrierT 17 D T) := by
  have lift {w : ℕ} (hw : w∈carrierT 17 D P) : w∈carrierT 17 D T := by
    obtain ⟨v,hv⟩ := k4_mem_carrier.mp hw
    obtain ⟨a,b⟩ := Finset.mem_inter.mp hv
    exact k4_mem_carrier.mpr ⟨v,Finset.mem_inter.mpr ⟨a,h b⟩⟩
  intro j hj
  obtain ⟨hr,out,a,b⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨hr,lift out,lift a,lift b⟩

theorem charge {D : Dag} (hG : sem_Gr G) (live : StrictLive 17 D) (sem : sem_Comp 17 G D)
    {Z T U H : Finset V} {A : V → Finset V} (inc : ineligSet 17 D ⊆ Z) (dat : Data Z T U H A) :
    33+Bzero 17 D+H.card+(merges 17 D (carrierT 17 D T)).card ≤ D.length+U.card+2*T.card := by
  classical
  let I := ineligSet 17 D
  let E := eligSet 17 D
  have total : I.card+E.card=17 := by
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
  have plus := totalSurplus_split 17 D
  omega

theorem panelBound {k : ℕ} {Z : Finset V} {D : Dag} (hG : sem_Gr G) (live : StrictLive 17 D)
    (sem : sem_Comp 17 G D) (inc : ineligSet 17 D ⊆ Z) (valid : Good k Z) : 33+Bzero 17 D≤D.length+k := by
  classical
  induction valid with
  | done Z T U H A dat price =>
    have c := charge hG live sem inc dat
    omega
  | pivot Z T U H A z dat price child ih =>
    by_cases hz : z∈ineligSet 17 D
    · have c := charge hG live sem inc dat
      obtain ⟨pos,hp⟩ := k4_assigned hG live sem
      have prop : nbr z ∩ T ⊆ supp 17 D (src D (pos z)) := by
        intro a ha
        exact (hp.1 z hz).2.2.1 a (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2
      have m := PEqualNP.Outside.L_meta_18910.Merge.support_price live.1 (nbr z ∩ T) (src D (pos z)) prop
      have incl := Finset.card_le_card (merges_mono (D:=D) (Finset.inter_subset_right : nbr z ∩ T ⊆ T))
      omega
    · exact ih (fun i hi => Finset.mem_erase.mpr ⟨fun e => hz (e ▸ hi),inc hi⟩)
structure Node where
  Z : Finset V
  T : Finset V
  U : Finset V
  H : Finset V
  expos : List (V × Finset V)
  mark : Option V
  child : Nat
deriving Inhabited
def Node.A (r : Node) (f : V) : Finset V := (r.expos.lookup f).getD ∅
namespace Cap5
def tree : Array Node := #[
⟨{3,4,5,15},∅,{3,4,5,15},∅,[],none,0⟩,
⟨{0,1,2,16},∅,{0,1,2,16},∅,[],none,0⟩,
⟨{1,2,4,5,6},∅,{1,2,4,5,6},∅,[],none,0⟩,
⟨{1,2,3,5,7},∅,{1,2,3,5,7},∅,[],none,0⟩,
⟨{1,2,5,6,7},∅,{1,2,5,6,7},∅,[],none,0⟩,
⟨{1,2,3,4,8},∅,{1,2,3,4,8},∅,[],none,0⟩,
⟨{1,2,4,6,8},∅,{1,2,4,6,8},∅,[],none,0⟩,
⟨{1,2,3,7,8},∅,{1,2,3,7,8},∅,[],none,0⟩,
⟨{0,2,4,5,9},∅,{0,2,4,5,9},∅,[],none,0⟩,
⟨{2,4,5,6,9},∅,{2,4,5,6,9},∅,[],none,0⟩,
⟨{0,2,3,5,10},∅,{0,2,3,5,10},∅,[],none,0⟩,
⟨{2,3,5,7,10},∅,{2,3,5,7,10},∅,[],none,0⟩,
⟨{0,2,5,9,10},∅,{0,2,5,9,10},∅,[],none,0⟩,
⟨{0,2,3,4,11},∅,{0,2,3,4,11},∅,[],none,0⟩,
⟨{2,3,4,8,11},∅,{2,3,4,8,11},∅,[],none,0⟩,
⟨{0,2,4,9,11},∅,{0,2,4,9,11},∅,[],none,0⟩,
⟨{0,2,3,10,11},∅,{0,2,3,10,11},∅,[],none,0⟩,
⟨{0,1,4,5,12},∅,{0,1,4,5,12},∅,[],none,0⟩,
⟨{1,4,5,6,12},∅,{1,4,5,6,12},∅,[],none,0⟩,
⟨{0,4,5,9,12},∅,{0,4,5,9,12},∅,[],none,0⟩,
⟨{0,1,3,5,13},∅,{0,1,3,5,13},∅,[],none,0⟩,
⟨{1,3,5,7,13},∅,{1,3,5,7,13},∅,[],none,0⟩,
⟨{0,3,5,10,13},∅,{0,3,5,10,13},∅,[],none,0⟩,
⟨{0,1,5,12,13},∅,{0,1,5,12,13},∅,[],none,0⟩,
⟨{0,1,3,4,14},∅,{0,1,3,4,14},∅,[],none,0⟩,
⟨{1,3,4,8,14},∅,{1,3,4,8,14},∅,[],none,0⟩,
⟨{0,3,4,11,14},∅,{0,3,4,11,14},∅,[],none,0⟩,
⟨{0,1,4,12,14},∅,{0,1,4,12,14},∅,[],none,0⟩,
⟨{0,1,3,13,14},∅,{0,1,3,13,14},∅,[],none,0⟩,
⟨{0,1,2,3,4,5},{15},{3,4,5},∅,[],none,0⟩,
⟨{2,5,6,7,9,10},{0},{2,5,9,10},{0},[(0,{3,4,8,11,14,15})],none,0⟩,
⟨{2,4,6,8,9,11},{0},{2,4,9,11},{0},[(0,{3,5,7,10,13,15})],none,0⟩,
⟨{2,3,7,8,10,11},{0},{2,3,10,11},{0},[(0,{4,5,6,9,12,15})],none,0⟩,
⟨{1,5,6,7,12,13},{0},{1,5,12,13},{0},[(0,{3,4,8,11,14,15})],none,0⟩,
⟨{0,5,9,10,12,13},{1},{0,5,12,13},{1},[(1,{3,4,8,11,14,15})],none,0⟩,
⟨{1,4,6,8,12,14},{0},{1,4,12,14},{0},[(0,{3,5,7,10,13,15})],none,0⟩,
⟨{0,4,9,11,12,14},{1},{0,4,12,14},{1},[(1,{3,5,7,10,13,15})],none,0⟩,
⟨{1,3,7,8,13,14},{0},{1,3,13,14},{0},[(0,{4,5,6,9,12,15})],none,0⟩,
⟨{0,3,10,11,13,14},{1},{0,3,13,14},{1},[(1,{4,5,6,9,12,15})],none,0⟩,
⟨{4,5,6,9,12,15},{3},{4,5,15},{3},[(3,{0,1,2,16})],none,0⟩,
⟨{3,5,7,10,13,15},{4},{3,5,15},{4},[(4,{0,1,2,16})],none,0⟩,
⟨{3,4,8,11,14,15},{5},{3,4,15},{5},[(5,{0,1,2,16})],none,0⟩,
⟨{1,2,6,7,8,16},{0},{1,2,16},{0},[(0,{3,4,5,15})],none,0⟩,
⟨{0,2,9,10,11,16},{1},{0,2,16},{1},[(1,{3,4,5,15})],none,0⟩,
⟨{0,1,12,13,14,16},{2},{0,1,16},{2},[(2,{3,4,5,15})],none,0⟩,
⟨{7,8,9,10,11,12,13,14},{1,4},{8,12,14},{1,4},[(1,{3,4,5,15}),(4,{0,1,2,16})],none,0⟩,
⟨{5,6,7,9,10,12,13,15},{0,1},{5,12,13},{0,1},[(0,{1,3,4,8,14}),(1,{0,3,4,11,14})],none,0⟩,
⟨{4,6,8,9,11,12,14,15},{0,1},{4,12,14},{0,1},[(0,{1,3,5,7,13}),(1,{0,3,5,10,13})],none,0⟩,
⟨{3,7,8,10,11,13,14,15},{0,1},{3,13,14},{0,1},[(0,{1,4,5,6,12}),(1,{0,4,5,9,12})],none,0⟩,
⟨{2,6,7,8,9,10,11,16},{0,3},{2,10,11},{0,3},[(0,{3,4,5,15}),(3,{0,1,4,12,14})],none,0⟩,
⟨{1,6,7,8,12,13,14,16},{0,3},{1,13,14},{0,3},[(0,{3,4,5,15}),(3,{0,2,4,9,11})],none,0⟩,
⟨{0,9,10,11,12,13,14,16},{1,3},{0,13,14},{1,3},[(1,{3,4,5,15}),(3,{1,2,4,6,8})],none,0⟩,
⟨{6,7,8,9,10,11,12,13,14},{0,3},{10,11,13,14},{0,3},[(0,{3,4,5,15}),(3,{0,1,2,16})],(some 6),45⟩,
⟨{6,7,8,9,10,11,12,13,14,16},{3,4,5},∅,∅,[],(some 16),52⟩,
⟨{6,7,8,9,10,11,12,13,14,15,16},{0,1,2},{16},∅,[],(some 15),53⟩]
def node (i : Nat) : Node := (tree[i]?).getD default
def valid (i : Nat) : Bool :=
  let r := node i
  verifies r.Z r.T r.U r.H r.A && (match r.mark with
    | none => decide (r.U.card+2*r.T.card≤5+r.H.card)
    | some z => decide ((r.U.card+2*r.T.card+1≤5+r.H.card+(nbr z∩r.T).card) ∧ (r.child < i) ∧ r.Z.erase z=(node r.child).Z))
private theorem dataOK : ∀ i : Fin 55, valid i.val=true := by decide +kernel
theorem checked (i : Nat) (hi : i<55) : Good 5 (node i).Z := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have both := Bool.and_eq_true_iff.mp (dataOK ⟨i,hi⟩)
    have dat := verifies_sound both.1
    cases m : (node i).mark with
    | none =>
      have yes := both.2
      simp only [m] at yes
      exact .done _ _ _ _ _ dat (of_decide_eq_true yes)
    | some z =>
      have yes := both.2
      simp only [m] at yes
      obtain ⟨pr,lt,eqn⟩ := of_decide_eq_true yes
      exact .pivot _ _ _ _ _ z dat pr (eqn.symm ▸ ih _ lt (by omega))
def indices : Array Nat := #[54,51,50,44,49,43,42,1,48,38,37,28,32,16,7,29,47,36,35,27,31,15,6,29,41,26,25,24,14,13,5,29,46,34,33,23,30,12,4,29,40,22,21,20,11,10,3,29,39,19,18,17,9,8,2,29,0,29,29,29,29,29,29,29]
def whereIs (S : Finset L) := (indices[key S]?).getD 0
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem covering : ∀ S : Finset L, whereIs S<55 ∧ panel S⊆(node (whereIs S)).Z := by decide +kernel
end Cap5
namespace Cap4
def tree : Array Node := #[
⟨{3,4,5,15},∅,{3,4,5,15},∅,[],none,0⟩,
⟨{0,1,2,16},∅,{0,1,2,16},∅,[],none,0⟩,
⟨{1,2,4,5,6},{15},{4,5,6},{15},[(15,{0,9,10,11,12,13,14,16})],none,0⟩,
⟨{1,2,3,5,7},{15},{3,5,7},{15},[(15,{0,9,10,11,12,13,14,16})],none,0⟩,
⟨{1,2,5,6,7},{0},{1,2,5},{0},[(0,{3,4,8,11,14,15})],none,0⟩,
⟨{1,2,3,4,8},{15},{3,4,8},{15},[(15,{0,9,10,11,12,13,14,16})],none,0⟩,
⟨{1,2,4,6,8},{0},{1,2,4},{0},[(0,{3,5,7,10,13,15})],none,0⟩,
⟨{1,2,3,7,8},{0},{1,2,3},{0},[(0,{4,5,6,9,12,15})],none,0⟩,
⟨{0,2,4,5,9},{15},{4,5,9},{15},[(15,{1,6,7,8,12,13,14,16})],none,0⟩,
⟨{2,4,5,6,9},{3},{2,4,5},{3},[(3,{0,1,12,13,14,16})],none,0⟩,
⟨{0,2,3,5,10},{15},{3,5,10},{15},[(15,{1,6,7,8,12,13,14,16})],none,0⟩,
⟨{2,3,5,7,10},{4},{2,3,5},{4},[(4,{0,1,12,13,14,16})],none,0⟩,
⟨{0,2,5,9,10},{1},{0,2,5},{1},[(1,{3,4,8,11,14,15})],none,0⟩,
⟨{0,2,3,4,11},{15},{3,4,11},{15},[(15,{1,6,7,8,12,13,14,16})],none,0⟩,
⟨{2,3,4,8,11},{5},{2,3,4},{5},[(5,{0,1,12,13,14,16})],none,0⟩,
⟨{0,2,4,9,11},{1},{0,2,4},{1},[(1,{3,5,7,10,13,15})],none,0⟩,
⟨{0,2,3,10,11},{1},{0,2,3},{1},[(1,{4,5,6,9,12,15})],none,0⟩,
⟨{0,1,4,5,12},{15},{4,5,12},{15},[(15,{2,6,7,8,9,10,11,16})],none,0⟩,
⟨{1,4,5,6,12},{3},{1,4,5},{3},[(3,{0,2,9,10,11,16})],none,0⟩,
⟨{0,4,5,9,12},{3},{0,4,5},{3},[(3,{1,2,6,7,8,16})],none,0⟩,
⟨{0,1,3,5,13},{15},{3,5,13},{15},[(15,{2,6,7,8,9,10,11,16})],none,0⟩,
⟨{1,3,5,7,13},{4},{1,3,5},{4},[(4,{0,2,9,10,11,16})],none,0⟩,
⟨{0,3,5,10,13},{4},{0,3,5},{4},[(4,{1,2,6,7,8,16})],none,0⟩,
⟨{0,1,5,12,13},{2},{0,1,5},{2},[(2,{3,4,8,11,14,15})],none,0⟩,
⟨{0,1,3,4,14},{15},{3,4,14},{15},[(15,{2,6,7,8,9,10,11,16})],none,0⟩,
⟨{1,3,4,8,14},{5},{1,3,4},{5},[(5,{0,2,9,10,11,16})],none,0⟩,
⟨{0,3,4,11,14},{5},{0,3,4},{5},[(5,{1,2,6,7,8,16})],none,0⟩,
⟨{0,1,4,12,14},{2},{0,1,4},{2},[(2,{3,5,7,10,13,15})],none,0⟩,
⟨{0,1,3,13,14},{2},{0,1,3},{2},[(2,{4,5,6,9,12,15})],none,0⟩,
⟨{0,1,2,3,4,5},{15,16},∅,∅,[],none,0⟩,
⟨{2,5,6,7,9,10},{0,1},{2,5},{0,1},[(0,{1,3,4,8,14}),(1,{0,3,4,11,14})],none,0⟩,
⟨{2,4,6,8,9,11},{0,1},{2,4},{0,1},[(0,{1,3,5,7,13}),(1,{0,3,5,10,13})],none,0⟩,
⟨{2,3,7,8,10,11},{0,1},{2,3},{0,1},[(0,{1,4,5,6,12}),(1,{0,4,5,9,12})],none,0⟩,
⟨{1,5,6,7,12,13},{0,2},{1,5},{0,2},[(0,{2,3,4,8,11}),(2,{0,3,4,11,14})],none,0⟩,
⟨{0,5,9,10,12,13},{1,2},{0,5},{1,2},[(1,{2,3,4,8,11}),(2,{1,3,4,8,14})],none,0⟩,
⟨{5,7,9,10,12,13},{4},{5,9,12},{4},[(4,{0,1,2,16})],none,0⟩,
⟨{1,4,6,8,12,14},{0,2},{1,4},{0,2},[(0,{2,3,5,7,10}),(2,{0,3,5,10,13})],none,0⟩,
⟨{0,4,9,11,12,14},{1,2},{0,4},{1,2},[(1,{2,3,5,7,10}),(2,{1,3,5,7,13})],none,0⟩,
⟨{4,8,9,11,12,14},{5},{4,9,12},{5},[(5,{0,1,2,16})],none,0⟩,
⟨{1,3,7,8,13,14},{0,2},{1,3},{0,2},[(0,{2,4,5,6,9}),(2,{0,4,5,9,12})],none,0⟩,
⟨{0,3,10,11,13,14},{1,2},{0,3},{1,2},[(1,{2,4,5,6,9}),(2,{1,4,5,6,12})],none,0⟩,
⟨{3,8,10,11,13,14},{5},{3,10,13},{5},[(5,{0,1,2,16})],none,0⟩,
⟨{4,5,6,9,12,15},{3},{4,5,15},{3},[(3,{0,1,2,16})],none,0⟩,
⟨{3,5,7,10,13,15},{4},{3,5,15},{4},[(4,{0,1,2,16})],none,0⟩,
⟨{3,4,8,11,14,15},{5},{3,4,15},{5},[(5,{0,1,2,16})],none,0⟩,
⟨{1,2,6,7,8,16},{0},{1,2,16},{0},[(0,{3,4,5,15})],none,0⟩,
⟨{0,2,9,10,11,16},{1},{0,2,16},{1},[(1,{3,4,5,15})],none,0⟩,
⟨{0,1,12,13,14,16},{2},{0,1,16},{2},[(2,{3,4,5,15})],none,0⟩,
⟨{5,6,7,9,10,12,13},{0,3},{5,10,13},{0,3},[(0,{3,4,8,11,14,15}),(3,{0,1,2,16})],(some 6),35⟩,
⟨{7,8,9,10,11,12,13},{1,4},{8,12},{1,4},[(1,{3,4,5,15}),(4,{0,1,2,16})],none,0⟩,
⟨{4,6,8,9,11,12,14},{0,3},{4,11,14},{0,3},[(0,{3,5,7,10,13,15}),(3,{0,1,2,16})],(some 6),38⟩,
⟨{7,8,9,10,11,12,14},{1,5},{7,12},{1,5},[(1,{3,4,5,15}),(5,{0,1,2,16})],none,0⟩,
⟨{3,7,8,10,11,13,14},{0,4},{3,11,14},{0,4},[(0,{4,5,6,9,12,15}),(4,{0,1,2,16})],(some 7),41⟩,
⟨{6,8,9,10,11,13,14},{1,5},{6,13},{1,5},[(1,{3,4,5,15}),(5,{0,1,2,16})],none,0⟩,
⟨{7,8,9,10,12,13,14},{2,4},{8,9},{2,4},[(2,{3,4,5,15}),(4,{0,1,2,16})],none,0⟩,
⟨{7,8,9,11,12,13,14},{2,5},{7,9},{2,5},[(2,{3,4,5,15}),(5,{0,1,2,16})],none,0⟩,
⟨{6,7,10,11,12,13,14},{2,4},{6,11},{2,4},[(2,{3,4,5,15}),(4,{0,1,2,16})],none,0⟩,
⟨{6,8,10,11,12,13,14},{2,5},{6,10},{2,5},[(2,{3,4,5,15}),(5,{0,1,2,16})],none,0⟩,
⟨{2,7,8,9,10,11,16},{1,4},{2,8},{1,4},[(1,{3,4,5,15}),(4,{0,1,3,13,14})],none,0⟩,
⟨{1,7,8,12,13,14,16},{2,4},{1,8},{2,4},[(2,{3,4,5,15}),(4,{0,2,3,10,11})],none,0⟩,
⟨{0,10,11,12,13,14,16},{2,4},{0,11},{2,4},[(2,{3,4,5,15}),(4,{1,2,3,7,8})],none,0⟩,
⟨{6,7,8,9,10,11,12,13},{0,3},{10,11,13},{0,3},[(0,{3,4,5,15}),(3,{0,1,2,16})],(some 6),49⟩,
⟨{6,7,8,9,10,11,12,14},{0,3},{10,11,14},{0,3},[(0,{3,4,5,15}),(3,{0,1,2,16})],(some 6),51⟩,
⟨{6,7,8,9,10,11,13,14},{0,4},{9,11,14},{0,4},[(0,{3,4,5,15}),(4,{0,1,2,16})],(some 7),53⟩,
⟨{6,7,8,9,10,12,13,14},{0,3},{10,13,14},{0,3},[(0,{3,4,5,15}),(3,{0,1,2,16})],(some 6),54⟩,
⟨{6,7,8,9,11,12,13,14},{0,3},{11,13,14},{0,3},[(0,{3,4,5,15}),(3,{0,1,2,16})],(some 6),55⟩,
⟨{6,7,8,10,11,12,13,14},{0,4},{11,12,14},{0,4},[(0,{3,4,5,15}),(4,{0,1,2,16})],(some 7),57⟩,
⟨{6,7,9,10,11,12,13,14},{1,3},{7,13,14},{1,3},[(1,{3,4,5,15}),(3,{0,1,2,16})],(some 9),56⟩,
⟨{6,8,9,10,11,12,13,14},{1,3},{8,13,14},{1,3},[(1,{3,4,5,15}),(3,{0,1,2,16})],(some 9),57⟩,
⟨{7,8,9,10,11,12,13,14},{1,4},{8,12,14},{1,4},[(1,{3,4,5,15}),(4,{0,1,2,16})],(some 10),55⟩,
⟨{5,6,7,9,10,12,13,15},{0,1},{5,12,13},{0,1},[(0,{1,3,4,8,14}),(1,{0,3,4,11,14})],(some 15),48⟩,
⟨{4,6,8,9,11,12,14,15},{0,1},{4,12,14},{0,1},[(0,{1,3,5,7,13}),(1,{0,3,5,10,13})],(some 15),50⟩,
⟨{3,7,8,10,11,13,14,15},{0,1},{3,13,14},{0,1},[(0,{1,4,5,6,12}),(1,{0,4,5,9,12})],(some 15),52⟩,
⟨{2,6,7,8,9,10,11,16},{0,3},{2,10,11},{0,3},[(0,{3,4,5,15}),(3,{0,1,4,12,14})],(some 6),58⟩,
⟨{1,6,7,8,12,13,14,16},{0,3},{1,13,14},{0,3},[(0,{3,4,5,15}),(3,{0,2,4,9,11})],(some 6),59⟩,
⟨{0,9,10,11,12,13,14,16},{1,3},{0,13,14},{1,3},[(1,{3,4,5,15}),(3,{1,2,4,6,8})],(some 9),60⟩,
⟨{6,7,8,9,10,11,12,13,16},{3,4,5},∅,{5},[(5,{0,1,3,4,14})],(some 16),61⟩,
⟨{6,7,8,9,10,11,12,14,16},{3,4,5},∅,{4},[(4,{0,1,3,5,13})],(some 16),62⟩,
⟨{6,7,8,9,10,11,13,14,16},{3,4,5},∅,{3},[(3,{0,1,4,5,12})],(some 16),63⟩,
⟨{6,7,8,9,10,12,13,14,16},{3,4,5},∅,{5},[(5,{0,2,3,4,11})],(some 16),64⟩,
⟨{6,7,8,9,11,12,13,14,16},{3,4,5},∅,{4},[(4,{0,2,3,5,10})],(some 16),65⟩,
⟨{6,7,8,10,11,12,13,14,16},{3,4,5},∅,{3},[(3,{0,2,4,5,9})],(some 16),66⟩,
⟨{6,7,9,10,11,12,13,14,16},{3,4,5},∅,{5},[(5,{1,2,3,4,8})],(some 16),67⟩,
⟨{6,8,9,10,11,12,13,14,16},{3,4,5},∅,{4},[(4,{1,2,3,5,7})],(some 16),68⟩,
⟨{7,8,9,10,11,12,13,14,16},{3,4,5},∅,{3},[(3,{1,2,4,5,6})],(some 16),69⟩,
⟨{6,7,8,9,10,11,12,13,15,16},{0,1,2},{16},{2},[(2,{0,1,3,4,14})],(some 15),76⟩,
⟨{6,7,8,9,10,11,12,14,15,16},{0,1,2},{16},{2},[(2,{0,1,3,5,13})],(some 15),77⟩,
⟨{6,7,8,9,10,11,13,14,15,16},{0,1,2},{16},{2},[(2,{0,1,4,5,12})],(some 15),78⟩,
⟨{6,7,8,9,10,12,13,14,15,16},{0,1,2},{16},{1},[(1,{0,2,3,4,11})],(some 15),79⟩,
⟨{6,7,8,9,11,12,13,14,15,16},{0,1,2},{16},{1},[(1,{0,2,3,5,10})],(some 15),80⟩,
⟨{6,7,8,10,11,12,13,14,15,16},{0,1,2},{16},{1},[(1,{0,2,4,5,9})],(some 15),81⟩,
⟨{6,7,9,10,11,12,13,14,15,16},{0,1,2},{16},{0},[(0,{1,2,3,4,8})],(some 15),82⟩,
⟨{6,8,9,10,11,12,13,14,15,16},{0,1,2},{16},{0},[(0,{1,2,3,5,7})],(some 15),83⟩,
⟨{7,8,9,10,11,12,13,14,15,16},{0,1,2},{16},{0},[(0,{1,2,4,5,6})],(some 15),84⟩]
def node (i : Nat) : Node := (tree[i]?).getD default
def valid (i : Nat) : Bool :=
  let r := node i
  verifies r.Z r.T r.U r.H r.A && (match r.mark with
    | none => decide (r.U.card+2*r.T.card≤4+r.H.card)
    | some z => decide ((r.U.card+2*r.T.card+1≤4+r.H.card+(nbr z∩r.T).card) ∧ (r.child < i) ∧ r.Z.erase z=(node r.child).Z))
private theorem dataOK : ∀ i : Fin 94, valid i.val=true := by decide +kernel
theorem checked (i : Nat) (hi : i<94) : Good 4 (node i).Z := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have both := Bool.and_eq_true_iff.mp (dataOK ⟨i,hi⟩)
    have dat := verifies_sound both.1
    cases m : (node i).mark with
    | none =>
      have yes := both.2
      simp only [m] at yes
      exact .done _ _ _ _ _ dat (of_decide_eq_true yes)
    | some z =>
      have yes := both.2
      simp only [m] at yes
      obtain ⟨pr,lt,eqn⟩ := of_decide_eq_true yes
      exact .pivot _ _ _ _ _ z dat pr (eqn.symm ▸ ih _ lt (by omega))
def indices : Array Nat := #[0,75,74,47,73,46,45,1,72,40,39,28,32,16,7,29,71,37,36,27,31,15,6,29,44,26,25,24,14,13,5,29,70,34,33,23,30,12,4,29,43,22,21,20,11,10,3,29,42,19,18,17,9,8,2,29,0,29,29,29,29,29,29,29]
def whereIs (S : Finset L) := (indices[key S]?).getD 0
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem covering : ∀ S : Finset L, S.Nonempty → whereIs S<94 ∧ panel S⊆(node (whereIs S)).Z := by decide +kernel
def spare (i : Fin 9) : Nat := (#[93,92,91,90,89,88,87,86,85] : Array Nat)[i.val]!
def cell (i : Fin 9) : V := ⟨6+i.val,by omega⟩
theorem pure : ∀ i : Fin 9, spare i<94 ∧ (panel ∅).erase (cell i) ⊆ (node (spare i)).Z := by decide +kernel
end Cap4
def leftSet (D : Dag) : Finset L := Finset.univ.filter fun l => line l∈ineligSet 17 D
theorem in_panel (D : Dag) (ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j) :
    ineligSet 17 D⊆panel (leftSet D) := by
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_cases lo : v.val<6
  · let l : L := ⟨v.val,lo⟩
    have e : v=line l := rfl
    exact Or.inl ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e ▸ hv⟩,e⟩
  · exact Or.inr ⟨by omega,fun l hl => ind v hv _ (Finset.mem_filter.mp hl).2⟩

theorem strict28 {D : Dag} (live : StrictLive 17 D) (correct : sem_Comp 17 G D)
    (ind : ∀ i∈ineligSet 17 D,∀ j∈ineligSet 17 D, ¬G i j) :
    28+Bzero 17 D≤D.length := by
  have c := Cap5.covering (leftSet D)
  have z := panelBound regular live correct ((in_panel D ind).trans c.2) (Cap5.checked _ c.1)
  omega

theorem strict29 {D : Dag} (live : StrictLive 17 D) (correct : sem_Comp 17 G D)
    (ind : ∀ i∈ineligSet 17 D,∀ j∈ineligSet 17 D, ¬G i j)
    (ex : (leftSet D).Nonempty ∨ ∃ i : Fin 9, Cap4.cell i∉ineligSet 17 D) :
    29+Bzero 17 D≤D.length := by
  classical
  by_cases h : (leftSet D).Nonempty
  · have c := Cap4.covering (leftSet D) h
    have z := panelBound regular live correct ((in_panel D ind).trans c.2) (Cap4.checked _ c.1)
    omega
  · obtain ⟨i,hi⟩ := ex.resolve_left h
    have eq : leftSet D=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have sub := in_panel D ind
    rw [eq] at sub
    have incl : ineligSet 17 D ⊆ (panel ∅).erase (Cap4.cell i) := fun v hv => Finset.mem_erase.mpr ⟨fun e => hi (e ▸ hv),sub hv⟩
    have c := Cap4.pure i
    have z := panelBound regular live correct (incl.trans c.2) (Cap4.checked _ c.1)
    omega
theorem finish     (C : Circuit) (hm : Monotone2 C) (correct : ∀ x : V → Bool,
      C.eval (List.ofFn x)=true ↔ sem_Edge G x) : 28≤C.size := by
  have hG := regular
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
  obtain ⟨D,ld,lim,simulation⟩ := normalize_strictLive (n:=17) C hm
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
  have sem : sem_Comp 17 G D := fun x => by rw [simulation x]; exact correct x
  have ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover hG ld sem ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have z := strict28 ld sem ind
  omega

def mask (m : Nat) : Finset V := Finset.univ.filter fun i => m.testBit i.val
def together (I : Finset V) (marked : Bool) (p q : V) : Prop :=
  (∃i∈I,G i p ∧ G i q) ∨ (marked=true ∧ (p=15 ∧ q=16 ∨ p=16 ∧ q=15))
instance (I : Finset V) (m : Bool) (p q : V) : Decidable (together I m p q) := by unfold together; infer_instance

def forest : List (V × Option V) → Finset V → Finset V → Bool → Bool
  | [],_,_,_ => true
  | (p,k)::l,A,I,b => decide (p∉A) && (match k with
    | none => true
    | some q => decide (q∈A ∧ together I b p q)) && forest l (insert p A) I b

def many (l : List (V × Option V)) := l.countP (fun e => e.2.isSome)
def collect (l : List (V × Option V)) : Finset V := (l.map Prod.fst).toFinset

theorem forest_bound {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D) (marked : Bool)
    (hw : marked=true → ∃w, (15:V)∈supp 17 D w ∧ (16:V)∈supp 17 D w)
    (I : Finset V) (inc : I⊆ineligSet 17 D) (l : List (V × Option V)) (A : Finset V)
    (valid : forest l A I marked=true) :
    (merges 17 D (carrierT 17 D A)).card + many l ≤ (merges 17 D (carrierT 17 D (A ∪ collect l))).card := by
  classical
  induction l generalizing A with
  | nil => simp [many,collect]
  | cons e l ih =>
    rcases e with ⟨p,k⟩
    have both := (Bool.and_eq_true_iff.mp valid)
    have first := (Bool.and_eq_true_iff.mp both.1)
    have np : p∉A := of_decide_eq_true first.1
    have tail := ih (insert p A) both.2
    have eq : insert p A ∪ collect l = A ∪ collect ((p,k)::l) := by ext z; simp [collect]
    rw [eq] at tail
    cases k with
    | none =>
      have le := Finset.card_le_card (merges_mono (D:=D) (Finset.subset_insert p A))
      simp [many,List.countP_cons] at tail ⊢
      omega
    | some q =>
      have data : q∈A ∧ together I marked p q := of_decide_eq_true first.2
      have existsW : ∃w, p∈supp 17 D w ∧ q∈supp 17 D w := by
        rcases data.2 with ⟨v,hv,a,b⟩|⟨hm,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
        · obtain ⟨pos,hp⟩ := k4_assigned regular live corr
          exact ⟨src D (pos v), (hp.1 v (inc hv)).2.2.1 _ a, (hp.1 v (inc hv)).2.2.1 _ b⟩
        · exact hw hm
        · obtain ⟨w,a,b⟩ := hw hm
          exact ⟨w,b,a⟩
      obtain ⟨w,pp,qq⟩ := existsW
      have step := PEqualNP.Outside.L_meta_18910.Merge.step live.1 np pp ⟨q,Finset.mem_inter.mpr ⟨qq,data.1⟩⟩
      simp [many,List.countP_cons] at tail ⊢
      omega

structure ProofRow where
  upper : Nat
  must : Nat
  ts : List (V × Option V)
  spare : Nat
  priv : Nat
  exp : List (V × Nat)
deriving Inhabited

def ProofRow.A (r : ProofRow) (u : V) := mask ((r.exp.lookup u).getD 0)
def ProofRow.valid (r : ProofRow) (m : Bool) (k : Nat) : Bool :=
  verifies (mask r.upper) (collect r.ts) (mask r.spare) (mask r.priv) r.A &&
  forest r.ts ∅ (mask r.must) m &&
  decide ((mask r.spare).card+2*(collect r.ts).card ≤ k+(mask r.priv).card+many r.ts)

theorem applyRow {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
    (m : Bool) (hw : m=true → ∃w, (15:V)∈supp 17 D w ∧ (16:V)∈supp 17 D w)
    (k : Nat) (r : ProofRow) (c : r.valid m k=true)
    (lo : mask r.must ⊆ ineligSet 17 D) (hi : ineligSet 17 D ⊆ mask r.upper) :
    33+Bzero 17 D ≤ D.length+k := by
  have ⟨a,z⟩ := Bool.and_eq_true_iff.mp c
  have ⟨v,b⟩ := Bool.and_eq_true_iff.mp a
  have bound := charge regular live corr hi (verifies_sound v)
  have forest := forest_bound live corr m hw _ lo _ _ b
  rw [Finset.empty_union] at forest
  have p := of_decide_eq_true z
  omega
namespace Scalar
def data : Array ProofRow := #[
⟨15,0,[],15,0,[]⟩,
⟨23,0,[],23,0,[]⟩,
⟨39,0,[],39,0,[]⟩,
⟨57,0,[],57,0,[]⟩,
⟨58,0,[],58,0,[]⟩,
⟨60,0,[],60,0,[]⟩,
⟨32824,0,[],32824,0,[]⟩,
⟨65543,0,[],65543,0,[]⟩,
⟨31,0,[(16,none)],7,65536,[(16,46816)]⟩,
⟨47,0,[(16,none)],7,65536,[(16,56144)]⟩,
⟨55,0,[(16,none)],7,65536,[(16,60808)]⟩,
⟨59,0,[(16,none)],3,0,[]⟩,
⟨61,0,[(16,none)],5,0,[]⟩,
⟨62,0,[(16,none)],6,0,[]⟩,
⟨118,0,[(16,none)],70,65536,[(16,60808)]⟩,
⟨174,0,[(16,none)],134,65536,[(16,56144)]⟩,
⟨230,0,[(0,none)],38,1,[(0,51480)]⟩,
⟨286,0,[(16,none)],262,65536,[(16,46816)]⟩,
⟨342,0,[(0,none)],22,1,[(0,42152)]⟩,
⟨398,0,[(0,none)],14,1,[(0,37488)]⟩,
⟨565,0,[(16,none)],517,65536,[(16,60808)]⟩,
⟨628,0,[(16,none)],580,65536,[(16,60808)]⟩,
⟨1069,0,[(16,none)],1029,65536,[(16,56144)]⟩,
⟨1196,0,[(16,none)],1156,65536,[(16,56144)]⟩,
⟨1252,0,[(0,none)],1060,1,[(0,51480)]⟩,
⟨1573,0,[(15,none)],1568,32768,[(15,94658)]⟩,
⟨2077,0,[(16,none)],2053,65536,[(16,46816)]⟩,
⟨2332,0,[(16,none)],2308,65536,[(16,46816)]⟩,
⟨2388,0,[(0,none)],2068,1,[(0,42152)]⟩,
⟨2581,0,[(15,none)],2576,32768,[(15,94658)]⟩,
⟨3085,0,[(15,none)],3080,32768,[(15,94658)]⟩,
⟨3340,0,[(5,none)],1036,32,[(5,94211)]⟩,
⟨4147,0,[(16,none)],4099,65536,[(16,60808)]⟩,
⟨4210,0,[(16,none)],4162,65536,[(16,60808)]⟩,
⟨4657,0,[(16,none)],4609,65536,[(16,60808)]⟩,
⟨8235,0,[(16,none)],8195,65536,[(16,56144)]⟩,
⟨8362,0,[(16,none)],8322,65536,[(16,56144)]⟩,
⟨8418,0,[(0,none)],8226,1,[(0,51480)]⟩,
⟨8586,0,[(0,none)],8202,1,[(0,37488)]⟩,
⟨9257,0,[(16,none)],9217,65536,[(16,56144)]⟩,
⟨11273,0,[(4,none)],2057,16,[(4,65990)]⟩,
⟨12323,0,[(15,none)],12320,32768,[(15,69572)]⟩,
⟨13345,0,[(4,none)],4129,16,[(4,65990)]⟩,
⟨16411,0,[(16,none)],16387,65536,[(16,46816)]⟩,
⟨16666,0,[(16,none)],16642,65536,[(16,46816)]⟩,
⟨16722,0,[(0,none)],16402,1,[(0,42152)]⟩,
⟨18457,0,[(16,none)],18433,65536,[(16,46816)]⟩,
⟨20499,0,[(15,none)],20496,32768,[(15,69572)]⟩,
⟨22545,0,[(5,none)],4113,32,[(5,65990)]⟩,
⟨24587,0,[(15,none)],24584,32768,[(15,69572)]⟩,
⟨63,0,[(15,none),(16,none)],0,0,[]⟩,
⟨1764,512,[(1,none),(3,some 1)],164,10,[(1,51480),(3,94211)]⟩,
⟨2900,512,[(1,none),(3,some 1)],276,10,[(1,42152),(3,94211)]⟩,
⟨3468,128,[(0,none),(4,some 0)],2060,17,[(0,37488),(4,94211)]⟩,
⟨3524,0,[(0,none)],3076,1,[(0,32824)]⟩,
⟨7616,0,[(0,none)],7168,1,[(0,32824)]⟩,
⟨11200,0,[(0,none)],10752,1,[(0,32824)]⟩,
⟨12514,4096,[(2,none),(3,some 2)],162,12,[(2,51480),(3,69125)]⟩,
⟨13857,512,[(1,none),(3,some 1)],8225,10,[(1,51480),(3,65990)]⟩,
⟨14784,0,[(0,none)],14336,1,[(0,32824)]⟩,
⟨15744,0,[(4,none)],6400,16,[(4,65543)]⟩,
⟨20818,4096,[(2,none),(3,some 2)],274,12,[(2,42152),(3,69125)]⟩,
⟨21952,0,[(0,none)],21504,1,[(0,32824)]⟩,
⟨22976,0,[(0,none)],22528,1,[(0,32824)]⟩,
⟨23057,512,[(1,none),(3,some 1)],16401,10,[(1,42152),(3,65990)]⟩,
⟨24970,16384,[(2,none),(5,some 2)],138,36,[(2,37488),(5,69125)]⟩,
⟨27657,16384,[(2,none),(5,some 2)],1033,36,[(2,37488),(5,65990)]⟩,
⟨27840,0,[(4,none)],18496,16,[(4,65543)]⟩,
⟨27968,0,[(5,none)],9280,32,[(5,65543)]⟩,
⟨37488,0,[(3,none)],32816,8,[(3,65543)]⟩,
⟨42152,0,[(4,none)],32808,16,[(4,65543)]⟩,
⟨42208,0,[(0,none)],9248,1,[(0,16666)]⟩,
⟨51480,0,[(5,none)],32792,32,[(5,65543)]⟩,
⟨51536,0,[(0,none)],18448,1,[(0,8362)]⟩,
⟨65990,0,[(0,none)],65542,1,[(0,32824)]⟩,
⟨69125,0,[(1,none)],65541,2,[(1,32824)]⟩,
⟨74178,0,[(0,none)],73730,1,[(0,32824)]⟩,
⟨76672,0,[(4,none)],2816,16,[(4,3085)]⟩,
⟨76992,0,[(4,none)],2112,0,[]⟩,
⟨77120,0,[(4,none)],2368,16,[(4,398)]⟩,
⟨92352,0,[(4,none)],18496,16,[(4,3085)]⟩,
⟨92480,0,[(5,none)],8256,0,[]⟩,
⟨93185,0,[(4,none)],18433,16,[(4,398)]⟩,
⟨94211,0,[(2,none)],65539,4,[(2,32824)]⟩,
⟨15296,512,[(1,none),(3,some 1)],8576,10,[(1,42152),(3,65543)]⟩,
⟨15808,0,[(0,none),(4,none)],6144,17,[(0,32824),(4,65543)]⟩,
⟨16256,512,[(1,none),(3,some 1)],8576,10,[(1,32824),(3,65990)]⟩,
⟨22464,512,[(1,none),(3,some 1)],16768,10,[(1,51480),(3,65543)]⟩,
⟨23488,512,[(1,none),(3,some 1)],16768,10,[(1,42152),(3,65543)]⟩,
⟨24000,16384,[(2,none),(5,some 2)],1216,36,[(2,42152),(5,65543)]⟩,
⟨26560,0,[(0,none),(4,none)],16896,17,[(0,32824),(4,65543)]⟩,
⟨27584,16384,[(2,none),(5,some 2)],704,36,[(2,37488),(5,65543)]⟩,
⟨31936,4096,[(2,none),(3,some 2)],3200,12,[(2,32824),(3,69125)]⟩,
⟨32064,4096,[(2,none),(3,some 2)],3328,12,[(2,32824),(3,69125)]⟩,
⟨44424,0,[(0,none),(4,none)],2056,17,[(0,4210),(4,65543)]⟩,
⟨46304,4096,[(2,none),(3,some 2)],1184,12,[(2,18457),(3,69125)]⟩,
⟨55632,4096,[(2,none),(3,some 2)],2320,12,[(2,9257),(3,69125)]⟩,
⟨69060,65536,[(3,none),(5,some 3)],1156,40,[(3,13857),(5,24587)]⟩,
⟨81280,65536,[(3,none),(5,some 3)],9344,40,[(3,1764),(5,24587)]⟩,
⟨90562,16384,[(2,none),(5,some 2)],194,36,[(2,37488),(5,3085)]⟩,
⟨92864,512,[(1,none),(3,some 1)],24704,10,[(1,42152),(3,20499)]⟩,
⟨92992,512,[(1,none),(3,some 1)],24832,10,[(1,42152),(3,20499)]⟩,
⟨93056,16384,[(2,none),(5,some 2)],640,4,[(2,37488)]⟩,
⟨93376,16384,[(2,none),(5,some 2)],1216,36,[(2,37488),(5,398)]⟩,
⟨93504,16384,[(2,none),(5,some 2)],1088,4,[(2,37488)]⟩,
⟨97281,4096,[(2,none),(3,some 2)],3073,12,[(2,32824),(3,2900)]⟩,
⟨32448,512,[(1,none),(3,some 1)],24704,10,[(1,32824),(3,65543)]⟩,
⟨32576,512,[(1,none),(3,some 1)],24832,10,[(1,32824),(3,65543)]⟩,
⟨32640,16384,[(2,none),(5,some 2)],1664,36,[(2,32824),(5,65543)]⟩,
⟨46816,512,[(1,none),(3,some 1)],8352,10,[(1,18457),(3,65543)]⟩,
⟨56144,512,[(1,none),(3,some 1)],16656,10,[(1,9257),(3,65543)]⟩,
⟨60808,16384,[(2,none),(5,some 2)],1160,36,[(2,4657),(5,65543)]⟩,
⟨69572,512,[(1,none),(3,some 1)],388,10,[(1,32824),(3,20499)]⟩,
⟨80832,65536,[(3,none),(5,some 3)],8320,32,[(5,24587)]⟩,
⟨81344,65536,[(3,none),(5,some 3)],9344,40,[(3,1573),(5,24587)]⟩,
⟨88000,65536,[(3,none),(5,some 3)],1152,32,[(5,3085)]⟩,
⟨89024,65536,[(3,none),(5,some 3)],128,0,[]⟩,
⟨89536,65536,[(3,none),(5,some 3)],1152,8,[(3,1573)]⟩,
⟨92096,65536,[(3,none),(5,some 3)],9344,40,[(3,12323),(5,3085)]⟩,
⟨93120,65536,[(3,none),(5,some 3)],8320,8,[(3,12323)]⟩,
⟨93632,128,[(0,none),(4,some 0)],18432,1,[(0,32824)]⟩,
⟨94658,4096,[(2,none),(3,some 2)],386,12,[(2,32824),(3,2581)]⟩,
⟨96960,4096,[(2,none),(3,some 2)],2176,4,[(2,32824)]⟩,
⟨97088,4096,[(2,none),(3,some 2)],2304,4,[(2,32824)]⟩,
⟨97152,4096,[(2,none),(3,some 2)],2432,12,[(2,32824),(3,342)]⟩,
⟨97472,4096,[(2,none),(3,some 2)],3200,12,[(2,32824),(3,2581)]⟩,
⟨97600,4096,[(2,none),(3,some 2)],3328,12,[(2,32824),(3,2581)]⟩,
⟨97664,16384,[(2,none),(5,some 2)],1152,4,[(2,32824)]⟩,
⟨97793,512,[(1,none),(3,some 1)],24577,10,[(1,32824),(3,342)]⟩,
⟨32704,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,1,[(0,32824)]⟩,
⟨81856,1536,[(1,none),(3,some 1),(4,some 1)],256,2,[(1,32824)]⟩,
⟨90048,1536,[(1,none),(3,some 1),(4,some 1)],16640,18,[(1,32824),(4,24587)]⟩,
⟨94144,1536,[(1,none),(3,some 1),(4,some 1)],16640,10,[(1,32824),(3,20499)]⟩,
⟨96192,12288,[(2,none),(3,some 2),(4,some 2)],256,4,[(2,32824)]⟩,
⟨97216,12288,[(2,none),(3,some 2),(4,some 2)],2304,20,[(2,32824),(4,3085)]⟩,
⟨97728,12288,[(2,none),(3,some 2),(4,some 2)],2304,12,[(2,32824),(3,2581)]⟩,
⟨97984,1536,[(1,none),(3,some 1),(4,some 1)],16384,2,[(1,32824)]⟩,
⟨98112,1536,[(1,none),(3,some 1),(4,some 1)],16640,18,[(1,32824),(4,398)]⟩,
⟨98176,1536,[(1,none),(3,some 1),(4,some 1)],16640,10,[(1,32824),(3,342)]⟩,
⟨65472,32768,[(0,none),(1,some 0),(2,some 0)],0,0,[]⟩,
⟨98240,65536,[(3,none),(4,some 3),(5,some 3)],0,0,[]⟩,
⟨114624,32768,[(0,none),(1,some 0),(2,some 0)],65536,4,[(2,16411)]⟩,
⟨122816,32768,[(0,none),(1,some 0),(2,some 0)],65536,4,[(2,8235)]⟩,
⟨126912,32768,[(0,none),(1,some 0),(2,some 0)],65536,4,[(2,4147)]⟩,
⟨128960,32768,[(0,none),(1,some 0),(2,some 0)],65536,2,[(1,2077)]⟩,
⟨129984,32768,[(0,none),(1,some 0),(2,some 0)],65536,2,[(1,1069)]⟩,
⟨130496,32768,[(0,none),(1,some 0),(2,some 0)],65536,2,[(1,565)]⟩,
⟨130752,32768,[(0,none),(1,some 0),(2,some 0)],65536,1,[(0,286)]⟩,
⟨130880,32768,[(0,none),(1,some 0),(2,some 0)],65536,1,[(0,174)]⟩,
⟨130944,32768,[(0,none),(1,some 0),(2,some 0)],65536,1,[(0,118)]⟩]
def row (i : Nat) := (data[i]?).getD default
private theorem ok0 : ∀ j : Fin 8, (row (0+j.val)).valid false 4=true := by decide +kernel
private theorem ok8 : ∀ j : Fin 8, (row (8+j.val)).valid false 4=true := by decide +kernel
private theorem ok16 : ∀ j : Fin 8, (row (16+j.val)).valid false 4=true := by decide +kernel
private theorem ok24 : ∀ j : Fin 8, (row (24+j.val)).valid false 4=true := by decide +kernel
private theorem ok32 : ∀ j : Fin 8, (row (32+j.val)).valid false 4=true := by decide +kernel
private theorem ok40 : ∀ j : Fin 8, (row (40+j.val)).valid false 4=true := by decide +kernel
private theorem ok48 : ∀ j : Fin 8, (row (48+j.val)).valid false 4=true := by decide +kernel
private theorem ok56 : ∀ j : Fin 8, (row (56+j.val)).valid false 4=true := by decide +kernel
private theorem ok64 : ∀ j : Fin 8, (row (64+j.val)).valid false 4=true := by decide +kernel
private theorem ok72 : ∀ j : Fin 8, (row (72+j.val)).valid false 4=true := by decide +kernel
private theorem ok80 : ∀ j : Fin 8, (row (80+j.val)).valid false 4=true := by decide +kernel
private theorem ok88 : ∀ j : Fin 8, (row (88+j.val)).valid false 4=true := by decide +kernel
private theorem ok96 : ∀ j : Fin 8, (row (96+j.val)).valid false 4=true := by decide +kernel
private theorem ok104 : ∀ j : Fin 8, (row (104+j.val)).valid false 4=true := by decide +kernel
private theorem ok112 : ∀ j : Fin 8, (row (112+j.val)).valid false 4=true := by decide +kernel
private theorem ok120 : ∀ j : Fin 8, (row (120+j.val)).valid false 4=true := by decide +kernel
private theorem ok128 : ∀ j : Fin 8, (row (128+j.val)).valid false 4=true := by decide +kernel
private theorem ok136 : ∀ j : Fin 8, (row (136+j.val)).valid false 4=true := by decide +kernel
private theorem ok144 : ∀ j : Fin 6, (row (144+j.val)).valid false 4=true := by decide +kernel
variable {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
variable (hw : false=true → ∃w, (15:V)∈supp 17 D w ∧ (16:V)∈supp 17 D w) (ne : ineligSet 17 D ≠ mask 131008)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15 (hi : ineligSet 17 D⊆mask 15) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 0) (ok0 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23 (hi : ineligSet 17 D⊆mask 23) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 1) (ok0 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c39 (hi : ineligSet 17 D⊆mask 39) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 2) (ok0 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c57 (hi : ineligSet 17 D⊆mask 57) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 3) (ok0 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c58 (hi : ineligSet 17 D⊆mask 58) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 4) (ok0 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c60 (hi : ineligSet 17 D⊆mask 60) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 5) (ok0 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32824 (hi : ineligSet 17 D⊆mask 32824) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 6) (ok0 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c65543 (hi : ineligSet 17 D⊆mask 65543) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 7) (ok0 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31 (hi : ineligSet 17 D⊆mask 31) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 8) (ok8 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c47 (hi : ineligSet 17 D⊆mask 47) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 9) (ok8 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c55 (hi : ineligSet 17 D⊆mask 55) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 10) (ok8 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c59 (hi : ineligSet 17 D⊆mask 59) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 11) (ok8 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c61 (hi : ineligSet 17 D⊆mask 61) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 12) (ok8 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c62 (hi : ineligSet 17 D⊆mask 62) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 13) (ok8 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c118 (hi : ineligSet 17 D⊆mask 118) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 14) (ok8 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c174 (hi : ineligSet 17 D⊆mask 174) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 15) (ok8 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c230 (hi : ineligSet 17 D⊆mask 230) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 16) (ok16 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c286 (hi : ineligSet 17 D⊆mask 286) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 17) (ok16 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c342 (hi : ineligSet 17 D⊆mask 342) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 18) (ok16 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c398 (hi : ineligSet 17 D⊆mask 398) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 19) (ok16 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c565 (hi : ineligSet 17 D⊆mask 565) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 20) (ok16 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c628 (hi : ineligSet 17 D⊆mask 628) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 21) (ok16 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1069 (hi : ineligSet 17 D⊆mask 1069) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 22) (ok16 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1196 (hi : ineligSet 17 D⊆mask 1196) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 23) (ok16 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1252 (hi : ineligSet 17 D⊆mask 1252) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 24) (ok24 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1573 (hi : ineligSet 17 D⊆mask 1573) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 25) (ok24 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2077 (hi : ineligSet 17 D⊆mask 2077) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 26) (ok24 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2332 (hi : ineligSet 17 D⊆mask 2332) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 27) (ok24 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2388 (hi : ineligSet 17 D⊆mask 2388) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 28) (ok24 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2581 (hi : ineligSet 17 D⊆mask 2581) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 29) (ok24 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3085 (hi : ineligSet 17 D⊆mask 3085) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 30) (ok24 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3340 (hi : ineligSet 17 D⊆mask 3340) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 31) (ok24 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4147 (hi : ineligSet 17 D⊆mask 4147) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 32) (ok32 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4210 (hi : ineligSet 17 D⊆mask 4210) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 33) (ok32 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4657 (hi : ineligSet 17 D⊆mask 4657) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 34) (ok32 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8235 (hi : ineligSet 17 D⊆mask 8235) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 35) (ok32 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8362 (hi : ineligSet 17 D⊆mask 8362) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 36) (ok32 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8418 (hi : ineligSet 17 D⊆mask 8418) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 37) (ok32 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8586 (hi : ineligSet 17 D⊆mask 8586) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 38) (ok32 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9257 (hi : ineligSet 17 D⊆mask 9257) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 39) (ok32 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11273 (hi : ineligSet 17 D⊆mask 11273) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 40) (ok40 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12323 (hi : ineligSet 17 D⊆mask 12323) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 41) (ok40 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c13345 (hi : ineligSet 17 D⊆mask 13345) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 42) (ok40 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16411 (hi : ineligSet 17 D⊆mask 16411) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 43) (ok40 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16666 (hi : ineligSet 17 D⊆mask 16666) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 44) (ok40 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16722 (hi : ineligSet 17 D⊆mask 16722) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 45) (ok40 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18457 (hi : ineligSet 17 D⊆mask 18457) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 46) (ok40 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20499 (hi : ineligSet 17 D⊆mask 20499) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 47) (ok40 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c22545 (hi : ineligSet 17 D⊆mask 22545) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 48) (ok48 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24587 (hi : ineligSet 17 D⊆mask 24587) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 49) (ok48 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c63 (hi : ineligSet 17 D⊆mask 63) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 50) (ok48 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1764 (hi : ineligSet 17 D⊆mask 1764) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c1252 live corr hw ne
    intro v hv
    have vv : v∈mask 1764 := hi hv
    have reduced : ∀ a:V, a∈mask 1764 → a≠9 → a∈mask 1252 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 51) (ok48 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2900 (hi : ineligSet 17 D⊆mask 2900) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c2388 live corr hw ne
    intro v hv
    have vv : v∈mask 2900 := hi hv
    have reduced : ∀ a:V, a∈mask 2900 → a≠9 → a∈mask 2388 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 52) (ok48 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3468 (hi : ineligSet 17 D⊆mask 3468) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c3340 live corr hw ne
    intro v hv
    have vv : v∈mask 3468 := hi hv
    have reduced : ∀ a:V, a∈mask 3468 → a≠7 → a∈mask 3340 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 53) (ok48 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3524 (hi : ineligSet 17 D⊆mask 3524) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 54) (ok48 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c7616 (hi : ineligSet 17 D⊆mask 7616) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 55) (ok48 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11200 (hi : ineligSet 17 D⊆mask 11200) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 56) (ok56 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12514 (hi : ineligSet 17 D⊆mask 12514) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c8418 live corr hw ne
    intro v hv
    have vv : v∈mask 12514 := hi hv
    have reduced : ∀ a:V, a∈mask 12514 → a≠12 → a∈mask 8418 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 57) (ok56 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c13857 (hi : ineligSet 17 D⊆mask 13857) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c13345 live corr hw ne
    intro v hv
    have vv : v∈mask 13857 := hi hv
    have reduced : ∀ a:V, a∈mask 13857 → a≠9 → a∈mask 13345 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 58) (ok56 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c14784 (hi : ineligSet 17 D⊆mask 14784) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 59) (ok56 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15744 (hi : ineligSet 17 D⊆mask 15744) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 60) (ok56 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20818 (hi : ineligSet 17 D⊆mask 20818) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c16722 live corr hw ne
    intro v hv
    have vv : v∈mask 20818 := hi hv
    have reduced : ∀ a:V, a∈mask 20818 → a≠12 → a∈mask 16722 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 61) (ok56 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c21952 (hi : ineligSet 17 D⊆mask 21952) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 62) (ok56 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c22976 (hi : ineligSet 17 D⊆mask 22976) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 63) (ok56 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23057 (hi : ineligSet 17 D⊆mask 23057) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c22545 live corr hw ne
    intro v hv
    have vv : v∈mask 23057 := hi hv
    have reduced : ∀ a:V, a∈mask 23057 → a≠9 → a∈mask 22545 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 64) (ok64 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24970 (hi : ineligSet 17 D⊆mask 24970) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c8586 live corr hw ne
    intro v hv
    have vv : v∈mask 24970 := hi hv
    have reduced : ∀ a:V, a∈mask 24970 → a≠14 → a∈mask 8586 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 65) (ok64 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27657 (hi : ineligSet 17 D⊆mask 27657) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11273 live corr hw ne
    intro v hv
    have vv : v∈mask 27657 := hi hv
    have reduced : ∀ a:V, a∈mask 27657 → a≠14 → a∈mask 11273 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 66) (ok64 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27840 (hi : ineligSet 17 D⊆mask 27840) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 67) (ok64 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27968 (hi : ineligSet 17 D⊆mask 27968) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 68) (ok64 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c37488 (hi : ineligSet 17 D⊆mask 37488) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 69) (ok64 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c42152 (hi : ineligSet 17 D⊆mask 42152) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 70) (ok64 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c42208 (hi : ineligSet 17 D⊆mask 42208) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 71) (ok64 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c51480 (hi : ineligSet 17 D⊆mask 51480) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 72) (ok72 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c51536 (hi : ineligSet 17 D⊆mask 51536) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 73) (ok72 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c65990 (hi : ineligSet 17 D⊆mask 65990) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 74) (ok72 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c69125 (hi : ineligSet 17 D⊆mask 69125) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 75) (ok72 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c74178 (hi : ineligSet 17 D⊆mask 74178) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 76) (ok72 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c76672 (hi : ineligSet 17 D⊆mask 76672) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 77) (ok72 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c76992 (hi : ineligSet 17 D⊆mask 76992) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 78) (ok72 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c77120 (hi : ineligSet 17 D⊆mask 77120) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 79) (ok72 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c92352 (hi : ineligSet 17 D⊆mask 92352) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 80) (ok80 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c92480 (hi : ineligSet 17 D⊆mask 92480) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 81) (ok80 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93185 (hi : ineligSet 17 D⊆mask 93185) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 82) (ok80 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c94211 (hi : ineligSet 17 D⊆mask 94211) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 83) (ok80 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15296 (hi : ineligSet 17 D⊆mask 15296) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c14784 live corr hw ne
    intro v hv
    have vv : v∈mask 15296 := hi hv
    have reduced : ∀ a:V, a∈mask 15296 → a≠9 → a∈mask 14784 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 84) (ok80 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15808 (hi : ineligSet 17 D⊆mask 15808) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 85) (ok80 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16256 (hi : ineligSet 17 D⊆mask 16256) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c15744 live corr hw ne
    intro v hv
    have vv : v∈mask 16256 := hi hv
    have reduced : ∀ a:V, a∈mask 16256 → a≠9 → a∈mask 15744 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 86) (ok80 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c22464 (hi : ineligSet 17 D⊆mask 22464) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c21952 live corr hw ne
    intro v hv
    have vv : v∈mask 22464 := hi hv
    have reduced : ∀ a:V, a∈mask 22464 → a≠9 → a∈mask 21952 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 87) (ok80 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23488 (hi : ineligSet 17 D⊆mask 23488) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c22976 live corr hw ne
    intro v hv
    have vv : v∈mask 23488 := hi hv
    have reduced : ∀ a:V, a∈mask 23488 → a≠9 → a∈mask 22976 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 88) (ok88 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24000 (hi : ineligSet 17 D⊆mask 24000) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c7616 live corr hw ne
    intro v hv
    have vv : v∈mask 24000 := hi hv
    have reduced : ∀ a:V, a∈mask 24000 → a≠14 → a∈mask 7616 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 89) (ok88 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c26560 (hi : ineligSet 17 D⊆mask 26560) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 90) (ok88 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27584 (hi : ineligSet 17 D⊆mask 27584) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11200 live corr hw ne
    intro v hv
    have vv : v∈mask 27584 := hi hv
    have reduced : ∀ a:V, a∈mask 27584 → a≠14 → a∈mask 11200 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 91) (ok88 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31936 (hi : ineligSet 17 D⊆mask 31936) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c27840 live corr hw ne
    intro v hv
    have vv : v∈mask 31936 := hi hv
    have reduced : ∀ a:V, a∈mask 31936 → a≠12 → a∈mask 27840 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 92) (ok88 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32064 (hi : ineligSet 17 D⊆mask 32064) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c27968 live corr hw ne
    intro v hv
    have vv : v∈mask 32064 := hi hv
    have reduced : ∀ a:V, a∈mask 32064 → a≠12 → a∈mask 27968 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 93) (ok88 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c44424 (hi : ineligSet 17 D⊆mask 44424) : 33+Bzero 17 D≤D.length+4 := by
  refine applyRow live corr false hw 4 (row 94) (ok88 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c46304 (hi : ineligSet 17 D⊆mask 46304) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c42208 live corr hw ne
    intro v hv
    have vv : v∈mask 46304 := hi hv
    have reduced : ∀ a:V, a∈mask 46304 → a≠12 → a∈mask 42208 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 95) (ok88 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c55632 (hi : ineligSet 17 D⊆mask 55632) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c51536 live corr hw ne
    intro v hv
    have vv : v∈mask 55632 := hi hv
    have reduced : ∀ a:V, a∈mask 55632 → a≠12 → a∈mask 51536 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 96) (ok96 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c69060 (hi : ineligSet 17 D⊆mask 69060) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c3524 live corr hw ne
    intro v hv
    have vv : v∈mask 69060 := hi hv
    have reduced : ∀ a:V, a∈mask 69060 → a≠16 → a∈mask 3524 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 97) (ok96 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c81280 (hi : ineligSet 17 D⊆mask 81280) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c15744 live corr hw ne
    intro v hv
    have vv : v∈mask 81280 := hi hv
    have reduced : ∀ a:V, a∈mask 81280 → a≠16 → a∈mask 15744 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 98) (ok96 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c90562 (hi : ineligSet 17 D⊆mask 90562) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c74178 live corr hw ne
    intro v hv
    have vv : v∈mask 90562 := hi hv
    have reduced : ∀ a:V, a∈mask 90562 → a≠14 → a∈mask 74178 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 99) (ok96 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c92864 (hi : ineligSet 17 D⊆mask 92864) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c92352 live corr hw ne
    intro v hv
    have vv : v∈mask 92864 := hi hv
    have reduced : ∀ a:V, a∈mask 92864 → a≠9 → a∈mask 92352 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 100) (ok96 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c92992 (hi : ineligSet 17 D⊆mask 92992) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c92480 live corr hw ne
    intro v hv
    have vv : v∈mask 92992 := hi hv
    have reduced : ∀ a:V, a∈mask 92992 → a≠9 → a∈mask 92480 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 101) (ok96 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93056 (hi : ineligSet 17 D⊆mask 93056) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c76672 live corr hw ne
    intro v hv
    have vv : v∈mask 93056 := hi hv
    have reduced : ∀ a:V, a∈mask 93056 → a≠14 → a∈mask 76672 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 102) (ok96 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93376 (hi : ineligSet 17 D⊆mask 93376) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c76992 live corr hw ne
    intro v hv
    have vv : v∈mask 93376 := hi hv
    have reduced : ∀ a:V, a∈mask 93376 → a≠14 → a∈mask 76992 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 103) (ok96 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93504 (hi : ineligSet 17 D⊆mask 93504) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c77120 live corr hw ne
    intro v hv
    have vv : v∈mask 93504 := hi hv
    have reduced : ∀ a:V, a∈mask 93504 → a≠14 → a∈mask 77120 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 104) (ok104 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97281 (hi : ineligSet 17 D⊆mask 97281) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93185 live corr hw ne
    intro v hv
    have vv : v∈mask 97281 := hi hv
    have reduced : ∀ a:V, a∈mask 97281 → a≠12 → a∈mask 93185 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 105) (ok104 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32448 (hi : ineligSet 17 D⊆mask 32448) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c31936 live corr hw ne
    intro v hv
    have vv : v∈mask 32448 := hi hv
    have reduced : ∀ a:V, a∈mask 32448 → a≠9 → a∈mask 31936 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 106) (ok104 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32576 (hi : ineligSet 17 D⊆mask 32576) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c32064 live corr hw ne
    intro v hv
    have vv : v∈mask 32576 := hi hv
    have reduced : ∀ a:V, a∈mask 32576 → a≠9 → a∈mask 32064 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 107) (ok104 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32640 (hi : ineligSet 17 D⊆mask 32640) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c16256 live corr hw ne
    intro v hv
    have vv : v∈mask 32640 := hi hv
    have reduced : ∀ a:V, a∈mask 32640 → a≠14 → a∈mask 16256 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 108) (ok104 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c46816 (hi : ineligSet 17 D⊆mask 46816) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c46304 live corr hw ne
    intro v hv
    have vv : v∈mask 46816 := hi hv
    have reduced : ∀ a:V, a∈mask 46816 → a≠9 → a∈mask 46304 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 109) (ok104 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c56144 (hi : ineligSet 17 D⊆mask 56144) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c55632 live corr hw ne
    intro v hv
    have vv : v∈mask 56144 := hi hv
    have reduced : ∀ a:V, a∈mask 56144 → a≠9 → a∈mask 55632 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 110) (ok104 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c60808 (hi : ineligSet 17 D⊆mask 60808) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c44424 live corr hw ne
    intro v hv
    have vv : v∈mask 60808 := hi hv
    have reduced : ∀ a:V, a∈mask 60808 → a≠14 → a∈mask 44424 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 111) (ok104 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c69572 (hi : ineligSet 17 D⊆mask 69572) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c69060 live corr hw ne
    intro v hv
    have vv : v∈mask 69572 := hi hv
    have reduced : ∀ a:V, a∈mask 69572 → a≠9 → a∈mask 69060 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 112) (ok112 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c80832 (hi : ineligSet 17 D⊆mask 80832) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c15296 live corr hw ne
    intro v hv
    have vv : v∈mask 80832 := hi hv
    have reduced : ∀ a:V, a∈mask 80832 → a≠16 → a∈mask 15296 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 113) (ok112 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c81344 (hi : ineligSet 17 D⊆mask 81344) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c15808 live corr hw ne
    intro v hv
    have vv : v∈mask 81344 := hi hv
    have reduced : ∀ a:V, a∈mask 81344 → a≠16 → a∈mask 15808 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 114) (ok112 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c88000 (hi : ineligSet 17 D⊆mask 88000) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c22464 live corr hw ne
    intro v hv
    have vv : v∈mask 88000 := hi hv
    have reduced : ∀ a:V, a∈mask 88000 → a≠16 → a∈mask 22464 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 115) (ok112 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c89024 (hi : ineligSet 17 D⊆mask 89024) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c23488 live corr hw ne
    intro v hv
    have vv : v∈mask 89024 := hi hv
    have reduced : ∀ a:V, a∈mask 89024 → a≠16 → a∈mask 23488 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 116) (ok112 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c89536 (hi : ineligSet 17 D⊆mask 89536) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c24000 live corr hw ne
    intro v hv
    have vv : v∈mask 89536 := hi hv
    have reduced : ∀ a:V, a∈mask 89536 → a≠16 → a∈mask 24000 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 117) (ok112 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c92096 (hi : ineligSet 17 D⊆mask 92096) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c26560 live corr hw ne
    intro v hv
    have vv : v∈mask 92096 := hi hv
    have reduced : ∀ a:V, a∈mask 92096 → a≠16 → a∈mask 26560 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 118) (ok112 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93120 (hi : ineligSet 17 D⊆mask 93120) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c27584 live corr hw ne
    intro v hv
    have vv : v∈mask 93120 := hi hv
    have reduced : ∀ a:V, a∈mask 93120 → a≠16 → a∈mask 27584 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 119) (ok112 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c93632 (hi : ineligSet 17 D⊆mask 93632) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c93504 live corr hw ne
    intro v hv
    have vv : v∈mask 93632 := hi hv
    have reduced : ∀ a:V, a∈mask 93632 → a≠7 → a∈mask 93504 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 120) (ok120 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c94658 (hi : ineligSet 17 D⊆mask 94658) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c90562 live corr hw ne
    intro v hv
    have vv : v∈mask 94658 := hi hv
    have reduced : ∀ a:V, a∈mask 94658 → a≠12 → a∈mask 90562 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 121) (ok120 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c96960 (hi : ineligSet 17 D⊆mask 96960) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c92864 live corr hw ne
    intro v hv
    have vv : v∈mask 96960 := hi hv
    have reduced : ∀ a:V, a∈mask 96960 → a≠12 → a∈mask 92864 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 122) (ok120 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97088 (hi : ineligSet 17 D⊆mask 97088) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c92992 live corr hw ne
    intro v hv
    have vv : v∈mask 97088 := hi hv
    have reduced : ∀ a:V, a∈mask 97088 → a≠12 → a∈mask 92992 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 123) (ok120 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97152 (hi : ineligSet 17 D⊆mask 97152) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93056 live corr hw ne
    intro v hv
    have vv : v∈mask 97152 := hi hv
    have reduced : ∀ a:V, a∈mask 97152 → a≠12 → a∈mask 93056 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 124) (ok120 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97472 (hi : ineligSet 17 D⊆mask 97472) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93376 live corr hw ne
    intro v hv
    have vv : v∈mask 97472 := hi hv
    have reduced : ∀ a:V, a∈mask 97472 → a≠12 → a∈mask 93376 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 125) (ok120 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97600 (hi : ineligSet 17 D⊆mask 97600) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93504 live corr hw ne
    intro v hv
    have vv : v∈mask 97600 := hi hv
    have reduced : ∀ a:V, a∈mask 97600 → a≠12 → a∈mask 93504 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 126) (ok120 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97664 (hi : ineligSet 17 D⊆mask 97664) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c81280 live corr hw ne
    intro v hv
    have vv : v∈mask 97664 := hi hv
    have reduced : ∀ a:V, a∈mask 97664 → a≠14 → a∈mask 81280 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 127) (ok120 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97793 (hi : ineligSet 17 D⊆mask 97793) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c97281 live corr hw ne
    intro v hv
    have vv : v∈mask 97793 := hi hv
    have reduced : ∀ a:V, a∈mask 97793 → a≠9 → a∈mask 97281 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 128) (ok128 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32704 (hi : ineligSet 17 D⊆mask 32704) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c32640 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠6 → a∈mask 32640 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c32576 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠7 → a∈mask 32576 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c32448 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠8 → a∈mask 32448 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 129) (ok128 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c81856 (hi : ineligSet 17 D⊆mask 81856) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c81344 live corr hw ne
    intro v hv
    have vv : v∈mask 81856 := hi hv
    have reduced : ∀ a:V, a∈mask 81856 → a≠9 → a∈mask 81344 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c80832 live corr hw ne
    intro v hv
    have vv : v∈mask 81856 := hi hv
    have reduced : ∀ a:V, a∈mask 81856 → a≠10 → a∈mask 80832 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 130) (ok128 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c90048 (hi : ineligSet 17 D⊆mask 90048) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c89536 live corr hw ne
    intro v hv
    have vv : v∈mask 90048 := hi hv
    have reduced : ∀ a:V, a∈mask 90048 → a≠9 → a∈mask 89536 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c89024 live corr hw ne
    intro v hv
    have vv : v∈mask 90048 := hi hv
    have reduced : ∀ a:V, a∈mask 90048 → a≠10 → a∈mask 89024 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 131) (ok128 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c94144 (hi : ineligSet 17 D⊆mask 94144) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c93632 live corr hw ne
    intro v hv
    have vv : v∈mask 94144 := hi hv
    have reduced : ∀ a:V, a∈mask 94144 → a≠9 → a∈mask 93632 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c93120 live corr hw ne
    intro v hv
    have vv : v∈mask 94144 := hi hv
    have reduced : ∀ a:V, a∈mask 94144 → a≠10 → a∈mask 93120 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 132) (ok128 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c96192 (hi : ineligSet 17 D⊆mask 96192) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c92096 live corr hw ne
    intro v hv
    have vv : v∈mask 96192 := hi hv
    have reduced : ∀ a:V, a∈mask 96192 → a≠12 → a∈mask 92096 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c88000 live corr hw ne
    intro v hv
    have vv : v∈mask 96192 := hi hv
    have reduced : ∀ a:V, a∈mask 96192 → a≠13 → a∈mask 88000 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 133) (ok128 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97216 (hi : ineligSet 17 D⊆mask 97216) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93120 live corr hw ne
    intro v hv
    have vv : v∈mask 97216 := hi hv
    have reduced : ∀ a:V, a∈mask 97216 → a≠12 → a∈mask 93120 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c89024 live corr hw ne
    intro v hv
    have vv : v∈mask 97216 := hi hv
    have reduced : ∀ a:V, a∈mask 97216 → a≠13 → a∈mask 89024 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 134) (ok128 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97728 (hi : ineligSet 17 D⊆mask 97728) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c93632 live corr hw ne
    intro v hv
    have vv : v∈mask 97728 := hi hv
    have reduced : ∀ a:V, a∈mask 97728 → a≠12 → a∈mask 93632 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c89536 live corr hw ne
    intro v hv
    have vv : v∈mask 97728 := hi hv
    have reduced : ∀ a:V, a∈mask 97728 → a≠13 → a∈mask 89536 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 135) (ok128 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c97984 (hi : ineligSet 17 D⊆mask 97984) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c97472 live corr hw ne
    intro v hv
    have vv : v∈mask 97984 := hi hv
    have reduced : ∀ a:V, a∈mask 97984 → a≠9 → a∈mask 97472 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c96960 live corr hw ne
    intro v hv
    have vv : v∈mask 97984 := hi hv
    have reduced : ∀ a:V, a∈mask 97984 → a≠10 → a∈mask 96960 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 136) (ok136 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c98112 (hi : ineligSet 17 D⊆mask 98112) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c97600 live corr hw ne
    intro v hv
    have vv : v∈mask 98112 := hi hv
    have reduced : ∀ a:V, a∈mask 98112 → a≠9 → a∈mask 97600 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c97088 live corr hw ne
    intro v hv
    have vv : v∈mask 98112 := hi hv
    have reduced : ∀ a:V, a∈mask 98112 → a≠10 → a∈mask 97088 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 137) (ok136 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c98176 (hi : ineligSet 17 D⊆mask 98176) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c97664 live corr hw ne
    intro v hv
    have vv : v∈mask 98176 := hi hv
    have reduced : ∀ a:V, a∈mask 98176 → a≠9 → a∈mask 97664 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c97152 live corr hw ne
    intro v hv
    have vv : v∈mask 98176 := hi hv
    have reduced : ∀ a:V, a∈mask 98176 → a≠10 → a∈mask 97152 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 138) (ok136 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c65472 (hi : ineligSet 17 D⊆mask 65472) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c32704 live corr hw ne
    intro v hv
    have vv : v∈mask 65472 := hi hv
    have reduced : ∀ a:V, a∈mask 65472 → a≠15 → a∈mask 32704 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 139) (ok136 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c98240 (hi : ineligSet 17 D⊆mask 98240) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c32704 live corr hw ne
    intro v hv
    have vv : v∈mask 98240 := hi hv
    have reduced : ∀ a:V, a∈mask 98240 → a≠16 → a∈mask 32704 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 140) (ok136 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 65536 → a=16 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c114624 (hi : ineligSet 17 D⊆mask 114624) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c81856 live corr hw ne
    intro v hv
    have vv : v∈mask 114624 := hi hv
    have reduced : ∀ a:V, a∈mask 114624 → a≠15 → a∈mask 81856 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 141) (ok136 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c122816 (hi : ineligSet 17 D⊆mask 122816) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c90048 live corr hw ne
    intro v hv
    have vv : v∈mask 122816 := hi hv
    have reduced : ∀ a:V, a∈mask 122816 → a≠15 → a∈mask 90048 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 142) (ok136 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c126912 (hi : ineligSet 17 D⊆mask 126912) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c94144 live corr hw ne
    intro v hv
    have vv : v∈mask 126912 := hi hv
    have reduced : ∀ a:V, a∈mask 126912 → a≠15 → a∈mask 94144 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 143) (ok136 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c128960 (hi : ineligSet 17 D⊆mask 128960) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c96192 live corr hw ne
    intro v hv
    have vv : v∈mask 128960 := hi hv
    have reduced : ∀ a:V, a∈mask 128960 → a≠15 → a∈mask 96192 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 144) (ok144 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c129984 (hi : ineligSet 17 D⊆mask 129984) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c97216 live corr hw ne
    intro v hv
    have vv : v∈mask 129984 := hi hv
    have reduced : ∀ a:V, a∈mask 129984 → a≠15 → a∈mask 97216 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 145) (ok144 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c130496 (hi : ineligSet 17 D⊆mask 130496) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c97728 live corr hw ne
    intro v hv
    have vv : v∈mask 130496 := hi hv
    have reduced : ∀ a:V, a∈mask 130496 → a≠15 → a∈mask 97728 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 146) (ok144 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c130752 (hi : ineligSet 17 D⊆mask 130752) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c97984 live corr hw ne
    intro v hv
    have vv : v∈mask 130752 := hi hv
    have reduced : ∀ a:V, a∈mask 130752 → a≠15 → a∈mask 97984 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 147) (ok144 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c130880 (hi : ineligSet 17 D⊆mask 130880) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c98112 live corr hw ne
    intro v hv
    have vv : v∈mask 130880 := hi hv
    have reduced : ∀ a:V, a∈mask 130880 → a≠15 → a∈mask 98112 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 148) (ok144 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c130944 (hi : ineligSet 17 D⊆mask 130944) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c98176 live corr hw ne
    intro v hv
    have vv : v∈mask 130944 := hi hv
    have reduced : ∀ a:V, a∈mask 130944 → a≠15 → a∈mask 98176 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  refine applyRow live corr false hw 4 (row 149) (ok144 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 32768 → a=15 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c131008 (hi : ineligSet 17 D⊆mask 131008) : 33+Bzero 17 D≤D.length+4 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c130944 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠6 → a∈mask 130944 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c130880 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠7 → a∈mask 130880 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c130752 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠8 → a∈mask 130752 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c130496 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠9 → a∈mask 130496 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c129984 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠10 → a∈mask 129984 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c128960 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠11 → a∈mask 128960 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c126912 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠12 → a∈mask 126912 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c122816 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠13 → a∈mask 122816 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c114624 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠14 → a∈mask 114624 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  by_cases h15 : (15:V)∈ineligSet 17 D
  swap
  · apply c98240 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠15 → a∈mask 98240 := by decide +kernel
    exact reduced v vv (fun e => h15 (e ▸ hv))
  by_cases h16 : (16:V)∈ineligSet 17 D
  swap
  · apply c65472 live corr hw ne
    intro v hv
    have vv : v∈mask 131008 := hi hv
    have reduced : ∀ a:V, a∈mask 131008 → a≠16 → a∈mask 65472 := by decide +kernel
    exact reduced v vv (fun e => h16 (e ▸ hv))
  exfalso
  apply ne
  apply Finset.Subset.antisymm hi
  intro v hv
  have list : ∀ a:V, a∈mask 131008 → a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 ∨ a=15 ∨ a=16 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
def roots : Array Nat := #[131008,97793,94658,94211,69572,69125,65990,65543,60808,27657,24970,24587,3468,3085,398,15,56144,23057,20818,20499,2900,2581,342,23,51480,18457,16666,16411,2332,2077,286,31,46816,13857,12514,12323,1764,1573,230,39,42152,9257,8362,8235,1196,1069,174,47,37488,4657,4210,4147,628,565,118,55,32824,57,58,59,60,61,62,63]
def root (S : Finset L) := (roots[key S]?).getD 0
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem cover : ∀ S : Finset L, panel S ⊆ mask (root S) := by decide +kernel
include live corr hw ne in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem all (ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j) : 33+Bzero 17 D≤D.length+4 := by
  let S := leftSet D
  have inc := in_panel D ind
  have con := cover S
  have hi : ineligSet 17 D⊆mask (root S) := fun i h => con (inc h)
  have cc0 : ∀ S : Finset L, root S ∈ ([15,23,31,39,47,55,57,58,59,60,61,62,63,118,174,230,286,342,398,565,628,1069,1196,1573,1764,2077,2332,2581,2900,3085,3468,4147,4210,4657,8235,8362,9257,12323,12514,13857,16411,16666,18457,20499,20818,23057,24587,24970,27657,32824,37488,42152,46816,51480,56144,60808,65543,65990,69125,69572,94211,94658,97793,131008] : List Nat) := by decide +kernel
  have cc := cc0 S
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cc
  rcases cc with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  · exact c15 live corr hw ne (e ▸ hi)
  · exact c23 live corr hw ne (e ▸ hi)
  · exact c31 live corr hw ne (e ▸ hi)
  · exact c39 live corr hw ne (e ▸ hi)
  · exact c47 live corr hw ne (e ▸ hi)
  · exact c55 live corr hw ne (e ▸ hi)
  · exact c57 live corr hw ne (e ▸ hi)
  · exact c58 live corr hw ne (e ▸ hi)
  · exact c59 live corr hw ne (e ▸ hi)
  · exact c60 live corr hw ne (e ▸ hi)
  · exact c61 live corr hw ne (e ▸ hi)
  · exact c62 live corr hw ne (e ▸ hi)
  · exact c63 live corr hw ne (e ▸ hi)
  · exact c118 live corr hw ne (e ▸ hi)
  · exact c174 live corr hw ne (e ▸ hi)
  · exact c230 live corr hw ne (e ▸ hi)
  · exact c286 live corr hw ne (e ▸ hi)
  · exact c342 live corr hw ne (e ▸ hi)
  · exact c398 live corr hw ne (e ▸ hi)
  · exact c565 live corr hw ne (e ▸ hi)
  · exact c628 live corr hw ne (e ▸ hi)
  · exact c1069 live corr hw ne (e ▸ hi)
  · exact c1196 live corr hw ne (e ▸ hi)
  · exact c1573 live corr hw ne (e ▸ hi)
  · exact c1764 live corr hw ne (e ▸ hi)
  · exact c2077 live corr hw ne (e ▸ hi)
  · exact c2332 live corr hw ne (e ▸ hi)
  · exact c2581 live corr hw ne (e ▸ hi)
  · exact c2900 live corr hw ne (e ▸ hi)
  · exact c3085 live corr hw ne (e ▸ hi)
  · exact c3468 live corr hw ne (e ▸ hi)
  · exact c4147 live corr hw ne (e ▸ hi)
  · exact c4210 live corr hw ne (e ▸ hi)
  · exact c4657 live corr hw ne (e ▸ hi)
  · exact c8235 live corr hw ne (e ▸ hi)
  · exact c8362 live corr hw ne (e ▸ hi)
  · exact c9257 live corr hw ne (e ▸ hi)
  · exact c12323 live corr hw ne (e ▸ hi)
  · exact c12514 live corr hw ne (e ▸ hi)
  · exact c13857 live corr hw ne (e ▸ hi)
  · exact c16411 live corr hw ne (e ▸ hi)
  · exact c16666 live corr hw ne (e ▸ hi)
  · exact c18457 live corr hw ne (e ▸ hi)
  · exact c20499 live corr hw ne (e ▸ hi)
  · exact c20818 live corr hw ne (e ▸ hi)
  · exact c23057 live corr hw ne (e ▸ hi)
  · exact c24587 live corr hw ne (e ▸ hi)
  · exact c24970 live corr hw ne (e ▸ hi)
  · exact c27657 live corr hw ne (e ▸ hi)
  · exact c32824 live corr hw ne (e ▸ hi)
  · exact c37488 live corr hw ne (e ▸ hi)
  · exact c42152 live corr hw ne (e ▸ hi)
  · exact c46816 live corr hw ne (e ▸ hi)
  · exact c51480 live corr hw ne (e ▸ hi)
  · exact c56144 live corr hw ne (e ▸ hi)
  · exact c60808 live corr hw ne (e ▸ hi)
  · exact c65543 live corr hw ne (e ▸ hi)
  · exact c65990 live corr hw ne (e ▸ hi)
  · exact c69125 live corr hw ne (e ▸ hi)
  · exact c69572 live corr hw ne (e ▸ hi)
  · exact c94211 live corr hw ne (e ▸ hi)
  · exact c94658 live corr hw ne (e ▸ hi)
  · exact c97793 live corr hw ne (e ▸ hi)
  · exact c131008 live corr hw ne (e ▸ hi)
end Scalar
namespace Marked
def data : Array ProofRow := #[
⟨7,0,[],7,0,[]⟩,
⟨56,0,[],56,0,[]⟩,
⟨15,0,[(15,none)],8,0,[]⟩,
⟨23,0,[(15,none)],16,0,[]⟩,
⟨39,0,[(15,none)],32,0,[]⟩,
⟨57,0,[(16,none)],1,0,[]⟩,
⟨58,0,[(16,none)],2,0,[]⟩,
⟨60,0,[(16,none)],4,0,[]⟩,
⟨676,0,[(15,none),(16,some 15)],640,98304,[(15,97793),(16,60808)]⟩,
⟨788,0,[(15,none),(16,some 15)],768,98304,[(15,97793),(16,60808)]⟩,
⟨1124,0,[(15,none),(16,some 15)],1088,98304,[(15,97793),(16,60808)]⟩,
⟨1292,0,[(15,none),(16,some 15)],1280,98304,[(15,97793),(16,56144)]⟩,
⟨2132,0,[(15,none),(16,some 15)],2112,98304,[(15,97793),(16,60808)]⟩,
⟨2188,0,[(15,none),(16,some 15)],2176,98304,[(15,97793),(16,56144)]⟩,
⟨2244,0,[(0,none)],2052,1,[(0,51480)]⟩,
⟨3140,0,[(1,none)],68,2,[(1,37488)]⟩,
⟨4258,0,[(15,none),(16,some 15)],4224,98304,[(15,97793),(16,60808)]⟩,
⟨4370,0,[(15,none),(16,some 15)],4352,98304,[(15,97793),(16,60808)]⟩,
⟨5153,0,[(15,none),(16,some 15)],5120,98304,[(15,94658),(16,60808)]⟩,
⟨5504,0,[(0,none)],5120,1,[(0,37488)]⟩,
⟨6161,0,[(15,none),(16,some 15)],6144,98304,[(15,94658),(16,60808)]⟩,
⟨6416,0,[(5,none)],4112,32,[(5,94211)]⟩,
⟨6528,0,[(0,none)],6144,1,[(0,37488)]⟩,
⟨7296,0,[(4,none)],6144,16,[(4,94211)]⟩,
⟨8290,0,[(15,none),(16,some 15)],8256,98304,[(15,97793),(16,60808)]⟩,
⟨8458,0,[(15,none),(16,some 15)],8448,98304,[(15,97793),(16,56144)]⟩,
⟨8514,0,[(0,none)],8194,1,[(0,42152)]⟩,
⟨8737,0,[(15,none),(16,some 15)],8704,98304,[(15,94658),(16,60808)]⟩,
⟨8864,0,[(4,none)],544,16,[(4,69125)]⟩,
⟨9312,0,[(4,none)],96,16,[(4,65990)]⟩,
⟨9536,0,[(0,none)],9216,1,[(0,42152)]⟩,
⟨10249,0,[(15,none),(16,some 15)],10240,98304,[(15,94658),(16,56144)]⟩,
⟨10376,0,[(4,none)],2056,16,[(4,69125)]⟩,
⟨10432,0,[(0,none)],10240,1,[(0,51480)]⟩,
⟨10504,0,[(5,none)],8200,32,[(5,94211)]⟩,
⟨10560,0,[(0,none)],10240,1,[(0,42152)]⟩,
⟨10753,0,[(1,none)],8193,2,[(1,42152)]⟩,
⟨11008,0,[(5,none)],8704,32,[(5,94211)]⟩,
⟨14337,0,[(2,none)],2049,4,[(2,51480)]⟩,
⟨16466,0,[(15,none),(16,some 15)],16448,98304,[(15,97793),(16,60808)]⟩,
⟨16522,0,[(15,none),(16,some 15)],16512,98304,[(15,97793),(16,56144)]⟩,
⟨16578,0,[(0,none)],16386,1,[(0,51480)]⟩,
⟨16913,0,[(15,none),(16,some 15)],16896,98304,[(15,94658),(16,60808)]⟩,
⟨17280,0,[(0,none)],16896,1,[(0,37488)]⟩,
⟨17417,0,[(15,none),(16,some 15)],17408,98304,[(15,94658),(16,56144)]⟩,
⟨18512,0,[(5,none)],80,32,[(5,65990)]⟩,
⟨18624,0,[(0,none)],18432,1,[(0,51480)]⟩,
⟨19520,0,[(5,none)],1088,32,[(5,65990)]⟩,
⟨25664,0,[(4,none)],16448,16,[(4,65990)]⟩,
⟨31,0,[(15,none),(16,none)],0,65536,[(16,46816)]⟩,
⟨47,0,[(15,none),(16,none)],0,65536,[(16,56144)]⟩,
⟨55,0,[(15,none),(16,none)],0,65536,[(16,60808)]⟩,
⟨59,0,[(15,none),(16,none)],0,32768,[(15,69572)]⟩,
⟨61,0,[(15,none),(16,none)],0,32768,[(15,94658)]⟩,
⟨62,0,[(15,none),(16,none)],0,32768,[(15,97793)]⟩,
⟨118,0,[(15,none),(16,none)],64,98304,[(15,97793),(16,60808)]⟩,
⟨174,0,[(15,none),(16,none)],128,98304,[(15,97793),(16,56144)]⟩,
⟨230,0,[(0,none),(15,none)],32,32769,[(0,51480),(15,97793)]⟩,
⟨286,0,[(15,none),(16,none)],256,98304,[(15,97793),(16,46816)]⟩,
⟨342,0,[(0,none),(15,none)],16,32769,[(0,42152),(15,97793)]⟩,
⟨398,0,[(0,none),(15,none)],8,32769,[(0,37488),(15,97793)]⟩,
⟨454,0,[(0,none)],6,1,[(0,32824)]⟩,
⟨565,0,[(15,none),(16,none)],512,98304,[(15,94658),(16,60808)]⟩,
⟨628,0,[(3,none),(16,none)],4,65544,[(3,94211),(16,60808)]⟩,
⟨740,64,[(0,none),(3,some 0)],36,9,[(0,51480),(3,94211)]⟩,
⟨1069,0,[(15,none),(16,none)],1024,98304,[(15,94658),(16,56144)]⟩,
⟨1196,0,[(4,none),(16,none)],4,65552,[(4,94211),(16,56144)]⟩,
⟨1252,128,[(0,none),(4,some 0)],36,17,[(0,51480),(4,94211)]⟩,
⟨1573,0,[(1,none),(15,none)],32,32770,[(1,51480),(15,94658)]⟩,
⟨2077,0,[(15,none),(16,none)],2048,98304,[(15,94658),(16,46816)]⟩,
⟨2332,0,[(5,none),(16,none)],4,65568,[(5,94211),(16,46816)]⟩,
⟨2388,256,[(0,none),(5,some 0)],20,33,[(0,42152),(5,94211)]⟩,
⟨2581,0,[(1,none),(15,none)],16,32770,[(1,42152),(15,94658)]⟩,
⟨2756,512,[(1,none),(3,some 1)],132,10,[(1,42152),(3,94211)]⟩,
⟨2836,2048,[(1,none),(5,some 1)],20,34,[(1,42152),(5,94211)]⟩,
⟨3085,0,[(1,none),(15,none)],8,32770,[(1,37488),(15,94658)]⟩,
⟨3212,1024,[(1,none),(4,some 1)],12,18,[(1,37488),(4,94211)]⟩,
⟨3340,2048,[(1,none),(5,some 1)],12,34,[(1,37488),(5,94211)]⟩,
⟨3396,256,[(0,none),(5,some 0)],1028,33,[(0,42152),(5,94211)]⟩,
⟨3589,0,[(1,none)],5,2,[(1,32824)]⟩,
⟨4147,0,[(15,none),(16,none)],4096,98304,[(15,69572),(16,60808)]⟩,
⟨4210,0,[(3,none),(16,none)],2,65544,[(3,69125),(16,60808)]⟩,
⟨4322,64,[(0,none),(3,some 0)],34,9,[(0,51480),(3,69125)]⟩,
⟨4657,0,[(3,none),(16,none)],1,65544,[(3,65990),(16,60808)]⟩,
⟨4720,0,[(3,none)],48,8,[(3,65543)]⟩,
⟨6673,512,[(1,none),(3,some 1)],17,10,[(1,42152),(3,65990)]⟩,
⟨6928,512,[(1,none),(3,some 1)],272,10,[(1,42152),(3,65990)]⟩,
⟨7040,512,[(1,none),(3,some 1)],384,10,[(1,42152),(3,65990)]⟩,
⟨7488,0,[(1,none),(3,none)],256,10,[(1,32824),(3,65543)]⟩,
⟨8235,0,[(15,none),(16,none)],8192,98304,[(15,69572),(16,56144)]⟩,
⟨8362,0,[(4,none),(16,none)],2,65552,[(4,69125),(16,56144)]⟩,
⟨8418,128,[(0,none),(4,some 0)],34,17,[(0,51480),(4,69125)]⟩,
⟨8586,128,[(0,none),(4,some 0)],10,17,[(0,37488),(4,69125)]⟩,
⟨9257,0,[(4,none),(16,none)],1,65552,[(4,65990),(16,56144)]⟩,
⟨9384,0,[(4,none)],40,16,[(4,65543)]⟩,
⟨9824,512,[(1,none),(3,some 1)],8224,10,[(1,51480),(3,94211)]⟩,
⟨10944,512,[(1,none),(3,some 1)],8320,10,[(1,42152),(3,94211)]⟩,
⟨11072,512,[(1,none),(3,some 1)],8448,10,[(1,42152),(3,94211)]⟩,
⟨11136,128,[(0,none),(4,some 0)],2560,17,[(0,37488),(4,69125)]⟩,
⟨11273,1024,[(1,none),(4,some 1)],9,18,[(1,37488),(4,65990)]⟩,
⟨11528,1024,[(1,none),(4,some 1)],264,18,[(1,37488),(4,65990)]⟩,
⟨11584,0,[(0,none),(4,none)],2048,17,[(0,32824),(4,65543)]⟩,
⟨12323,0,[(2,none),(15,none)],32,32772,[(2,51480),(15,69572)]⟩,
⟨12833,4096,[(2,none),(3,some 2)],33,12,[(2,51480),(3,65990)]⟩,
⟨12960,4096,[(2,none),(3,some 2)],160,12,[(2,51480),(3,65990)]⟩,
⟨13345,8192,[(2,none),(4,some 2)],33,20,[(2,51480),(4,65990)]⟩,
⟨15361,1024,[(1,none),(4,some 1)],4097,18,[(1,37488),(4,65990)]⟩,
⟨15424,0,[(1,none),(3,none)],8192,10,[(1,32824),(3,65543)]⟩,
⟨15616,0,[(2,none),(5,none)],1024,36,[(2,32824),(5,65543)]⟩,
⟨16411,0,[(15,none),(16,none)],16384,98304,[(15,69572),(16,46816)]⟩,
⟨16666,0,[(5,none),(16,none)],2,65568,[(5,69125),(16,46816)]⟩,
⟨16722,256,[(0,none),(5,some 0)],18,33,[(0,42152),(5,69125)]⟩,
⟨16778,256,[(0,none),(5,some 0)],10,33,[(0,37488),(5,69125)]⟩,
⟨18457,0,[(5,none),(16,none)],1,65568,[(5,65990),(16,46816)]⟩,
⟨18712,0,[(5,none)],24,32,[(5,65543)]⟩,
⟨18961,2048,[(1,none),(5,some 1)],17,34,[(1,42152),(5,65990)]⟩,
⟨19024,512,[(1,none),(3,some 1)],16400,10,[(1,42152),(3,94211)]⟩,
⟨19136,512,[(1,none),(3,some 1)],16512,10,[(1,42152),(3,94211)]⟩,
⟨19465,2048,[(1,none),(5,some 1)],9,34,[(1,37488),(5,65990)]⟩,
⟨19648,128,[(0,none),(4,some 0)],18432,17,[(0,51480),(4,94211)]⟩,
⟨20499,0,[(2,none),(15,none)],16,32772,[(2,42152),(15,69572)]⟩,
⟨20674,4096,[(2,none),(3,some 2)],130,12,[(2,42152),(3,69125)]⟩,
⟨20754,16384,[(2,none),(5,some 2)],18,36,[(2,42152),(5,69125)]⟩,
⟨21376,4096,[(2,none),(3,some 2)],384,12,[(2,42152),(3,65990)]⟩,
⟨21888,16384,[(2,none),(5,some 2)],1152,36,[(2,42152),(5,69125)]⟩,
⟨23680,16384,[(2,none),(5,some 2)],1152,36,[(2,42152),(5,65990)]⟩,
⟨24587,0,[(2,none),(15,none)],8,32772,[(2,37488),(15,69572)]⟩,
⟨24898,16384,[(2,none),(5,some 2)],66,36,[(2,37488),(5,69125)]⟩,
⟨25408,0,[(2,none),(3,none)],256,12,[(2,32824),(3,65543)]⟩,
⟨25920,16384,[(2,none),(5,some 2)],1088,36,[(2,37488),(5,69125)]⟩,
⟨26176,512,[(1,none),(3,some 1)],24576,10,[(1,51480),(3,94211)]⟩,
⟨26760,16384,[(2,none),(5,some 2)],136,36,[(2,37488),(5,65990)]⟩,
⟨27137,16384,[(2,none),(5,some 2)],513,36,[(2,37488),(5,65990)]⟩,
⟨28675,0,[(2,none)],3,4,[(2,32824)]⟩,
⟨63,0,[(15,none),(16,some 15)],0,0,[]⟩,
⟨1764,1536,[(1,none),(3,some 1),(4,some 1)],36,26,[(1,51480),(3,20499),(4,24587)]⟩,
⟨2900,576,[(0,none),(3,some 0),(1,some 3)],20,11,[(0,8362),(1,9257),(3,94211)]⟩,
⟨3012,256,[(0,none),(5,some 0)],516,33,[(0,32824),(5,94211)]⟩,
⟨3468,384,[(0,none),(4,some 0),(5,some 0)],12,49,[(0,37488),(4,12323),(5,20499)]⟩,
⟨3524,128,[(0,none),(4,some 0)],2052,17,[(0,32824),(4,94211)]⟩,
⟨9952,128,[(0,none),(4,some 0)],544,17,[(0,51480),(4,65543)]⟩,
⟨11656,128,[(0,none),(4,some 0)],2056,17,[(0,37488),(4,65543)]⟩,
⟨12514,12288,[(2,none),(3,some 2),(4,some 2)],34,28,[(2,51480),(3,2581),(4,3085)]⟩,
⟨13857,1536,[(1,none),(3,some 1),(4,some 1)],33,26,[(1,51480),(3,342),(4,398)]⟩,
⟨13984,1024,[(1,none),(4,some 1)],4128,18,[(1,51480),(4,65543)]⟩,
⟨15232,12288,[(2,none),(3,some 2),(4,some 2)],2304,28,[(2,51480),(3,342),(4,3085)]⟩,
⟨15552,128,[(0,none),(4,some 0)],6144,17,[(0,51480),(4,65543)]⟩,
⟨15680,12288,[(2,none),(3,some 2),(4,some 2)],2304,28,[(2,51480),(3,2581),(4,398)]⟩,
⟨15744,128,[(0,none),(4,some 0)],6144,17,[(0,37488),(4,65543)]⟩,
⟨19280,256,[(0,none),(5,some 0)],528,33,[(0,42152),(5,65543)]⟩,
⟨20818,4160,[(0,none),(3,some 0),(2,some 3)],18,13,[(0,1196),(2,9257),(3,69125)]⟩,
⟨20930,256,[(0,none),(5,some 0)],4098,33,[(0,32824),(5,69125)]⟩,
⟨22400,1536,[(1,none),(3,some 1),(4,some 1)],16640,26,[(1,51480),(3,342),(4,24587)]⟩,
⟨23057,20480,[(2,none),(3,some 2),(5,some 2)],17,44,[(2,42152),(3,230),(5,398)]⟩,
⟨23312,16384,[(2,none),(5,some 2)],528,36,[(2,42152),(5,65543)]⟩,
⟨23744,4160,[(0,none),(3,some 0),(2,some 3)],3072,13,[(0,2332),(2,9257),(3,69125)]⟩,
⟨23872,16384,[(2,none),(5,some 2)],1088,36,[(2,42152),(5,65543)]⟩,
⟨24970,24576,[(2,none),(4,some 2),(5,some 2)],10,52,[(2,37488),(4,1573),(5,2581)]⟩,
⟨25026,128,[(0,none),(4,some 0)],16386,17,[(0,32824),(4,69125)]⟩,
⟨26304,128,[(0,none),(4,some 0)],16896,17,[(0,51480),(4,65543)]⟩,
⟨26432,1536,[(1,none),(3,some 1),(4,some 1)],16640,26,[(1,51480),(3,20499),(4,398)]⟩,
⟨27328,24576,[(2,none),(4,some 2),(5,some 2)],576,52,[(2,37488),(4,1573),(5,342)]⟩,
⟨27456,16384,[(2,none),(5,some 2)],576,36,[(2,37488),(5,65543)]⟩,
⟨27520,16384,[(2,none),(5,some 2)],640,36,[(2,37488),(5,65543)]⟩,
⟨27657,24576,[(2,none),(4,some 2),(5,some 2)],9,52,[(2,37488),(4,230),(5,342)]⟩,
⟨27784,1024,[(1,none),(4,some 1)],16392,18,[(1,37488),(4,65543)]⟩,
⟨31233,4096,[(2,none),(3,some 2)],2049,12,[(2,32824),(3,65990)]⟩,
⟨31745,16384,[(2,none),(5,some 2)],1025,36,[(2,32824),(5,65990)]⟩,
⟨4036,1536,[(1,none),(3,some 1),(4,some 1)],260,26,[(1,32824),(3,20499),(4,24587)]⟩,
⟨14048,4160,[(0,none),(3,some 0),(2,some 3)],1056,13,[(0,2332),(2,18457),(3,65543)]⟩,
⟨16064,512,[(1,none),(3,some 1)],8320,10,[(1,32824),(3,65543)]⟩,
⟨16192,512,[(1,none),(3,some 1)],8448,10,[(1,32824),(3,65543)]⟩,
⟨16256,1024,[(1,none),(4,some 1)],4352,18,[(1,32824),(4,65543)]⟩,
⟨23376,4160,[(0,none),(3,some 0),(2,some 3)],2064,13,[(0,1196),(2,9257),(3,65543)]⟩,
⟨24256,512,[(1,none),(3,some 1)],16512,10,[(1,32824),(3,65543)]⟩,
⟨24384,512,[(1,none),(3,some 1)],16640,10,[(1,32824),(3,65543)]⟩,
⟨24448,2048,[(1,none),(5,some 1)],4224,34,[(1,32824),(5,65543)]⟩,
⟨28040,16640,[(0,none),(5,some 0),(2,some 5)],1032,37,[(0,628),(2,4657),(5,65543)]⟩,
⟨28352,1024,[(1,none),(4,some 1)],16448,18,[(1,32824),(4,65543)]⟩,
⟨28480,2048,[(1,none),(5,some 1)],8256,34,[(1,32824),(5,65543)]⟩,
⟨28544,1024,[(1,none),(4,some 1)],16640,18,[(1,32824),(4,65543)]⟩,
⟨29122,12288,[(2,none),(3,some 2),(4,some 2)],258,28,[(2,32824),(3,2581),(4,3085)]⟩,
⟨30400,4096,[(2,none),(3,some 2)],1152,12,[(2,32824),(3,65543)]⟩,
⟨30528,4096,[(2,none),(3,some 2)],1280,12,[(2,32824),(3,65543)]⟩,
⟨30592,8192,[(2,none),(4,some 2)],768,20,[(2,32824),(4,65543)]⟩,
⟨31424,4096,[(2,none),(3,some 2)],2176,12,[(2,32824),(3,65543)]⟩,
⟨31552,4096,[(2,none),(3,some 2)],2304,12,[(2,32824),(3,65543)]⟩,
⟨31616,16384,[(2,none),(5,some 2)],640,36,[(2,32824),(5,65543)]⟩,
⟨31936,8192,[(2,none),(4,some 2)],2112,20,[(2,32824),(4,65543)]⟩,
⟨32064,16384,[(2,none),(5,some 2)],1088,36,[(2,32824),(5,65543)]⟩,
⟨32128,16384,[(2,none),(5,some 2)],1152,36,[(2,32824),(5,65543)]⟩,
⟨32257,1536,[(1,none),(3,some 1),(4,some 1)],16385,26,[(1,32824),(3,342),(4,398)]⟩,
⟨16320,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,33,[(0,32824),(5,16411)]⟩,
⟨24512,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,17,[(0,32824),(4,8235)]⟩,
⟨28608,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,9,[(0,32824),(3,4147)]⟩,
⟨30656,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,33,[(0,32824),(5,2077)]⟩,
⟨31680,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,17,[(0,32824),(4,1069)]⟩,
⟨32192,448,[(0,none),(3,some 0),(4,some 0),(5,some 0)],0,9,[(0,32824),(3,565)]⟩,
⟨32448,3584,[(1,none),(3,some 1),(4,some 1),(5,some 1)],0,34,[(1,32824),(5,286)]⟩,
⟨32576,3584,[(1,none),(3,some 1),(4,some 1),(5,some 1)],0,18,[(1,32824),(4,174)]⟩,
⟨32640,3584,[(1,none),(3,some 1),(4,some 1),(5,some 1)],0,10,[(1,32824),(3,118)]⟩]
def row (i : Nat) := (data[i]?).getD default
private theorem ok0 : ∀ j : Fin 8, (row (0+j.val)).valid true 3=true := by decide +kernel
private theorem ok8 : ∀ j : Fin 8, (row (8+j.val)).valid true 3=true := by decide +kernel
private theorem ok16 : ∀ j : Fin 8, (row (16+j.val)).valid true 3=true := by decide +kernel
private theorem ok24 : ∀ j : Fin 8, (row (24+j.val)).valid true 3=true := by decide +kernel
private theorem ok32 : ∀ j : Fin 8, (row (32+j.val)).valid true 3=true := by decide +kernel
private theorem ok40 : ∀ j : Fin 8, (row (40+j.val)).valid true 3=true := by decide +kernel
private theorem ok48 : ∀ j : Fin 8, (row (48+j.val)).valid true 3=true := by decide +kernel
private theorem ok56 : ∀ j : Fin 8, (row (56+j.val)).valid true 3=true := by decide +kernel
private theorem ok64 : ∀ j : Fin 8, (row (64+j.val)).valid true 3=true := by decide +kernel
private theorem ok72 : ∀ j : Fin 8, (row (72+j.val)).valid true 3=true := by decide +kernel
private theorem ok80 : ∀ j : Fin 8, (row (80+j.val)).valid true 3=true := by decide +kernel
private theorem ok88 : ∀ j : Fin 8, (row (88+j.val)).valid true 3=true := by decide +kernel
private theorem ok96 : ∀ j : Fin 8, (row (96+j.val)).valid true 3=true := by decide +kernel
private theorem ok104 : ∀ j : Fin 8, (row (104+j.val)).valid true 3=true := by decide +kernel
private theorem ok112 : ∀ j : Fin 8, (row (112+j.val)).valid true 3=true := by decide +kernel
private theorem ok120 : ∀ j : Fin 8, (row (120+j.val)).valid true 3=true := by decide +kernel
private theorem ok128 : ∀ j : Fin 8, (row (128+j.val)).valid true 3=true := by decide +kernel
private theorem ok136 : ∀ j : Fin 8, (row (136+j.val)).valid true 3=true := by decide +kernel
private theorem ok144 : ∀ j : Fin 8, (row (144+j.val)).valid true 3=true := by decide +kernel
private theorem ok152 : ∀ j : Fin 8, (row (152+j.val)).valid true 3=true := by decide +kernel
private theorem ok160 : ∀ j : Fin 8, (row (160+j.val)).valid true 3=true := by decide +kernel
private theorem ok168 : ∀ j : Fin 8, (row (168+j.val)).valid true 3=true := by decide +kernel
private theorem ok176 : ∀ j : Fin 8, (row (176+j.val)).valid true 3=true := by decide +kernel
private theorem ok184 : ∀ j : Fin 8, (row (184+j.val)).valid true 3=true := by decide +kernel
private theorem ok192 : ∀ j : Fin 8, (row (192+j.val)).valid true 3=true := by decide +kernel
private theorem ok200 : ∀ j : Fin 1, (row (200+j.val)).valid true 3=true := by decide +kernel
variable {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
variable (hw : true=true → ∃w, (15:V)∈supp 17 D w ∧ (16:V)∈supp 17 D w) (ne : ineligSet 17 D ≠ mask 32704)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c7 (hi : ineligSet 17 D⊆mask 7) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 0) (ok0 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c56 (hi : ineligSet 17 D⊆mask 56) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 1) (ok0 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15 (hi : ineligSet 17 D⊆mask 15) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 2) (ok0 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23 (hi : ineligSet 17 D⊆mask 23) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 3) (ok0 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c39 (hi : ineligSet 17 D⊆mask 39) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 4) (ok0 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c57 (hi : ineligSet 17 D⊆mask 57) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 5) (ok0 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c58 (hi : ineligSet 17 D⊆mask 58) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 6) (ok0 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c60 (hi : ineligSet 17 D⊆mask 60) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 7) (ok0 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c676 (hi : ineligSet 17 D⊆mask 676) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 8) (ok8 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c788 (hi : ineligSet 17 D⊆mask 788) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 9) (ok8 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1124 (hi : ineligSet 17 D⊆mask 1124) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 10) (ok8 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1292 (hi : ineligSet 17 D⊆mask 1292) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 11) (ok8 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2132 (hi : ineligSet 17 D⊆mask 2132) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 12) (ok8 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2188 (hi : ineligSet 17 D⊆mask 2188) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 13) (ok8 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2244 (hi : ineligSet 17 D⊆mask 2244) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 14) (ok8 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3140 (hi : ineligSet 17 D⊆mask 3140) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 15) (ok8 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4258 (hi : ineligSet 17 D⊆mask 4258) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 16) (ok16 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4370 (hi : ineligSet 17 D⊆mask 4370) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 17) (ok16 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c5153 (hi : ineligSet 17 D⊆mask 5153) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 18) (ok16 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c5504 (hi : ineligSet 17 D⊆mask 5504) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 19) (ok16 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c6161 (hi : ineligSet 17 D⊆mask 6161) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 20) (ok16 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c6416 (hi : ineligSet 17 D⊆mask 6416) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 21) (ok16 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c6528 (hi : ineligSet 17 D⊆mask 6528) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 22) (ok16 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c7296 (hi : ineligSet 17 D⊆mask 7296) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 23) (ok16 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8290 (hi : ineligSet 17 D⊆mask 8290) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 24) (ok24 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8458 (hi : ineligSet 17 D⊆mask 8458) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 25) (ok24 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8514 (hi : ineligSet 17 D⊆mask 8514) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 26) (ok24 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8737 (hi : ineligSet 17 D⊆mask 8737) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 27) (ok24 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8864 (hi : ineligSet 17 D⊆mask 8864) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 28) (ok24 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9312 (hi : ineligSet 17 D⊆mask 9312) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 29) (ok24 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9536 (hi : ineligSet 17 D⊆mask 9536) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 30) (ok24 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10249 (hi : ineligSet 17 D⊆mask 10249) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 31) (ok24 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10376 (hi : ineligSet 17 D⊆mask 10376) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 32) (ok32 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10432 (hi : ineligSet 17 D⊆mask 10432) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 33) (ok32 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10504 (hi : ineligSet 17 D⊆mask 10504) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 34) (ok32 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10560 (hi : ineligSet 17 D⊆mask 10560) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 35) (ok32 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10753 (hi : ineligSet 17 D⊆mask 10753) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 36) (ok32 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11008 (hi : ineligSet 17 D⊆mask 11008) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 37) (ok32 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c14337 (hi : ineligSet 17 D⊆mask 14337) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 38) (ok32 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16466 (hi : ineligSet 17 D⊆mask 16466) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 39) (ok32 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16522 (hi : ineligSet 17 D⊆mask 16522) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 40) (ok40 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16578 (hi : ineligSet 17 D⊆mask 16578) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 41) (ok40 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16913 (hi : ineligSet 17 D⊆mask 16913) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 42) (ok40 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c17280 (hi : ineligSet 17 D⊆mask 17280) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 43) (ok40 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c17417 (hi : ineligSet 17 D⊆mask 17417) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 44) (ok40 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18512 (hi : ineligSet 17 D⊆mask 18512) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 45) (ok40 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18624 (hi : ineligSet 17 D⊆mask 18624) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 46) (ok40 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19520 (hi : ineligSet 17 D⊆mask 19520) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 47) (ok40 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c25664 (hi : ineligSet 17 D⊆mask 25664) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 48) (ok48 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31 (hi : ineligSet 17 D⊆mask 31) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 49) (ok48 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c47 (hi : ineligSet 17 D⊆mask 47) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 50) (ok48 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c55 (hi : ineligSet 17 D⊆mask 55) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 51) (ok48 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c59 (hi : ineligSet 17 D⊆mask 59) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 52) (ok48 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c61 (hi : ineligSet 17 D⊆mask 61) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 53) (ok48 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c62 (hi : ineligSet 17 D⊆mask 62) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 54) (ok48 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c118 (hi : ineligSet 17 D⊆mask 118) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 55) (ok48 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c174 (hi : ineligSet 17 D⊆mask 174) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 56) (ok56 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c230 (hi : ineligSet 17 D⊆mask 230) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 57) (ok56 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c286 (hi : ineligSet 17 D⊆mask 286) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 58) (ok56 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c342 (hi : ineligSet 17 D⊆mask 342) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 59) (ok56 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c398 (hi : ineligSet 17 D⊆mask 398) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 60) (ok56 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c454 (hi : ineligSet 17 D⊆mask 454) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 61) (ok56 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c565 (hi : ineligSet 17 D⊆mask 565) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 62) (ok56 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c628 (hi : ineligSet 17 D⊆mask 628) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 63) (ok56 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c740 (hi : ineligSet 17 D⊆mask 740) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c676 live corr hw ne
    intro v hv
    have vv : v∈mask 740 := hi hv
    have reduced : ∀ a:V, a∈mask 740 → a≠6 → a∈mask 676 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 64) (ok64 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 64 → a=6 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1069 (hi : ineligSet 17 D⊆mask 1069) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 65) (ok64 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1196 (hi : ineligSet 17 D⊆mask 1196) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 66) (ok64 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1252 (hi : ineligSet 17 D⊆mask 1252) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c1124 live corr hw ne
    intro v hv
    have vv : v∈mask 1252 := hi hv
    have reduced : ∀ a:V, a∈mask 1252 → a≠7 → a∈mask 1124 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 67) (ok64 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1573 (hi : ineligSet 17 D⊆mask 1573) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 68) (ok64 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2077 (hi : ineligSet 17 D⊆mask 2077) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 69) (ok64 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2332 (hi : ineligSet 17 D⊆mask 2332) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 70) (ok64 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2388 (hi : ineligSet 17 D⊆mask 2388) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c2132 live corr hw ne
    intro v hv
    have vv : v∈mask 2388 := hi hv
    have reduced : ∀ a:V, a∈mask 2388 → a≠8 → a∈mask 2132 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 71) (ok64 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2581 (hi : ineligSet 17 D⊆mask 2581) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 72) (ok72 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2756 (hi : ineligSet 17 D⊆mask 2756) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c2244 live corr hw ne
    intro v hv
    have vv : v∈mask 2756 := hi hv
    have reduced : ∀ a:V, a∈mask 2756 → a≠9 → a∈mask 2244 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 73) (ok72 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2836 (hi : ineligSet 17 D⊆mask 2836) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c788 live corr hw ne
    intro v hv
    have vv : v∈mask 2836 := hi hv
    have reduced : ∀ a:V, a∈mask 2836 → a≠11 → a∈mask 788 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 74) (ok72 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3085 (hi : ineligSet 17 D⊆mask 3085) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 75) (ok72 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3212 (hi : ineligSet 17 D⊆mask 3212) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c2188 live corr hw ne
    intro v hv
    have vv : v∈mask 3212 := hi hv
    have reduced : ∀ a:V, a∈mask 3212 → a≠10 → a∈mask 2188 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 76) (ok72 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3340 (hi : ineligSet 17 D⊆mask 3340) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c1292 live corr hw ne
    intro v hv
    have vv : v∈mask 3340 := hi hv
    have reduced : ∀ a:V, a∈mask 3340 → a≠11 → a∈mask 1292 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 77) (ok72 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3396 (hi : ineligSet 17 D⊆mask 3396) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c3140 live corr hw ne
    intro v hv
    have vv : v∈mask 3396 := hi hv
    have reduced : ∀ a:V, a∈mask 3396 → a≠8 → a∈mask 3140 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 78) (ok72 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3589 (hi : ineligSet 17 D⊆mask 3589) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 79) (ok72 7) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4147 (hi : ineligSet 17 D⊆mask 4147) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 80) (ok80 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4210 (hi : ineligSet 17 D⊆mask 4210) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 81) (ok80 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4322 (hi : ineligSet 17 D⊆mask 4322) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c4258 live corr hw ne
    intro v hv
    have vv : v∈mask 4322 := hi hv
    have reduced : ∀ a:V, a∈mask 4322 → a≠6 → a∈mask 4258 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 82) (ok80 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 64 → a=6 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4657 (hi : ineligSet 17 D⊆mask 4657) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 83) (ok80 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4720 (hi : ineligSet 17 D⊆mask 4720) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 84) (ok80 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c6673 (hi : ineligSet 17 D⊆mask 6673) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c6161 live corr hw ne
    intro v hv
    have vv : v∈mask 6673 := hi hv
    have reduced : ∀ a:V, a∈mask 6673 → a≠9 → a∈mask 6161 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 85) (ok80 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c6928 (hi : ineligSet 17 D⊆mask 6928) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c6416 live corr hw ne
    intro v hv
    have vv : v∈mask 6928 := hi hv
    have reduced : ∀ a:V, a∈mask 6928 → a≠9 → a∈mask 6416 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 86) (ok80 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c7040 (hi : ineligSet 17 D⊆mask 7040) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c6528 live corr hw ne
    intro v hv
    have vv : v∈mask 7040 := hi hv
    have reduced : ∀ a:V, a∈mask 7040 → a≠9 → a∈mask 6528 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 87) (ok80 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c7488 (hi : ineligSet 17 D⊆mask 7488) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 88) (ok88 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8235 (hi : ineligSet 17 D⊆mask 8235) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 89) (ok88 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8362 (hi : ineligSet 17 D⊆mask 8362) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 90) (ok88 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8418 (hi : ineligSet 17 D⊆mask 8418) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c8290 live corr hw ne
    intro v hv
    have vv : v∈mask 8418 := hi hv
    have reduced : ∀ a:V, a∈mask 8418 → a≠7 → a∈mask 8290 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 91) (ok88 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c8586 (hi : ineligSet 17 D⊆mask 8586) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c8458 live corr hw ne
    intro v hv
    have vv : v∈mask 8586 := hi hv
    have reduced : ∀ a:V, a∈mask 8586 → a≠7 → a∈mask 8458 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 92) (ok88 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9257 (hi : ineligSet 17 D⊆mask 9257) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 93) (ok88 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9384 (hi : ineligSet 17 D⊆mask 9384) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 94) (ok88 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9824 (hi : ineligSet 17 D⊆mask 9824) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c9312 live corr hw ne
    intro v hv
    have vv : v∈mask 9824 := hi hv
    have reduced : ∀ a:V, a∈mask 9824 → a≠9 → a∈mask 9312 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 95) (ok88 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c10944 (hi : ineligSet 17 D⊆mask 10944) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c10432 live corr hw ne
    intro v hv
    have vv : v∈mask 10944 := hi hv
    have reduced : ∀ a:V, a∈mask 10944 → a≠9 → a∈mask 10432 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 96) (ok96 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11072 (hi : ineligSet 17 D⊆mask 11072) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c10560 live corr hw ne
    intro v hv
    have vv : v∈mask 11072 := hi hv
    have reduced : ∀ a:V, a∈mask 11072 → a≠9 → a∈mask 10560 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 97) (ok96 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11136 (hi : ineligSet 17 D⊆mask 11136) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c11008 live corr hw ne
    intro v hv
    have vv : v∈mask 11136 := hi hv
    have reduced : ∀ a:V, a∈mask 11136 → a≠7 → a∈mask 11008 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 98) (ok96 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11273 (hi : ineligSet 17 D⊆mask 11273) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c10249 live corr hw ne
    intro v hv
    have vv : v∈mask 11273 := hi hv
    have reduced : ∀ a:V, a∈mask 11273 → a≠10 → a∈mask 10249 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 99) (ok96 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11528 (hi : ineligSet 17 D⊆mask 11528) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c10504 live corr hw ne
    intro v hv
    have vv : v∈mask 11528 := hi hv
    have reduced : ∀ a:V, a∈mask 11528 → a≠10 → a∈mask 10504 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 100) (ok96 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11584 (hi : ineligSet 17 D⊆mask 11584) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 101) (ok96 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12323 (hi : ineligSet 17 D⊆mask 12323) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 102) (ok96 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12833 (hi : ineligSet 17 D⊆mask 12833) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c8737 live corr hw ne
    intro v hv
    have vv : v∈mask 12833 := hi hv
    have reduced : ∀ a:V, a∈mask 12833 → a≠12 → a∈mask 8737 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 103) (ok96 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12960 (hi : ineligSet 17 D⊆mask 12960) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c8864 live corr hw ne
    intro v hv
    have vv : v∈mask 12960 := hi hv
    have reduced : ∀ a:V, a∈mask 12960 → a≠12 → a∈mask 8864 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 104) (ok104 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c13345 (hi : ineligSet 17 D⊆mask 13345) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c5153 live corr hw ne
    intro v hv
    have vv : v∈mask 13345 := hi hv
    have reduced : ∀ a:V, a∈mask 13345 → a≠13 → a∈mask 5153 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 105) (ok104 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 8192 → a=13 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15361 (hi : ineligSet 17 D⊆mask 15361) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c14337 live corr hw ne
    intro v hv
    have vv : v∈mask 15361 := hi hv
    have reduced : ∀ a:V, a∈mask 15361 → a≠10 → a∈mask 14337 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 106) (ok104 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15424 (hi : ineligSet 17 D⊆mask 15424) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 107) (ok104 3) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15616 (hi : ineligSet 17 D⊆mask 15616) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 108) (ok104 4) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16411 (hi : ineligSet 17 D⊆mask 16411) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 109) (ok104 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16666 (hi : ineligSet 17 D⊆mask 16666) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 110) (ok104 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16722 (hi : ineligSet 17 D⊆mask 16722) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c16466 live corr hw ne
    intro v hv
    have vv : v∈mask 16722 := hi hv
    have reduced : ∀ a:V, a∈mask 16722 → a≠8 → a∈mask 16466 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 111) (ok104 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16778 (hi : ineligSet 17 D⊆mask 16778) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c16522 live corr hw ne
    intro v hv
    have vv : v∈mask 16778 := hi hv
    have reduced : ∀ a:V, a∈mask 16778 → a≠8 → a∈mask 16522 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 112) (ok112 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18457 (hi : ineligSet 17 D⊆mask 18457) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 113) (ok112 1) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18712 (hi : ineligSet 17 D⊆mask 18712) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 114) (ok112 2) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c18961 (hi : ineligSet 17 D⊆mask 18961) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c16913 live corr hw ne
    intro v hv
    have vv : v∈mask 18961 := hi hv
    have reduced : ∀ a:V, a∈mask 18961 → a≠11 → a∈mask 16913 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 115) (ok112 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19024 (hi : ineligSet 17 D⊆mask 19024) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c18512 live corr hw ne
    intro v hv
    have vv : v∈mask 19024 := hi hv
    have reduced : ∀ a:V, a∈mask 19024 → a≠9 → a∈mask 18512 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 116) (ok112 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19136 (hi : ineligSet 17 D⊆mask 19136) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c18624 live corr hw ne
    intro v hv
    have vv : v∈mask 19136 := hi hv
    have reduced : ∀ a:V, a∈mask 19136 → a≠9 → a∈mask 18624 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 117) (ok112 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19465 (hi : ineligSet 17 D⊆mask 19465) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c17417 live corr hw ne
    intro v hv
    have vv : v∈mask 19465 := hi hv
    have reduced : ∀ a:V, a∈mask 19465 → a≠11 → a∈mask 17417 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 118) (ok112 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19648 (hi : ineligSet 17 D⊆mask 19648) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c19520 live corr hw ne
    intro v hv
    have vv : v∈mask 19648 := hi hv
    have reduced : ∀ a:V, a∈mask 19648 → a≠7 → a∈mask 19520 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 119) (ok112 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20499 (hi : ineligSet 17 D⊆mask 20499) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 120) (ok120 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20674 (hi : ineligSet 17 D⊆mask 20674) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c16578 live corr hw ne
    intro v hv
    have vv : v∈mask 20674 := hi hv
    have reduced : ∀ a:V, a∈mask 20674 → a≠12 → a∈mask 16578 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 121) (ok120 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20754 (hi : ineligSet 17 D⊆mask 20754) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c4370 live corr hw ne
    intro v hv
    have vv : v∈mask 20754 := hi hv
    have reduced : ∀ a:V, a∈mask 20754 → a≠14 → a∈mask 4370 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 122) (ok120 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c21376 (hi : ineligSet 17 D⊆mask 21376) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c17280 live corr hw ne
    intro v hv
    have vv : v∈mask 21376 := hi hv
    have reduced : ∀ a:V, a∈mask 21376 → a≠12 → a∈mask 17280 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 123) (ok120 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c21888 (hi : ineligSet 17 D⊆mask 21888) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c5504 live corr hw ne
    intro v hv
    have vv : v∈mask 21888 := hi hv
    have reduced : ∀ a:V, a∈mask 21888 → a≠14 → a∈mask 5504 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 124) (ok120 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23680 (hi : ineligSet 17 D⊆mask 23680) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c7296 live corr hw ne
    intro v hv
    have vv : v∈mask 23680 := hi hv
    have reduced : ∀ a:V, a∈mask 23680 → a≠14 → a∈mask 7296 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 125) (ok120 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24587 (hi : ineligSet 17 D⊆mask 24587) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 126) (ok120 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24898 (hi : ineligSet 17 D⊆mask 24898) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c8514 live corr hw ne
    intro v hv
    have vv : v∈mask 24898 := hi hv
    have reduced : ∀ a:V, a∈mask 24898 → a≠14 → a∈mask 8514 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 127) (ok120 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c25408 (hi : ineligSet 17 D⊆mask 25408) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 128) (ok128 0) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c25920 (hi : ineligSet 17 D⊆mask 25920) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c9536 live corr hw ne
    intro v hv
    have vv : v∈mask 25920 := hi hv
    have reduced : ∀ a:V, a∈mask 25920 → a≠14 → a∈mask 9536 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 129) (ok128 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c26176 (hi : ineligSet 17 D⊆mask 26176) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c25664 live corr hw ne
    intro v hv
    have vv : v∈mask 26176 := hi hv
    have reduced : ∀ a:V, a∈mask 26176 → a≠9 → a∈mask 25664 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 130) (ok128 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c26760 (hi : ineligSet 17 D⊆mask 26760) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c10376 live corr hw ne
    intro v hv
    have vv : v∈mask 26760 := hi hv
    have reduced : ∀ a:V, a∈mask 26760 → a≠14 → a∈mask 10376 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 131) (ok128 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27137 (hi : ineligSet 17 D⊆mask 27137) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c10753 live corr hw ne
    intro v hv
    have vv : v∈mask 27137 := hi hv
    have reduced : ∀ a:V, a∈mask 27137 → a≠14 → a∈mask 10753 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 132) (ok128 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28675 (hi : ineligSet 17 D⊆mask 28675) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 133) (ok128 5) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c63 (hi : ineligSet 17 D⊆mask 63) : 33+Bzero 17 D≤D.length+3 := by
  refine applyRow live corr true hw 3 (row 134) (ok128 6) ?_ hi
  intro v hv
  exact False.elim ((by decide +kernel : ∀ a:V,a∉mask 0) v hv)
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c1764 (hi : ineligSet 17 D⊆mask 1764) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c1252 live corr hw ne
    intro v hv
    have vv : v∈mask 1764 := hi hv
    have reduced : ∀ a:V, a∈mask 1764 → a≠9 → a∈mask 1252 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c740 live corr hw ne
    intro v hv
    have vv : v∈mask 1764 := hi hv
    have reduced : ∀ a:V, a∈mask 1764 → a≠10 → a∈mask 740 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 135) (ok128 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c2900 (hi : ineligSet 17 D⊆mask 2900) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c2836 live corr hw ne
    intro v hv
    have vv : v∈mask 2900 := hi hv
    have reduced : ∀ a:V, a∈mask 2900 → a≠6 → a∈mask 2836 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c2388 live corr hw ne
    intro v hv
    have vv : v∈mask 2900 := hi hv
    have reduced : ∀ a:V, a∈mask 2900 → a≠9 → a∈mask 2388 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 136) (ok136 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 576 → a=6 ∨ a=9 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3012 (hi : ineligSet 17 D⊆mask 3012) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c2756 live corr hw ne
    intro v hv
    have vv : v∈mask 3012 := hi hv
    have reduced : ∀ a:V, a∈mask 3012 → a≠8 → a∈mask 2756 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 137) (ok136 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3468 (hi : ineligSet 17 D⊆mask 3468) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c3340 live corr hw ne
    intro v hv
    have vv : v∈mask 3468 := hi hv
    have reduced : ∀ a:V, a∈mask 3468 → a≠7 → a∈mask 3340 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c3212 live corr hw ne
    intro v hv
    have vv : v∈mask 3468 := hi hv
    have reduced : ∀ a:V, a∈mask 3468 → a≠8 → a∈mask 3212 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 138) (ok136 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 384 → a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c3524 (hi : ineligSet 17 D⊆mask 3524) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c3396 live corr hw ne
    intro v hv
    have vv : v∈mask 3524 := hi hv
    have reduced : ∀ a:V, a∈mask 3524 → a≠7 → a∈mask 3396 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 139) (ok136 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c9952 (hi : ineligSet 17 D⊆mask 9952) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c9824 live corr hw ne
    intro v hv
    have vv : v∈mask 9952 := hi hv
    have reduced : ∀ a:V, a∈mask 9952 → a≠7 → a∈mask 9824 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 140) (ok136 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c11656 (hi : ineligSet 17 D⊆mask 11656) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c11528 live corr hw ne
    intro v hv
    have vv : v∈mask 11656 := hi hv
    have reduced : ∀ a:V, a∈mask 11656 → a≠7 → a∈mask 11528 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 141) (ok136 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c12514 (hi : ineligSet 17 D⊆mask 12514) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c8418 live corr hw ne
    intro v hv
    have vv : v∈mask 12514 := hi hv
    have reduced : ∀ a:V, a∈mask 12514 → a≠12 → a∈mask 8418 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c4322 live corr hw ne
    intro v hv
    have vv : v∈mask 12514 := hi hv
    have reduced : ∀ a:V, a∈mask 12514 → a≠13 → a∈mask 4322 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 142) (ok136 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c13857 (hi : ineligSet 17 D⊆mask 13857) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c13345 live corr hw ne
    intro v hv
    have vv : v∈mask 13857 := hi hv
    have reduced : ∀ a:V, a∈mask 13857 → a≠9 → a∈mask 13345 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c12833 live corr hw ne
    intro v hv
    have vv : v∈mask 13857 := hi hv
    have reduced : ∀ a:V, a∈mask 13857 → a≠10 → a∈mask 12833 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 143) (ok136 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c13984 (hi : ineligSet 17 D⊆mask 13984) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c12960 live corr hw ne
    intro v hv
    have vv : v∈mask 13984 := hi hv
    have reduced : ∀ a:V, a∈mask 13984 → a≠10 → a∈mask 12960 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 144) (ok144 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15232 (hi : ineligSet 17 D⊆mask 15232) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c11136 live corr hw ne
    intro v hv
    have vv : v∈mask 15232 := hi hv
    have reduced : ∀ a:V, a∈mask 15232 → a≠12 → a∈mask 11136 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c7040 live corr hw ne
    intro v hv
    have vv : v∈mask 15232 := hi hv
    have reduced : ∀ a:V, a∈mask 15232 → a≠13 → a∈mask 7040 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 145) (ok144 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15552 (hi : ineligSet 17 D⊆mask 15552) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c15424 live corr hw ne
    intro v hv
    have vv : v∈mask 15552 := hi hv
    have reduced : ∀ a:V, a∈mask 15552 → a≠7 → a∈mask 15424 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 146) (ok144 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15680 (hi : ineligSet 17 D⊆mask 15680) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c11584 live corr hw ne
    intro v hv
    have vv : v∈mask 15680 := hi hv
    have reduced : ∀ a:V, a∈mask 15680 → a≠12 → a∈mask 11584 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c7488 live corr hw ne
    intro v hv
    have vv : v∈mask 15680 := hi hv
    have reduced : ∀ a:V, a∈mask 15680 → a≠13 → a∈mask 7488 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 147) (ok144 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c15744 (hi : ineligSet 17 D⊆mask 15744) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c15616 live corr hw ne
    intro v hv
    have vv : v∈mask 15744 := hi hv
    have reduced : ∀ a:V, a∈mask 15744 → a≠7 → a∈mask 15616 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 148) (ok144 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c19280 (hi : ineligSet 17 D⊆mask 19280) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c19024 live corr hw ne
    intro v hv
    have vv : v∈mask 19280 := hi hv
    have reduced : ∀ a:V, a∈mask 19280 → a≠8 → a∈mask 19024 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 149) (ok144 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20818 (hi : ineligSet 17 D⊆mask 20818) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c20754 live corr hw ne
    intro v hv
    have vv : v∈mask 20818 := hi hv
    have reduced : ∀ a:V, a∈mask 20818 → a≠6 → a∈mask 20754 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c16722 live corr hw ne
    intro v hv
    have vv : v∈mask 20818 := hi hv
    have reduced : ∀ a:V, a∈mask 20818 → a≠12 → a∈mask 16722 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 150) (ok144 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4160 → a=6 ∨ a=12 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c20930 (hi : ineligSet 17 D⊆mask 20930) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c20674 live corr hw ne
    intro v hv
    have vv : v∈mask 20930 := hi hv
    have reduced : ∀ a:V, a∈mask 20930 → a≠8 → a∈mask 20674 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 151) (ok144 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 256 → a=8 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c22400 (hi : ineligSet 17 D⊆mask 22400) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c21888 live corr hw ne
    intro v hv
    have vv : v∈mask 22400 := hi hv
    have reduced : ∀ a:V, a∈mask 22400 → a≠9 → a∈mask 21888 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c21376 live corr hw ne
    intro v hv
    have vv : v∈mask 22400 := hi hv
    have reduced : ∀ a:V, a∈mask 22400 → a≠10 → a∈mask 21376 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 152) (ok152 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23057 (hi : ineligSet 17 D⊆mask 23057) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c18961 live corr hw ne
    intro v hv
    have vv : v∈mask 23057 := hi hv
    have reduced : ∀ a:V, a∈mask 23057 → a≠12 → a∈mask 18961 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c6673 live corr hw ne
    intro v hv
    have vv : v∈mask 23057 := hi hv
    have reduced : ∀ a:V, a∈mask 23057 → a≠14 → a∈mask 6673 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 153) (ok152 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 20480 → a=12 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23312 (hi : ineligSet 17 D⊆mask 23312) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c6928 live corr hw ne
    intro v hv
    have vv : v∈mask 23312 := hi hv
    have reduced : ∀ a:V, a∈mask 23312 → a≠14 → a∈mask 6928 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 154) (ok152 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23744 (hi : ineligSet 17 D⊆mask 23744) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c23680 live corr hw ne
    intro v hv
    have vv : v∈mask 23744 := hi hv
    have reduced : ∀ a:V, a∈mask 23744 → a≠6 → a∈mask 23680 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c19648 live corr hw ne
    intro v hv
    have vv : v∈mask 23744 := hi hv
    have reduced : ∀ a:V, a∈mask 23744 → a≠12 → a∈mask 19648 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 155) (ok152 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4160 → a=6 ∨ a=12 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23872 (hi : ineligSet 17 D⊆mask 23872) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c7488 live corr hw ne
    intro v hv
    have vv : v∈mask 23872 := hi hv
    have reduced : ∀ a:V, a∈mask 23872 → a≠14 → a∈mask 7488 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 156) (ok152 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24970 (hi : ineligSet 17 D⊆mask 24970) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c16778 live corr hw ne
    intro v hv
    have vv : v∈mask 24970 := hi hv
    have reduced : ∀ a:V, a∈mask 24970 → a≠13 → a∈mask 16778 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c8586 live corr hw ne
    intro v hv
    have vv : v∈mask 24970 := hi hv
    have reduced : ∀ a:V, a∈mask 24970 → a≠14 → a∈mask 8586 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 157) (ok152 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 24576 → a=13 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c25026 (hi : ineligSet 17 D⊆mask 25026) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c24898 live corr hw ne
    intro v hv
    have vv : v∈mask 25026 := hi hv
    have reduced : ∀ a:V, a∈mask 25026 → a≠7 → a∈mask 24898 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 158) (ok152 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c26304 (hi : ineligSet 17 D⊆mask 26304) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c26176 live corr hw ne
    intro v hv
    have vv : v∈mask 26304 := hi hv
    have reduced : ∀ a:V, a∈mask 26304 → a≠7 → a∈mask 26176 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 159) (ok152 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 128 → a=7 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c26432 (hi : ineligSet 17 D⊆mask 26432) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c25920 live corr hw ne
    intro v hv
    have vv : v∈mask 26432 := hi hv
    have reduced : ∀ a:V, a∈mask 26432 → a≠9 → a∈mask 25920 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c25408 live corr hw ne
    intro v hv
    have vv : v∈mask 26432 := hi hv
    have reduced : ∀ a:V, a∈mask 26432 → a≠10 → a∈mask 25408 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 160) (ok160 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27328 (hi : ineligSet 17 D⊆mask 27328) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c19136 live corr hw ne
    intro v hv
    have vv : v∈mask 27328 := hi hv
    have reduced : ∀ a:V, a∈mask 27328 → a≠13 → a∈mask 19136 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c10944 live corr hw ne
    intro v hv
    have vv : v∈mask 27328 := hi hv
    have reduced : ∀ a:V, a∈mask 27328 → a≠14 → a∈mask 10944 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 161) (ok160 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 24576 → a=13 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27456 (hi : ineligSet 17 D⊆mask 27456) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11072 live corr hw ne
    intro v hv
    have vv : v∈mask 27456 := hi hv
    have reduced : ∀ a:V, a∈mask 27456 → a≠14 → a∈mask 11072 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 162) (ok160 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27520 (hi : ineligSet 17 D⊆mask 27520) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11136 live corr hw ne
    intro v hv
    have vv : v∈mask 27520 := hi hv
    have reduced : ∀ a:V, a∈mask 27520 → a≠14 → a∈mask 11136 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 163) (ok160 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27657 (hi : ineligSet 17 D⊆mask 27657) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c19465 live corr hw ne
    intro v hv
    have vv : v∈mask 27657 := hi hv
    have reduced : ∀ a:V, a∈mask 27657 → a≠13 → a∈mask 19465 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11273 live corr hw ne
    intro v hv
    have vv : v∈mask 27657 := hi hv
    have reduced : ∀ a:V, a∈mask 27657 → a≠14 → a∈mask 11273 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 164) (ok160 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 24576 → a=13 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c27784 (hi : ineligSet 17 D⊆mask 27784) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c26760 live corr hw ne
    intro v hv
    have vv : v∈mask 27784 := hi hv
    have reduced : ∀ a:V, a∈mask 27784 → a≠10 → a∈mask 26760 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 165) (ok160 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31233 (hi : ineligSet 17 D⊆mask 31233) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c27137 live corr hw ne
    intro v hv
    have vv : v∈mask 31233 := hi hv
    have reduced : ∀ a:V, a∈mask 31233 → a≠12 → a∈mask 27137 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 166) (ok160 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31745 (hi : ineligSet 17 D⊆mask 31745) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c15361 live corr hw ne
    intro v hv
    have vv : v∈mask 31745 := hi hv
    have reduced : ∀ a:V, a∈mask 31745 → a≠14 → a∈mask 15361 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 167) (ok160 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c4036 (hi : ineligSet 17 D⊆mask 4036) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c3524 live corr hw ne
    intro v hv
    have vv : v∈mask 4036 := hi hv
    have reduced : ∀ a:V, a∈mask 4036 → a≠9 → a∈mask 3524 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c3012 live corr hw ne
    intro v hv
    have vv : v∈mask 4036 := hi hv
    have reduced : ∀ a:V, a∈mask 4036 → a≠10 → a∈mask 3012 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 168) (ok168 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c14048 (hi : ineligSet 17 D⊆mask 14048) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c13984 live corr hw ne
    intro v hv
    have vv : v∈mask 14048 := hi hv
    have reduced : ∀ a:V, a∈mask 14048 → a≠6 → a∈mask 13984 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c9952 live corr hw ne
    intro v hv
    have vv : v∈mask 14048 := hi hv
    have reduced : ∀ a:V, a∈mask 14048 → a≠12 → a∈mask 9952 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 169) (ok168 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4160 → a=6 ∨ a=12 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16064 (hi : ineligSet 17 D⊆mask 16064) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c15552 live corr hw ne
    intro v hv
    have vv : v∈mask 16064 := hi hv
    have reduced : ∀ a:V, a∈mask 16064 → a≠9 → a∈mask 15552 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 170) (ok168 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16192 (hi : ineligSet 17 D⊆mask 16192) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c15680 live corr hw ne
    intro v hv
    have vv : v∈mask 16192 := hi hv
    have reduced : ∀ a:V, a∈mask 16192 → a≠9 → a∈mask 15680 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 171) (ok168 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16256 (hi : ineligSet 17 D⊆mask 16256) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c15232 live corr hw ne
    intro v hv
    have vv : v∈mask 16256 := hi hv
    have reduced : ∀ a:V, a∈mask 16256 → a≠10 → a∈mask 15232 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 172) (ok168 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c23376 (hi : ineligSet 17 D⊆mask 23376) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c23312 live corr hw ne
    intro v hv
    have vv : v∈mask 23376 := hi hv
    have reduced : ∀ a:V, a∈mask 23376 → a≠6 → a∈mask 23312 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c19280 live corr hw ne
    intro v hv
    have vv : v∈mask 23376 := hi hv
    have reduced : ∀ a:V, a∈mask 23376 → a≠12 → a∈mask 19280 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 173) (ok168 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4160 → a=6 ∨ a=12 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24256 (hi : ineligSet 17 D⊆mask 24256) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c23744 live corr hw ne
    intro v hv
    have vv : v∈mask 24256 := hi hv
    have reduced : ∀ a:V, a∈mask 24256 → a≠9 → a∈mask 23744 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 174) (ok168 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24384 (hi : ineligSet 17 D⊆mask 24384) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c23872 live corr hw ne
    intro v hv
    have vv : v∈mask 24384 := hi hv
    have reduced : ∀ a:V, a∈mask 24384 → a≠9 → a∈mask 23872 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 175) (ok168 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 512 → a=9 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24448 (hi : ineligSet 17 D⊆mask 24448) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c22400 live corr hw ne
    intro v hv
    have vv : v∈mask 24448 := hi hv
    have reduced : ∀ a:V, a∈mask 24448 → a≠11 → a∈mask 22400 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 176) (ok176 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28040 (hi : ineligSet 17 D⊆mask 28040) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c27784 live corr hw ne
    intro v hv
    have vv : v∈mask 28040 := hi hv
    have reduced : ∀ a:V, a∈mask 28040 → a≠8 → a∈mask 27784 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c11656 live corr hw ne
    intro v hv
    have vv : v∈mask 28040 := hi hv
    have reduced : ∀ a:V, a∈mask 28040 → a≠14 → a∈mask 11656 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 177) (ok176 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16640 → a=8 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28352 (hi : ineligSet 17 D⊆mask 28352) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c27328 live corr hw ne
    intro v hv
    have vv : v∈mask 28352 := hi hv
    have reduced : ∀ a:V, a∈mask 28352 → a≠10 → a∈mask 27328 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 178) (ok176 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28480 (hi : ineligSet 17 D⊆mask 28480) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c26432 live corr hw ne
    intro v hv
    have vv : v∈mask 28480 := hi hv
    have reduced : ∀ a:V, a∈mask 28480 → a≠11 → a∈mask 26432 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 179) (ok176 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 2048 → a=11 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28544 (hi : ineligSet 17 D⊆mask 28544) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c27520 live corr hw ne
    intro v hv
    have vv : v∈mask 28544 := hi hv
    have reduced : ∀ a:V, a∈mask 28544 → a≠10 → a∈mask 27520 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 180) (ok176 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1024 → a=10 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c29122 (hi : ineligSet 17 D⊆mask 29122) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c25026 live corr hw ne
    intro v hv
    have vv : v∈mask 29122 := hi hv
    have reduced : ∀ a:V, a∈mask 29122 → a≠12 → a∈mask 25026 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c20930 live corr hw ne
    intro v hv
    have vv : v∈mask 29122 := hi hv
    have reduced : ∀ a:V, a∈mask 29122 → a≠13 → a∈mask 20930 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 181) (ok176 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 12288 → a=12 ∨ a=13 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c30400 (hi : ineligSet 17 D⊆mask 30400) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c26304 live corr hw ne
    intro v hv
    have vv : v∈mask 30400 := hi hv
    have reduced : ∀ a:V, a∈mask 30400 → a≠12 → a∈mask 26304 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 182) (ok176 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c30528 (hi : ineligSet 17 D⊆mask 30528) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c26432 live corr hw ne
    intro v hv
    have vv : v∈mask 30528 := hi hv
    have reduced : ∀ a:V, a∈mask 30528 → a≠12 → a∈mask 26432 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 183) (ok176 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c30592 (hi : ineligSet 17 D⊆mask 30592) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c22400 live corr hw ne
    intro v hv
    have vv : v∈mask 30592 := hi hv
    have reduced : ∀ a:V, a∈mask 30592 → a≠13 → a∈mask 22400 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 184) (ok184 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 8192 → a=13 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31424 (hi : ineligSet 17 D⊆mask 31424) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c27328 live corr hw ne
    intro v hv
    have vv : v∈mask 31424 := hi hv
    have reduced : ∀ a:V, a∈mask 31424 → a≠12 → a∈mask 27328 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 185) (ok184 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31552 (hi : ineligSet 17 D⊆mask 31552) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c27456 live corr hw ne
    intro v hv
    have vv : v∈mask 31552 := hi hv
    have reduced : ∀ a:V, a∈mask 31552 → a≠12 → a∈mask 27456 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 186) (ok184 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 4096 → a=12 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31616 (hi : ineligSet 17 D⊆mask 31616) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c15232 live corr hw ne
    intro v hv
    have vv : v∈mask 31616 := hi hv
    have reduced : ∀ a:V, a∈mask 31616 → a≠14 → a∈mask 15232 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 187) (ok184 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31936 (hi : ineligSet 17 D⊆mask 31936) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c23744 live corr hw ne
    intro v hv
    have vv : v∈mask 31936 := hi hv
    have reduced : ∀ a:V, a∈mask 31936 → a≠13 → a∈mask 23744 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 188) (ok184 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 8192 → a=13 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32064 (hi : ineligSet 17 D⊆mask 32064) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c15680 live corr hw ne
    intro v hv
    have vv : v∈mask 32064 := hi hv
    have reduced : ∀ a:V, a∈mask 32064 → a≠14 → a∈mask 15680 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 189) (ok184 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32128 (hi : ineligSet 17 D⊆mask 32128) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c15744 live corr hw ne
    intro v hv
    have vv : v∈mask 32128 := hi hv
    have reduced : ∀ a:V, a∈mask 32128 → a≠14 → a∈mask 15744 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 190) (ok184 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 16384 → a=14 := by decide +kernel
  rcases list v hv with rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32257 (hi : ineligSet 17 D⊆mask 32257) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c31745 live corr hw ne
    intro v hv
    have vv : v∈mask 32257 := hi hv
    have reduced : ∀ a:V, a∈mask 32257 → a≠9 → a∈mask 31745 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c31233 live corr hw ne
    intro v hv
    have vv : v∈mask 32257 := hi hv
    have reduced : ∀ a:V, a∈mask 32257 → a≠10 → a∈mask 31233 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 191) (ok184 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 1536 → a=9 ∨ a=10 := by decide +kernel
  rcases list v hv with rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c16320 (hi : ineligSet 17 D⊆mask 16320) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c16256 live corr hw ne
    intro v hv
    have vv : v∈mask 16320 := hi hv
    have reduced : ∀ a:V, a∈mask 16320 → a≠6 → a∈mask 16256 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c16192 live corr hw ne
    intro v hv
    have vv : v∈mask 16320 := hi hv
    have reduced : ∀ a:V, a∈mask 16320 → a≠7 → a∈mask 16192 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c16064 live corr hw ne
    intro v hv
    have vv : v∈mask 16320 := hi hv
    have reduced : ∀ a:V, a∈mask 16320 → a≠8 → a∈mask 16064 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 192) (ok192 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c24512 (hi : ineligSet 17 D⊆mask 24512) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c24448 live corr hw ne
    intro v hv
    have vv : v∈mask 24512 := hi hv
    have reduced : ∀ a:V, a∈mask 24512 → a≠6 → a∈mask 24448 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c24384 live corr hw ne
    intro v hv
    have vv : v∈mask 24512 := hi hv
    have reduced : ∀ a:V, a∈mask 24512 → a≠7 → a∈mask 24384 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c24256 live corr hw ne
    intro v hv
    have vv : v∈mask 24512 := hi hv
    have reduced : ∀ a:V, a∈mask 24512 → a≠8 → a∈mask 24256 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 193) (ok192 1) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c28608 (hi : ineligSet 17 D⊆mask 28608) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c28544 live corr hw ne
    intro v hv
    have vv : v∈mask 28608 := hi hv
    have reduced : ∀ a:V, a∈mask 28608 → a≠6 → a∈mask 28544 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c28480 live corr hw ne
    intro v hv
    have vv : v∈mask 28608 := hi hv
    have reduced : ∀ a:V, a∈mask 28608 → a≠7 → a∈mask 28480 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c28352 live corr hw ne
    intro v hv
    have vv : v∈mask 28608 := hi hv
    have reduced : ∀ a:V, a∈mask 28608 → a≠8 → a∈mask 28352 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 194) (ok192 2) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c30656 (hi : ineligSet 17 D⊆mask 30656) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c30592 live corr hw ne
    intro v hv
    have vv : v∈mask 30656 := hi hv
    have reduced : ∀ a:V, a∈mask 30656 → a≠6 → a∈mask 30592 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c30528 live corr hw ne
    intro v hv
    have vv : v∈mask 30656 := hi hv
    have reduced : ∀ a:V, a∈mask 30656 → a≠7 → a∈mask 30528 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c30400 live corr hw ne
    intro v hv
    have vv : v∈mask 30656 := hi hv
    have reduced : ∀ a:V, a∈mask 30656 → a≠8 → a∈mask 30400 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 195) (ok192 3) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c31680 (hi : ineligSet 17 D⊆mask 31680) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c31616 live corr hw ne
    intro v hv
    have vv : v∈mask 31680 := hi hv
    have reduced : ∀ a:V, a∈mask 31680 → a≠6 → a∈mask 31616 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c31552 live corr hw ne
    intro v hv
    have vv : v∈mask 31680 := hi hv
    have reduced : ∀ a:V, a∈mask 31680 → a≠7 → a∈mask 31552 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c31424 live corr hw ne
    intro v hv
    have vv : v∈mask 31680 := hi hv
    have reduced : ∀ a:V, a∈mask 31680 → a≠8 → a∈mask 31424 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 196) (ok192 4) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32192 (hi : ineligSet 17 D⊆mask 32192) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c32128 live corr hw ne
    intro v hv
    have vv : v∈mask 32192 := hi hv
    have reduced : ∀ a:V, a∈mask 32192 → a≠6 → a∈mask 32128 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c32064 live corr hw ne
    intro v hv
    have vv : v∈mask 32192 := hi hv
    have reduced : ∀ a:V, a∈mask 32192 → a≠7 → a∈mask 32064 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c31936 live corr hw ne
    intro v hv
    have vv : v∈mask 32192 := hi hv
    have reduced : ∀ a:V, a∈mask 32192 → a≠8 → a∈mask 31936 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 197) (ok192 5) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 448 → a=6 ∨ a=7 ∨ a=8 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32448 (hi : ineligSet 17 D⊆mask 32448) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c31936 live corr hw ne
    intro v hv
    have vv : v∈mask 32448 := hi hv
    have reduced : ∀ a:V, a∈mask 32448 → a≠9 → a∈mask 31936 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c31424 live corr hw ne
    intro v hv
    have vv : v∈mask 32448 := hi hv
    have reduced : ∀ a:V, a∈mask 32448 → a≠10 → a∈mask 31424 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c30400 live corr hw ne
    intro v hv
    have vv : v∈mask 32448 := hi hv
    have reduced : ∀ a:V, a∈mask 32448 → a≠11 → a∈mask 30400 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 198) (ok192 6) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 3584 → a=9 ∨ a=10 ∨ a=11 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32576 (hi : ineligSet 17 D⊆mask 32576) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c32064 live corr hw ne
    intro v hv
    have vv : v∈mask 32576 := hi hv
    have reduced : ∀ a:V, a∈mask 32576 → a≠9 → a∈mask 32064 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c31552 live corr hw ne
    intro v hv
    have vv : v∈mask 32576 := hi hv
    have reduced : ∀ a:V, a∈mask 32576 → a≠10 → a∈mask 31552 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c30528 live corr hw ne
    intro v hv
    have vv : v∈mask 32576 := hi hv
    have reduced : ∀ a:V, a∈mask 32576 → a≠11 → a∈mask 30528 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 199) (ok192 7) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 3584 → a=9 ∨ a=10 ∨ a=11 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32640 (hi : ineligSet 17 D⊆mask 32640) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c32128 live corr hw ne
    intro v hv
    have vv : v∈mask 32640 := hi hv
    have reduced : ∀ a:V, a∈mask 32640 → a≠9 → a∈mask 32128 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c31616 live corr hw ne
    intro v hv
    have vv : v∈mask 32640 := hi hv
    have reduced : ∀ a:V, a∈mask 32640 → a≠10 → a∈mask 31616 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c30592 live corr hw ne
    intro v hv
    have vv : v∈mask 32640 := hi hv
    have reduced : ∀ a:V, a∈mask 32640 → a≠11 → a∈mask 30592 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  refine applyRow live corr true hw 3 (row 200) (ok200 0) ?_ hi
  intro v hv
  have list : ∀ a:V, a∈mask 3584 → a=9 ∨ a=10 ∨ a=11 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl <;> assumption
set_option maxRecDepth 24000 in
include live corr hw ne in
private theorem c32704 (hi : ineligSet 17 D⊆mask 32704) : 33+Bzero 17 D≤D.length+3 := by
  by_cases h6 : (6:V)∈ineligSet 17 D
  swap
  · apply c32640 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠6 → a∈mask 32640 := by decide +kernel
    exact reduced v vv (fun e => h6 (e ▸ hv))
  by_cases h7 : (7:V)∈ineligSet 17 D
  swap
  · apply c32576 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠7 → a∈mask 32576 := by decide +kernel
    exact reduced v vv (fun e => h7 (e ▸ hv))
  by_cases h8 : (8:V)∈ineligSet 17 D
  swap
  · apply c32448 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠8 → a∈mask 32448 := by decide +kernel
    exact reduced v vv (fun e => h8 (e ▸ hv))
  by_cases h9 : (9:V)∈ineligSet 17 D
  swap
  · apply c32192 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠9 → a∈mask 32192 := by decide +kernel
    exact reduced v vv (fun e => h9 (e ▸ hv))
  by_cases h10 : (10:V)∈ineligSet 17 D
  swap
  · apply c31680 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠10 → a∈mask 31680 := by decide +kernel
    exact reduced v vv (fun e => h10 (e ▸ hv))
  by_cases h11 : (11:V)∈ineligSet 17 D
  swap
  · apply c30656 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠11 → a∈mask 30656 := by decide +kernel
    exact reduced v vv (fun e => h11 (e ▸ hv))
  by_cases h12 : (12:V)∈ineligSet 17 D
  swap
  · apply c28608 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠12 → a∈mask 28608 := by decide +kernel
    exact reduced v vv (fun e => h12 (e ▸ hv))
  by_cases h13 : (13:V)∈ineligSet 17 D
  swap
  · apply c24512 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠13 → a∈mask 24512 := by decide +kernel
    exact reduced v vv (fun e => h13 (e ▸ hv))
  by_cases h14 : (14:V)∈ineligSet 17 D
  swap
  · apply c16320 live corr hw ne
    intro v hv
    have vv : v∈mask 32704 := hi hv
    have reduced : ∀ a:V, a∈mask 32704 → a≠14 → a∈mask 16320 := by decide +kernel
    exact reduced v vv (fun e => h14 (e ▸ hv))
  exfalso
  apply ne
  apply Finset.Subset.antisymm hi
  intro v hv
  have list : ∀ a:V, a∈mask 32704 → a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by decide +kernel
  rcases list v hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption
def roots : Array Nat := #[32704,32257,29122,28675,4036,3589,454,7,28040,27657,24970,24587,3468,3085,398,15,23376,23057,20818,20499,2900,2581,342,23,18712,18457,16666,16411,2332,2077,286,31,14048,13857,12514,12323,1764,1573,230,39,9384,9257,8362,8235,1196,1069,174,47,4720,4657,4210,4147,628,565,118,55,56,57,58,59,60,61,62,63]
def root (S : Finset L) := (roots[key S]?).getD 0
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem cover : ∀ S : Finset L, (panel S).filter (fun v => v.val<15) ⊆ mask (root S) := by decide +kernel
include live corr hw ne in
set_option maxRecDepth 24000 in
set_option maxHeartbeats 6000000 in
theorem all (ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j) (hubs : ∀i∈ineligSet 17 D,i.val<15) : 33+Bzero 17 D≤D.length+3 := by
  let S := leftSet D
  have inc := in_panel D ind
  have con := cover S
  have hi : ineligSet 17 D⊆mask (root S) := fun i h => con (Finset.mem_filter.mpr ⟨inc h,hubs i h⟩)
  have cc0 : ∀ S : Finset L, root S ∈ ([7,15,23,31,39,47,55,56,57,58,59,60,61,62,63,118,174,230,286,342,398,454,565,628,1069,1196,1573,1764,2077,2332,2581,2900,3085,3468,3589,4036,4147,4210,4657,4720,8235,8362,9257,9384,12323,12514,13857,14048,16411,16666,18457,18712,20499,20818,23057,23376,24587,24970,27657,28040,28675,29122,32257,32704] : List Nat) := by decide +kernel
  have cc := cc0 S
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cc
  rcases cc with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  · exact c7 live corr hw ne (e ▸ hi)
  · exact c15 live corr hw ne (e ▸ hi)
  · exact c23 live corr hw ne (e ▸ hi)
  · exact c31 live corr hw ne (e ▸ hi)
  · exact c39 live corr hw ne (e ▸ hi)
  · exact c47 live corr hw ne (e ▸ hi)
  · exact c55 live corr hw ne (e ▸ hi)
  · exact c56 live corr hw ne (e ▸ hi)
  · exact c57 live corr hw ne (e ▸ hi)
  · exact c58 live corr hw ne (e ▸ hi)
  · exact c59 live corr hw ne (e ▸ hi)
  · exact c60 live corr hw ne (e ▸ hi)
  · exact c61 live corr hw ne (e ▸ hi)
  · exact c62 live corr hw ne (e ▸ hi)
  · exact c63 live corr hw ne (e ▸ hi)
  · exact c118 live corr hw ne (e ▸ hi)
  · exact c174 live corr hw ne (e ▸ hi)
  · exact c230 live corr hw ne (e ▸ hi)
  · exact c286 live corr hw ne (e ▸ hi)
  · exact c342 live corr hw ne (e ▸ hi)
  · exact c398 live corr hw ne (e ▸ hi)
  · exact c454 live corr hw ne (e ▸ hi)
  · exact c565 live corr hw ne (e ▸ hi)
  · exact c628 live corr hw ne (e ▸ hi)
  · exact c1069 live corr hw ne (e ▸ hi)
  · exact c1196 live corr hw ne (e ▸ hi)
  · exact c1573 live corr hw ne (e ▸ hi)
  · exact c1764 live corr hw ne (e ▸ hi)
  · exact c2077 live corr hw ne (e ▸ hi)
  · exact c2332 live corr hw ne (e ▸ hi)
  · exact c2581 live corr hw ne (e ▸ hi)
  · exact c2900 live corr hw ne (e ▸ hi)
  · exact c3085 live corr hw ne (e ▸ hi)
  · exact c3468 live corr hw ne (e ▸ hi)
  · exact c3589 live corr hw ne (e ▸ hi)
  · exact c4036 live corr hw ne (e ▸ hi)
  · exact c4147 live corr hw ne (e ▸ hi)
  · exact c4210 live corr hw ne (e ▸ hi)
  · exact c4657 live corr hw ne (e ▸ hi)
  · exact c4720 live corr hw ne (e ▸ hi)
  · exact c8235 live corr hw ne (e ▸ hi)
  · exact c8362 live corr hw ne (e ▸ hi)
  · exact c9257 live corr hw ne (e ▸ hi)
  · exact c9384 live corr hw ne (e ▸ hi)
  · exact c12323 live corr hw ne (e ▸ hi)
  · exact c12514 live corr hw ne (e ▸ hi)
  · exact c13857 live corr hw ne (e ▸ hi)
  · exact c14048 live corr hw ne (e ▸ hi)
  · exact c16411 live corr hw ne (e ▸ hi)
  · exact c16666 live corr hw ne (e ▸ hi)
  · exact c18457 live corr hw ne (e ▸ hi)
  · exact c18712 live corr hw ne (e ▸ hi)
  · exact c20499 live corr hw ne (e ▸ hi)
  · exact c20818 live corr hw ne (e ▸ hi)
  · exact c23057 live corr hw ne (e ▸ hi)
  · exact c23376 live corr hw ne (e ▸ hi)
  · exact c24587 live corr hw ne (e ▸ hi)
  · exact c24970 live corr hw ne (e ▸ hi)
  · exact c27657 live corr hw ne (e ▸ hi)
  · exact c28040 live corr hw ne (e ▸ hi)
  · exact c28675 live corr hw ne (e ▸ hi)
  · exact c29122 live corr hw ne (e ▸ hi)
  · exact c32257 live corr hw ne (e ▸ hi)
  · exact c32704 live corr hw ne (e ▸ hi)
end Marked
abbrev Port := Fin 17
abbrev Support := Finset Port
def W (j : Nat) := 17+j

/-- A backwards cut through a physical DAG replaces a wire by at most one wire plus
    its local charge. Each gate index is processed only once. -/
lemma frontier (m : Nat) (S : Nat → Support) (cold charged : Nat → Prop)
    [DecidablePred charged]
    (raw : ∀ w<17, cold w → (S w).card≤1)
    (step : ∀ j < m, cold (W j) → ∃ K : Finset Nat,
      (∀ i∈K, i<W j ∧ cold i) ∧ S (W j) ⊆ K.biUnion S ∧ K.card≤1+(if charged j then 1 else 0)) :
    ∀ q ≤ m, ∀ F : Finset Nat, (∀ i∈F, i<W q ∧ cold i) →
      (F.biUnion S).card≤ F.card + ((Finset.range q).filter charged).card := by
  classical
  intro q
  induction q with
  | zero =>
    intro _ F good
    apply Finset.card_biUnion_le.trans
    have bound := Finset.sum_le_sum (fun w (h : w∈F) => raw w (good w h).1 (good w h).2)
    simpa using bound
  | succ q ih =>
    intro lim F good
    have lt := Nat.lt_of_succ_le lim
    have lim' := Nat.le_of_lt lt
    have cf : ((Finset.range (q+1)).filter charged).card =
        ((Finset.range q).filter charged).card + (if charged q then 1 else 0) := by
      have re : Finset.range (q+1)=insert q (Finset.range q) := by ext n; simp; omega
      rw [re,Finset.filter_insert]
      split_ifs with h <;> simp [h]
    rw [cf]
    by_cases h : W q∈F
    · obtain ⟨K,prior,sub,kc⟩ := step q lt (good _ h).2
      let P := F.erase (W q) ∪ K
      have hp : ∀ i∈P, i<W q ∧ cold i := by
        intro i hi
        rcases Finset.mem_union.mp hi with he|hk
        · obtain ⟨ne,mem⟩ := Finset.mem_erase.mp he
          have g := good i mem
          exact ⟨by dsimp [W] at g ne ⊢; omega,g.2⟩
        · exact prior i hk
      have hs : F.biUnion S ⊆ P.biUnion S := by
        intro u hu
        obtain ⟨i,hi,ui⟩ := Finset.mem_biUnion.mp hu
        by_cases e : i=W q
        · subst i
          obtain ⟨k,hk,uk⟩ := Finset.mem_biUnion.mp (sub ui)
          exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_union_right _ hk,uk⟩
        · exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨e,hi⟩),ui⟩
      have e := Finset.card_erase_add_one h
      have upper : P.card≤(F.erase (W q)).card+K.card := Finset.card_union_le _ _
      have bd := (Finset.card_le_card hs).trans (ih lim' P hp)
      omega
    · have bd := ih lim' F (fun i hi => ⟨by
          have ne : i≠W q := fun e => h (e ▸ hi)
          have g := (good i hi).1
          dsimp [W] at g ne ⊢
          omega,(good i hi).2⟩)
      omega



def land : Finset V := Finset.univ.filter (fun v => v.val<6)
def sea : Finset V := Finset.univ.filter (fun v => 6≤v.val)
def ambient (v : V) := decide (v.val<6)
def hot (i : V) (v : V) := decide (v.val<6 ∨ v=i)
def cold (D : Dag) (w : Nat) := val D ambient w=false
def SS (D : Dag) (w : Nat) := sea.filter (fun i => val D (hot i) w=true)
instance (D : Dag) (w : Nat) : Decidable (cold D w) := by unfold cold; infer_instance
def outer (D : Dag) : Finset Nat :=
  (Finset.range D.length).filter (fun j => tag D j=false ∧ cold D (17+j))
private theorem ambientOff : ¬sem_Edge G ambient := by
  unfold sem_Edge
  decide +kernel
private theorem hotOn : ∀u∈sea,sem_Edge G (hot u) := by
  unfold sem_Edge
  decide +kernel
theorem outerTen {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D) : 10≤(outer D).card := by
  classical
  let S := SS D
  let ch (j : Nat) := tag D j=false ∧ cold D (W j)
  have raw (w : Nat) (hw : w<17) (off : cold D w) : (S w).card≤1 := by
    have p := (val_input D ambient w hw).symm.trans off
    have h6 : ¬w<6 := of_decide_eq_false p
    calc
      (S w).card ≤ ({⟨w,hw⟩} : Finset V).card := Finset.card_le_card (by
        intro i hi
        have q := (val_input D (hot i) w hw).symm.trans (Finset.mem_filter.mp hi).2
        exact Finset.mem_singleton.mpr ((of_decide_eq_true q).resolve_left h6).symm)
      _ ≤ 1 := by simp
  have steps (j : Nat) (hj : j<D.length) (off : cold D (W j)) :
      ∃ K : Finset Nat,(∀ i∈K,i<W j ∧ cold D i) ∧ S (W j)⊆K.biUnion S ∧ K.card≤1+(if ch j then 1 else 0) := by
    let a := opA D j
    let b := opB D j
    have ⟨la,lb,_⟩ := live.1 j hj
    have eq (x : V → Bool) : val D x (W j)=gop (tag D j) (val D x a) (val D x b) := val_gate live.1 x j hj
    by_cases tagj : tag D j=true
    ·
      have ca : cold D a ∨ cold D b := by
        change val D ambient a=false ∨ val D ambient b=false
        change val D ambient (W j)=false at off
        rw [eq,tagj,gop_true] at off
        cases h : val D ambient a <;> simp_all
      rcases ca with ca|cb
      · refine ⟨{a},by simpa [a,W] using And.intro la ca,?_,by simp⟩
        simp only [Finset.singleton_biUnion]
        intro i hi
        have ⟨ms,on⟩ := Finset.mem_filter.mp hi
        rw [eq,tagj,gop_true,Bool.and_eq_true] at on
        exact Finset.mem_filter.mpr ⟨ms,on.1⟩
      · refine ⟨{b},by simpa [b,W] using And.intro lb cb,?_,by simp⟩
        simp only [Finset.singleton_biUnion]
        intro i hi
        have ⟨ms,on⟩ := Finset.mem_filter.mp hi
        rw [eq,tagj,gop_true,Bool.and_eq_true] at on
        exact Finset.mem_filter.mpr ⟨ms,on.2⟩
    · have tagj : tag D j=false := Bool.eq_false_iff.mpr tagj
      have hv : val D ambient (W j)=false := off
      rw [eq,tagj,gop_false,Bool.or_eq_false_iff] at hv
      refine ⟨{a,b},?_,?_,?_⟩
      · intro v hv'
        rcases Finset.mem_insert.mp hv' with e|e
        · subst v; exact ⟨la,hv.1⟩
        · obtain rfl := Finset.mem_singleton.mp e; exact ⟨lb,hv.2⟩
      · intro i hi
        have ⟨ms,on⟩ := Finset.mem_filter.mp hi
        rw [eq,tagj,gop_false,Bool.or_eq_true] at on
        rcases on with z|z
        · exact Finset.mem_biUnion.mpr ⟨a,by simp, Finset.mem_filter.mpr ⟨ms,z⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨b,by simp, Finset.mem_filter.mpr ⟨ms,z⟩⟩
      · have c : ch j := ⟨tagj,off⟩
        simpa [c] using Finset.card_insert_le a ({b} : Finset Nat)
  have n : ¬sem_Edge G ambient := ambientOff
  have out0 : cold D (outW 17 D) := Bool.eq_false_iff.mpr fun z => n ((corr _).mp z)
  have all : S (outW 17 D)=sea := by
    ext i
    refine Finset.mem_filter.trans ⟨And.left,fun hi => ⟨hi,(corr _).mpr ?_⟩⟩
    exact hotOn i hi
  have p := frontier D.length S (cold D) ch raw steps D.length le_rfl {outW 17 D} (by
    simp only [Finset.mem_singleton,forall_eq]
    exact ⟨by dsimp [outW,W]; omega,out0⟩)
  have sz : sea.card=11 := by decide
  have t : 11≤1+((Finset.range D.length).filter ch).card := by simpa [all,sz] using p
  change 10≤((Finset.range D.length).filter ch).card
  omega

def leftSupp (D : Dag) (w : Nat) := supp 17 D w ∩ land
def neighbors (v : V) := land.filter (fun i => G v i)
theorem rightGeometry : (∀ i∈sea,2≤(neighbors i).card) ∧
    (∀ i∈sea,∀ j∈sea,neighbors i=neighbors j → i=j) ∧
    (∀ a∈land,∀ b∈land,¬G a b) := by decide +kernel

theorem priced {D : Dag} (R : Finset V) (hr : R⊆sea) (live : StrictLive 17 D)
    (corr : sem_Comp 17 G D) (hi : R⊆ineligSet 17 D) (bz : Bzero 17 D=0) :
    ∃ A B : Finset Nat, A.card=R.card ∧ B.card=R.card ∧
      (∀j∈A,j<D.length ∧ tag D j=true ∧ supp 17 D (17+j)=∅ ∧
        (∃i∈R,∃s, supp 17 D (src D (j,s))={i})) ∧
      (∀j∈B,j<D.length ∧ ∃i∈R,leftSupp D (17+j)=neighbors i) ∧
      (∀i∈R,∃j,leftSupp D (17+j)=neighbors i) := by
  classical
  have asn (i : V) (h : i∈R) := sem_inelig_consumer regular live corr (hi h)
  choose! gate ag using asn
  have exactNb (i : V) (h : i∈R) := sem_exact_nbhd regular live.1 corr land rightGeometry.2.2
    (sem_noempty_chain_out regular live corr bz (hi h))
  choose! gg side bh using exactNb
  let w (i : V) := src D (gg i,side i)
  have we (i : V) (h : i∈R) : leftSupp D (w i)=neighbors i := by
    ext a
    by_cases ha : a∈land
    · simpa [leftSupp,neighbors,ha,w] using (bh i h).2.2.2 a ha
    · simp [leftSupp,neighbors,ha]
  have big (i : V) (h : i∈R) : 17≤w i := by
    by_contra! small
    have rw0 : supp 17 D (w i) = {⟨w i,small⟩} := supp_input D ⟨_,small⟩
    have sub : leftSupp D (w i) ⊆ {⟨w i,small⟩} := by rw [←rw0]; exact Finset.inter_subset_left
    have c := Finset.card_le_card sub
    rw [we i h,Finset.card_singleton] at c
    have l := rightGeometry.1 _ (hr h)
    omega
  have Wlt (i : V) (h : i∈R) : w i<17+D.length := by
    have z := sem_src_lt live.1 (bh i h).1 (side i)
    have z' := (bh i h).1
    dsimp [w]; omega
  let ja (i : V) := (gate i).1
  let jb (i : V) := w i - 17
  have ia : Set.InjOn ja (R : Set V) := by
    intro i h j k eq
    change (gate i).1=(gate j).1 at eq
    have hh := ag i h
    have kk := ag j k
    have center : (gate i).2=(gate j).2 := by
      by_contra diff
      have flip : (!(gate i).2)=(gate j).2 := by cases e:(gate i).2 <;> cases f:(gate j).2 <;> simp_all
      have tog : ((gate i).1,!(gate i).2)=gate j := Prod.ext eq flip
      have one := kk.2.2.1
      have ss : neighbors i⊆{j} := by
        intro x hx
        have v := hh.2.2.2.2.1 x (Finset.mem_filter.mp hx).2
        rwa [tog,one] at v
      have z := rightGeometry.1 i (hr h)
      have y := Finset.card_le_card ss
      simp only [Finset.card_singleton] at y
      omega
    have same : gate i=gate j := Prod.ext eq center
    have one := hh.2.2.1
    rw [same,kk.2.2.1] at one
    exact (Finset.singleton_injective one).symm
  have ib : Set.InjOn jb (R : Set V) := by
    intro i h j k e
    have ha := big i h
    have hb := big j k
    change w i - 17 = w j - 17 at e
    have ee : w i=w j := by omega
    apply rightGeometry.2.1 i (hr h) j (hr k)
    rw [←we i h,←we j k,ee]
  refine ⟨R.image ja,R.image jb,Finset.card_image_of_injOn ia,Finset.card_image_of_injOn ib,?_,?_,?_⟩
  · intro j hj
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hj
    have hh := ag i h
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,i,h,(gate i).2,by simpa [ja] using hh.2.2.1⟩
  · intro j hj
    obtain ⟨i,h,rfl⟩ := Finset.mem_image.mp hj
    have a := big i h
    have b := Wlt i h
    have eq : 17+jb i=w i := by dsimp [jb]; omega
    exact ⟨by dsimp [jb]; omega,i,h,by rw [eq,we i h]⟩
  · intro i h
    have a := big i h
    refine ⟨jb i,?_⟩
    have eq : 17+jb i=w i := by dsimp [jb]; omega
    rw [eq,we i h]

def cells : Finset V := mask 32704
theorem cs : cells.card=9 ∧ cells⊆sea ∧ land.card=6 ∧ sea.card=11 ∧
  (∀i∈cells,(neighbors i).card=2) := by decide +kernel
def chargedA (D : Dag) (R : Finset V) (j : Nat) := j<D.length ∧ tag D j=true ∧ supp 17 D (17+j)=∅ ∧ ∃ i∈R,∃ t,supp 17 D (src D (j,t))={i}
def chargedB (D : Dag) (R : Finset V) (j : Nat) := j<D.length ∧ ∃i∈R,leftSupp D (17+j)=neighbors i
def coldpool (D : Dag) (R : Finset V) (A B : Finset Nat) := A∪B∪outer D
theorem land_on {D : Dag} (live : StrictLive 17 D) {w : Nat} (h : (leftSupp D w).Nonempty) : ¬cold D w := by
  obtain ⟨v,hi⟩ := h
  obtain ⟨inSupp,inLand⟩ := Finset.mem_inter.mp hi
  exact fun off => Bool.noConfusion ((sem_val_of_supp live.1 inSupp (show ambient v=true from decide_eq_true ((Finset.mem_filter.mp inLand).2))).symm.trans off)
theorem census {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D) (R : Finset V) (hr:R⊆sea)
    {A B : Finset Nat} (ac:A.card=R.card) (bc:B.card=R.card)
    (a : ∀j∈A,chargedA D R j) (b : ∀j∈B,chargedB D R j) :
    coldpool D R A B ⊆ Finset.range D.length ∧ 2*R.card+10 ≤ (coldpool D R A B).card := by
  have nb (i : V) (hi : i∈R) := rightGeometry.1 i (hr hi)
  have active {j} (hj : j∈B) : (leftSupp D (17+j)).Nonempty := by
    obtain ⟨_,i,hi,e⟩ := b j hj
    rw [e]
    exact Finset.card_pos.mp (by have := nb i hi; omega)
  have dis : Disjoint A B := Finset.disjoint_left.mpr (by
    intro j ha hb
    have nope : leftSupp D (17+j)=∅ := by simp [leftSupp,(a j ha).2.2.1]
    simpa [nope] using active hb)
  have dis2 : Disjoint (A∪B) (outer D) := Finset.disjoint_left.mpr (by
    intro j hm ho
    have bb := (Finset.mem_filter.mp ho).2
    rcases Finset.mem_union.mp hm with ha|hb
    · exact Bool.noConfusion ((a j ha).2.1.symm.trans bb.1)
    · exact land_on live (active hb) bb.2)
  refine ⟨?_,?_⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with ab|o
    · rcases Finset.mem_union.mp ab with ha|hb
      · exact Finset.mem_range.mpr (a j ha).1
      · exact Finset.mem_range.mpr (b j hb).1
    · exact (Finset.mem_filter.mp o).1
  · have outerP := outerTen live corr
    rw [coldpool,Finset.card_union_of_disjoint dis2,Finset.card_union_of_disjoint dis,ac,bc]
    omega
theorem endScalar {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
    (hc : sea⊆ineligSet 17 D) (zero : Bzero 17 D=0) : 32≤D.length := by
  obtain ⟨A,B,ac,bc,a,b,_⟩ := priced sea (Finset.Subset.refl _) live corr hc zero
  obtain ⟨sub,num⟩ := census live corr sea (Finset.Subset.refl _) ac bc a b
  have lim := Finset.card_le_card sub
  rw [Finset.card_range] at lim
  rw [cs.2.2.2.1] at num
  omega

theorem narrowBirth {D : Dag} (live : StrictLive 17 D) (small : ∀w,(leftSupp D w).card≤2)
    (R : Finset V) (hR:R⊆cells) (existing : ∀i∈R,∃j,leftSupp D (17+j)=neighbors i) :
    ∃B : Finset Nat, B.card=R.card ∧ ∀j∈B, chargedB D R j ∧ tag D j=false := by
  classical
  let first (i : V) (h : i∈R) := Nat.find (existing i h)
  have birth (i : V) (hi : i∈R) : ∃j, j<D.length ∧ leftSupp D (17+j)=neighbors i ∧ tag D j=false := by
    let j := first i hi
    have eq : leftSupp D (17+j)=neighbors i := Nat.find_spec (existing i hi)
    have num := cs.2.2.2.2 i (hR hi)
    have pos : (leftSupp D (17+j)).Nonempty := Finset.card_pos.mp (by rw [eq,num]; decide)
    obtain ⟨v,hv⟩ := pos
    have lim := sem_supp_lt (Finset.mem_inter.mp hv).1
    have hj : j<D.length := by omega
    refine ⟨j,hj,eq,?_⟩
    cases h : tag D j with
    | false => rfl
    | true =>
      exfalso
      let u := opA D j
      have sub : leftSupp D (17+j) ⊆ leftSupp D u := by
        intro v hv
        obtain ⟨hs,hl⟩ := Finset.mem_inter.mp hv
        rw [sem_supp_and live.1 hj h] at hs
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hs).1,hl⟩
      have same : leftSupp D (17+j)=leftSupp D u := Finset.eq_of_subset_of_card_le sub (by rw [eq,num]; exact small _)
      have big : 17≤u := by
        by_contra! hraw
        have one : supp 17 D u={⟨u,hraw⟩} := supp_input D ⟨u,hraw⟩
        have bd : leftSupp D u⊆{⟨u,hraw⟩} := by rw [←one]; exact Finset.inter_subset_left
        have k := Finset.card_le_card bd
        rw [←same,eq,num,Finset.card_singleton] at k
        omega
      have uj : u<17+j := (live.1 j hj).1
      have uu : 17+(u-17)=u := by omega
      have earlier : leftSupp D (17+(u-17))=neighbors i := by rw [uu,←same,eq]
      have e : j≤u-17 := Nat.find_min' (existing i hi) earlier
      omega
  choose! j spec using birth
  have inj : Set.InjOn j (R : Set V) := by
    intro i h k hk e
    exact rightGeometry.2.1 i (cs.2.1 (hR h)) k (cs.2.1 (hR hk)) (by rw [←(spec i h).2.1,←(spec k hk).2.1,e])
  refine ⟨R.image j,Finset.card_image_of_injOn inj,?_⟩
  intro t ht
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
  exact ⟨⟨(spec i hi).1,i,hi,(spec i hi).2.1⟩,(spec i hi).2.2⟩

def hub (u : V) : V := if u.val<3 then 15 else 16
theorem endMarked {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
    (cellEq : ineligSet 17 D=cells) (zero : Bzero 17 D=0) : 30≤D.length := by
  classical
  by_contra! len
  have inc : cells⊆ineligSet 17 D := by rw [cellEq]
  obtain ⟨A,B,ac,bc,a,b,roots⟩ := priced cells cs.2.1 live corr inc zero
  have eligible (i : V) (ni : i∉cells) : i∈eligSet 17 D := by
    by_contra no
    exact ni (cellEq ▸ (sem_mem_inelig.mpr no))
  obtain ⟨f,hf,tf,ef,_,_,_,pure⟩ := sem_free_empty regular live corr (by decide : G 0 15)
    (eligible 0 (by decide)) (eligible 15 (by decide))
  have fa : f∉A := by
    intro af
    obtain ⟨_,_,_,i,hi,v,sp⟩ := a f af
    have cl := pure i (inc hi)
    have mem : i∈supp 17 D (src D (f,v)) := by rw [sp]; simp
    cases v <;> simp [src] at mem <;> tauto
  have pack (B' : Finset Nat) (cb : B'.card=cells.card) (g : ∀j∈B',chargedB D cells j) :
      insert f (coldpool D cells A B') = Finset.range D.length := by
    obtain ⟨sub,num⟩ := census live corr cells cs.2.1 ac cb a g
    have fb : f∉B' := by
      intro bf
      obtain ⟨_,i,hi,eq⟩ := g f bf
      have n := cs.2.2.2.2 i hi
      rw [←eq] at n
      simp [leftSupp,ef] at n
    have fo : f∉outer D := fun z => Bool.noConfusion (tf.symm.trans (Finset.mem_filter.mp z).2.1)
    have ff : f∉coldpool D cells A B' := by simp [coldpool,fa,fb,fo]
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset (Finset.mem_range.mpr hf) sub)
    rw [Finset.card_insert_of_notMem ff,Finset.card_range]
    rw [cs.1] at num
    omega
  have all := pack B bc b
  have small (w : Nat) : (leftSupp D w).card≤2 := by
    by_cases raw : w<17
    · have eq : supp 17 D w={⟨w,raw⟩} := supp_input D ⟨w,raw⟩
      have sub : leftSupp D w⊆{⟨w,raw⟩} := by rw [←eq]; exact Finset.inter_subset_left
      have le := Finset.card_le_card sub
      simp only [Finset.card_singleton] at le; omega
    by_contra! big
    obtain ⟨v,mem⟩ := Finset.card_pos.mp (by omega : 0<(leftSupp D w).card)
    have ub := sem_supp_lt (Finset.mem_inter.mp mem).1
    let j := w-17
    have eq : 17+j=w := by dsimp [j]; omega
    have inj : j∈insert f (coldpool D cells A B) := by rw [all]; apply Finset.mem_range.mpr; dsimp [j]; omega
    rw [←eq] at big mem
    rcases Finset.mem_insert.mp inj with rfl|m
    · simp [leftSupp,ef] at big
    · rcases Finset.mem_union.mp m with ab|out
      · rcases Finset.mem_union.mp ab with aa|bb
        · simp [leftSupp,(a j aa).2.2.1] at big
        · obtain ⟨_,i,hi,el⟩ := b j bb
          rw [el,cs.2.2.2.2 i hi] at big
          omega
      · exact land_on live ⟨v,mem⟩ (Finset.mem_filter.mp out).2.2
  obtain ⟨B',cardB',orB⟩ := narrowBirth live small cells (Finset.Subset.refl _) roots
  have all' := pack B' cardB' (fun j h => (orB j h).1)
  have hit (p : V) (hp : p∈land) : p∈leftSupp D (opA D f) ∪ leftSupp D (opB D f) := by
    have g := (by decide +kernel : ∀ p∈land,G p (hub p)) p hp
    obtain ⟨j,hj,op,_,_,_,v,pOn,_,hOn,_⟩ := sem_joint_meeting regular live.1 corr g
    have jmem : j∈insert f (coldpool D cells A B') := by rw [all']; exact Finset.mem_range.mpr hj
    have jf : j=f := by
      rcases Finset.mem_insert.mp jmem with eq|mm
      · exact eq
      rcases Finset.mem_union.mp mm with ab|out
      · rcases Finset.mem_union.mp ab with aa|bb
        · obtain ⟨_,_,_,i,hi,t,pureI⟩ := a j aa
          have noP := (by decide +kernel : ∀ p∈land,∀ i∈cells,p≠i ∧ hub p≠i) p hp i hi
          cases t <;> cases v <;> simp [src] at pureI pOn hOn <;>
            first | (rw [pureI,Finset.mem_singleton] at pOn; contradiction) |
                    (rw [pureI,Finset.mem_singleton] at hOn; contradiction) | grind
        · exact False.elim (Bool.noConfusion (op.symm.trans (orB j bb).2))
      · exact False.elim (Bool.noConfusion (op.symm.trans (Finset.mem_filter.mp out).2.1))
    subst j
    cases v with
    | false => exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨pOn,hp⟩)
    | true => exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨pOn,hp⟩)
  have six := Finset.card_le_card hit
  have mx := Finset.card_union_le (leftSupp D (opA D f)) (leftSupp D (opB D f))
  have a1 := small (opA D f)
  have a2 := small (opB D f)
  rw [cs.2.2.1] at six
  omega
theorem scalarFloor {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D) : 29≤D.length := by
  classical
  have ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover regular live corr ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  by_cases h : ineligSet 17 D = mask 131008
  · have h28 := strict28 live corr ind
    by_contra! h29
    have bz : Bzero 17 D=0 := by omega
    have eq : mask 131008=sea := by decide +kernel
    have l := endScalar live corr (by rw [h,eq]) bz
    omega
  · have v := Scalar.all live corr (by simp) h ind
    omega

theorem markedFloor {D : Dag} (live : StrictLive 17 D) (corr : sem_Comp 17 G D)
    (w : Nat) (h15 : (15:V)∈supp 17 D w) (h16 : (16:V)∈supp 17 D w) : 30≤D.length := by
  classical
  have ind : ∀i∈ineligSet 17 D,∀j∈ineligSet 17 D,¬G i j := by
    intro i hi j hj ed
    exact (sem_elig_cover regular live corr ed).elim (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).2
  have hubs : ∀i∈ineligSet 17 D,i.val<15 := by
    intro i hi
    by_contra! big
    have e : i=15 ∨ i=16 := by omega
    rcases e with rfl|rfl
    · have p := sem_inelig_pure regular live.1 corr hi h15
      rw [p] at h16; exact (by decide : (16:V)∉({15} : Finset V)) h16
    · have p := sem_inelig_pure regular live.1 corr hi h16
      rw [p] at h15; exact (by decide : (15:V)∉({16} : Finset V)) h15
  have diff : ineligSet 17 D≠mask 131008 := by
    intro e
    have v := hubs 16 (e ▸ (by decide : (16:V)∈mask 131008))
    omega
  have n29 := Scalar.all live corr (by simp) diff ind
  by_cases e : ineligSet 17 D=mask 32704
  · by_contra! len
    have bz : Bzero 17 D=0 := by omega
    have m := endMarked live corr e bz
    omega
  · have q := Marked.all live corr (fun _ => ⟨w,h15,h16⟩) e ind hubs
    omega
theorem physical {C : Circuit} (hm : Monotone2 C) (sz : C.size≤29)
    (correct : ∀x : V → Bool,C.eval (List.ofFn x)=true ↔ sem_Edge G x)
    (k : Nat) (on : ∀i∈([15,16]:List V),(C.wires (List.ofFn (single i))).getD k false=true)
    (off : (C.wires (List.ofFn (fun _ : V => false))).getD k false=false) : False := by
  classical
  have hG := regular
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
  obtain ⟨D,ld,lim,simulation,w,sm⟩ := preserve_marks (n:=17) C hm
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
    (by
      intro D live sim
      have corr : sem_Comp 17 G D := fun x => by rw [sim]; exact correct x
      have floor := scalarFloor live corr
      omega) k (by
      intro b
      cases b with
      | false => exact ⟨DagProof.single (15 : V),by rw [on 15 (by simp)]; decide⟩
      | true => exact ⟨fun _ => false,by rw [off]; decide⟩)
  have corr : sem_Comp 17 G D := fun x => by rw [simulation]; exact correct x
  have ok (i : V) (hi : i∈([15,16]:List V)) : i∈supp 17 D w :=
    mem_supp.mpr ((sm _).trans (on i hi))
  have m := markedFloor ld corr w (ok 15 (by simp)) (ok 16 (by simp))
  omega
end Main
namespace Mono
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma append_mono (x y : List Bool) (a b : Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i, (x ++ [a]).getD i false = true → (y ++ [b]).getD i false = true := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega)]
    exact h i
  · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hl]
    cases he : i - y.length <;> simp_all

lemma gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (h : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro hx i hi
    exact h i (hx i hi)
  · simp only [hg, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, hx⟩
    exact ⟨i, hi, h i hx⟩

lemma run_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, (run gs (x ++ [_])).getD i false = true →
      (run gs (y ++ [_])).getD i false = true
    apply ih (fun q hq => hm q (List.mem_cons_of_mem g hq)) _ _ (by simp [hl])
    exact append_mono x y _ _ hl h (gate_mono g (hm g (by simp)) _ _ h)

lemma eval_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply run_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, hi]

lemma impossible {n : ℕ} (f : (Fin n → Bool) → Bool) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) (hx : f x = true) (hy : f y = false) :
    ¬ ∃ C : Circuit, Monotone2 C ∧ ∀ z : Fin n → Bool, C.eval (List.ofFn z) = f z := by
  rintro ⟨C, hm, hf⟩
  have h := eval_mono C hm x y hxy
  rw [hf, hf, hx, hy] at h
  exact Bool.false_ne_true (h rfl)

lemma wires_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C) (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) :
    ∀ i, (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  apply run_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp)
  intro i
  by_cases hi : i < n
  · simpa [List.getD_eq_getElem?_getD, hi] using h ⟨i, hi⟩
  · simp [List.getD_eq_getElem?_getD, hi]


lemma wire_monotone (C : Circuit) (n w : ℕ) (hC : PEqualNP.TopForm.IsAO2 n C) :
    Monotone (fun x : Fin n → Bool => PEqualNP.BlindGate.wireValue C n x w) := by
  have hm : Monotone2 C := fun g hg => ⟨hC.1 g hg, (hC.2.2 g hg).le⟩
  intro x y hxy
  have hi : ∀ i,x i = true → y i = true := by
    intro i he
    exact Bool.le_iff_imp.mp (hxy i) he
  have he := wires_mono C hm x y hi w
  change (C.wires (List.ofFn x)).getD w false ≤ (C.wires (List.ofFn y)).getD w false
  exact Bool.le_iff_imp.mpr he

lemma eval_list_monotone (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (h : List.Forall₂ (· ≤ ·) x y) : C.eval x ≤ C.eval y := by
  have hi : ∀ i,x.getD i false ≤ y.getD i false := by
    induction h with
    | nil => intro i; simp
    | @cons a b xs ys hab h ih =>
      intro i
      cases i with
      | zero => simpa using hab
      | succ i => simpa using ih i
  have he := run_mono C.gates (fun g hg => (hm g hg).1) x y h.length_eq
    (fun i hh => Bool.le_iff_imp.mp (hi i) hh) C.output
  change (run C.gates x).getD C.output false ≤ (run C.gates y).getD C.output false
  exact Bool.le_iff_imp.mpr he


lemma wires_list_monotone (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (h : List.Forall₂ (· ≤ ·) x y) :
    ∀ i : ℕ, (C.wires x).getD i false ≤ (C.wires y).getD i false := by
  have hi : ∀ i,x.getD i false ≤ y.getD i false := by
    induction h with
    | nil => intro i; simp
    | @cons a b xs ys hab h ih =>
      intro i
      cases i with
      | zero => simpa using hab
      | succ i => simpa using ih i
  intro i
  exact Bool.le_iff_imp.mpr (run_mono C.gates (fun g hg => (hm g hg).1) x y h.length_eq
    (fun k hh => Bool.le_iff_imp.mp (hi k) hh) i)

lemma zip_implies (a b : List Bool) (hl : a.length=b.length)
    (h : (a.zipWith (fun x y => !x || y) b).all id = true) :
    List.Forall₂ (· ≤ ·) a b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => simp_all
    | cons b bs =>
      simp only [List.zipWith_cons_cons,List.all_cons,id_eq,Bool.and_eq_true] at h
      apply List.Forall₂.cons
      · cases a <;> cases b <;> simp_all
      · exact ih bs (by simpa using hl) h.2

lemma downward (C : Circuit) (hm : Monotone2 C) (a b : List Bool)
    (ha : a.length=21) (hb : b.length=21)
    (h : (a.zipWith (fun x y => !x || y) b).all id = true)
    (he : C.eval b=false) : C.eval a=false := by
  have m := eval_list_monotone C hm a b (zip_implies a b (ha.trans hb.symm) h)
  rw [he] at m
  exact le_antisymm m (Bool.false_le _)
end Mono


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 9000000 in
theorem fullSpec
    (tests : let E := fun (p l : Fin 17) => ([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0 |>.testBit l.val
     ∃ (C : Circuit) (w : ℕ), Monotone2 C ∧ C.size ≤ 29 ∧ C.output < 17+C.size ∧ w < 17+C.size ∧
       (∀ p l, E p l = true → C.eval (List.ofFn fun i : Fin 17 => decide (i = p ∨ i = l)) = true) ∧
       (∀ j ∈ ([15,16] : List (Fin 17)), (C.wires (List.ofFn fun i => decide (i = j))).getD w false = true) ∧
       ∀ (b : Bool) (P : Finset (Fin 17)), (∀ i ∈ P, i.val < 6) →
         let L := fun j : Fin 17 => (b = false ∨ j.val < 15) ∧ ∀ i ∈ P, E i j = false
         ∀ u : Fin 17 → Bool,
           (∀ i, u i = true ↔ if i.val < 6 then ∀ j, E i j = true → ¬ L j else L i) →
             (C.wires (List.ofFn u)).getD (if b then w else C.output) false = false)
    (mono : ∀ (C : Circuit), Monotone2 C → ∀ a b : List Bool, List.Forall₂ (· ≤ ·) a b → ∀ i : ℕ, (C.wires a).getD i false ≤ (C.wires b).getD i false) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (29 : ℕ) ∧       x1.output < (17 : ℕ) + x1.size ∧         x2 < (17 : ℕ) + x1.size ∧           ∀ (x3 : Fin (17 : ℕ) → Bool),             have x4 : Fin (17 : ℕ) → Fin (17 : ℕ) → Prop := fun (x4 x5 : Fin (17 : ℕ)) => ↑x4 < (6 : ℕ) ∧ (↑x5 = (15 : ℕ) + ↑x4 / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑x5 ∧ ↑x5 < (15 : ℕ) ∧ (if ↑x4 < (3 : ℕ) then (↑x5 - (6 : ℕ)) / (3 : ℕ) else (↑x5 - (6 : ℕ)) % (3 : ℕ)) = ↑x4 % (3 : ℕ));             (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (17 : ℕ)) (x6 : Fin (17 : ℕ)), x4 x5 x6 ∧ x3 x5 = Bool.true ∧ x3 x6 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (15 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ))))) := by
  classical
  let E := fun (p l : Fin 17) => ([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0 |>.testBit l.val
  have edge : ∀ p l : Fin 17, E p l = true ↔ ↑p < (6 : ℕ) ∧ (↑l = (15 : ℕ) + ↑p / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑l ∧ ↑l < (15 : ℕ) ∧ (if ↑p < (3 : ℕ) then (↑l - (6 : ℕ)) / (3 : ℕ) else (↑l - (6 : ℕ)) % (3 : ℕ)) = ↑p % (3 : ℕ)) := by decide +kernel
  have sides : ∀ p l, E p l = true → p.val < 6 ∧ 6 ≤ l.val := by decide +kernel
  obtain ⟨C,w,hm,hs,ho,hw,hp,ha,hn⟩ := tests
  refine ⟨C,w,hm,hs,ho,hw,?_⟩
  intro x
  dsimp only
  let W := fun (y : Fin 17 → Bool) (i : ℕ) => (C.wires (List.ofFn y)).getD i false
  have leW (a b : Fin 17 → Bool) (h : a ≤ b) (w' : ℕ) : W a w' ≤ W b w' := by
    apply mono C hm
    apply List.forall₂_iff_get.mpr
    refine ⟨by simp only [List.length_ofFn], ?_⟩
    intro i hi hj
    rw [List.get_ofFn, List.get_ofFn]
    exact h _
  let H := ∃ p l, E p l = true ∧ x p = true ∧ x l = true
  have positive (h : H) : W x C.output = true := by
    obtain ⟨p,l,he,hp',hl⟩ := h
    have hd : (fun i : Fin 17 => decide (i = p ∨ i = l)) ≤ x := by
      intro i
      by_cases hh : i = p ∨ i = l
      · rcases hh with rfl | rfl
        · rw [hp']; exact Bool.le_true _
        · rw [hl]; exact Bool.le_true _
      · simp [hh]
    have z := leW _ _ hd C.output
    have ht : W (fun i : Fin 17 => decide (i = p ∨ i = l)) C.output = true := hp p l he
    rw [ht] at z
    exact le_antisymm (Bool.le_true _) z
  have negative (absent : ¬ H) (b : Bool)
      (special : b = true → x 15 = false ∧ x 16 = false) : W x (if b then w else C.output) = false := by
    let P := Finset.univ.filter fun i : Fin 17 => i.val < 6 ∧ x i = true
    let L := fun j : Fin 17 => (b = false ∨ j.val < 15) ∧ ∀ i ∈ P, E i j = false
    let U := fun i : Fin 17 => if i.val < 6 then @decide (∀ j, E i j = true → ¬ L j) (Classical.propDecidable _) else @decide (L i) (Classical.propDecidable _)
    have allowed : ∀ i ∈ P, i.val < 6 := by intro i hi; exact (Finset.mem_filter.mp hi).2.1
    have up : x ≤ U := by
      intro i
      cases hx : x i with
      | false => exact Bool.false_le _
      | true =>
        by_cases hleft : i.val < 6
        · have hi : i ∈ P := by simp [P,hleft,hx]
          have no : ∀ j, E i j = true → ¬ L j := by
            intro j ej lj
            exact Bool.noConfusion (ej.symm.trans (lj.2 i hi))
          simp only [U, if_pos hleft]
          exact le_of_eq (@decide_eq_true _ (Classical.propDecidable _) no).symm
        · have yes : L i := by
            constructor
            · cases b with
              | false => exact Or.inl rfl
              | true =>
                right
                have hh := special rfl
                by_contra! high
                have : i = 15 ∨ i = 16 := by omega
                rcases this with rfl | rfl
                · exact Bool.noConfusion (hx.symm.trans hh.1)
                · exact Bool.noConfusion (hx.symm.trans hh.2)
            · intro p mem
              have active := (Finset.mem_filter.mp mem).2.2
              cases he : E p i with
              | false => rfl
              | true => exact False.elim (absent ⟨p,i,he,active,hx⟩)
          simp only [U, if_neg hleft]
          exact le_of_eq (@decide_eq_true _ (Classical.propDecidable _) yes).symm
    have z := leW x U up (if b then w else C.output)
    have hzero : W U (if b then w else C.output) = false := by
      apply hn b P allowed U
      intro i
      change U i = true ↔ if i.val < 6 then ∀ j, E i j = true → ¬ L j else L i
      by_cases hi : i.val < 6
      · simp only [U, if_pos hi, decide_eq_true_eq]
      · simp only [U, if_neg hi, decide_eq_true_eq]
    exact le_antisymm (hzero ▸ z) (Bool.false_le _)
  have main : W x C.output = true ↔ H := by
    constructor
    · intro eq; by_contra h
      have off : W x C.output = false := negative h false (by simp)
      exact Bool.noConfusion (eq.symm.trans off)
    · exact positive
  constructor
  · change W x C.output = true ↔ _
    rw [main]
    change (∃ p l, E p l = true ∧ x p = true ∧ x l = true) ↔ _
    simp only [edge, and_assoc]
  · intro low
    change W x C.output = false at low
    have absent : ¬H := fun h => Bool.noConfusion ((positive h).symm.trans low)
    by_cases hit : x 15 = true ∨ x 16 = true
    · obtain ⟨j,hj,hx⟩ : ∃ j ∈ ([15,16] : List (Fin 17)), x j = true := by
        rcases hit with h|h
        · exact ⟨15,by simp,h⟩
        · exact ⟨16,by simp,h⟩
      have dir : (fun i : Fin 17 => decide (i = j)) ≤ x := by
        intro i; by_cases e : i = j
        · subst i; simp [hx]
        · simp [e]
      have good : W (fun i : Fin 17 => decide (i = j)) w = true := ha j hj
      have z := leW _ _ dir w
      rw [good] at z
      have on := le_antisymm (Bool.le_true _) z
      change W x w = _
      rcases hit with h | h <;> simp [on,h]
    · have hh : x 15 = false ∧ x 16 = false := by simpa using hit
      have off := negative absent true (fun _ => hh)
      change W x w = _
      simpa [hh] using off

end PEqualNP.Outside.L_meta_18910

theorem PEqualNP.Outside.L_meta_18910 : ¬ (have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (29 : ℕ) ∧       x2.output < (17 : ℕ) + x2.size ∧         x3 < (17 : ℕ) + x2.size ∧           (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧             (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧               ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),                 (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →                   have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;                   ∀ (x8 : Fin (17 : ℕ) → Bool), (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) → (x2.wires (List.ofFn x8)).getD (if x4 = Bool.true then x3 else x2.output) Bool.false = Bool.false) := by
  intro trial
  obtain ⟨C,k,hm,sz,_,_,spec⟩ := PEqualNP.Outside.L_meta_18910.fullSpec trial PEqualNP.Outside.L_meta_18910.Mono.wires_list_monotone
  refine PEqualNP.Outside.L_meta_18910.Main.physical hm sz ?_ k ?_ ?_
  · intro x
    rw [(spec x).1]
    have rel : ∀p l : Fin 17, PEqualNP.Outside.L_meta_18910.Main.E p l=true ↔
      (p.val<6 ∧ (l.val=15+p.val/3 ∨ 6≤l.val ∧ l.val<15 ∧ (if p.val<3 then (l.val-6)/3 else (l.val-6)%3)=p.val % 3)) := by decide +kernel
    constructor
    · rintro ⟨p,l,e,a,b⟩
      exact ⟨p,l,Or.inl ((rel p l).mpr e),a,b⟩
    · rintro ⟨p,l,e,a,b⟩
      rcases e with f|f
      · exact ⟨p,l,(rel p l).mp f,a,b⟩
      · exact ⟨l,p,(rel l p).mp f,b,a⟩
  · intro i hi
    have rel : ∀ u v : Fin 17, (u.val<6 ∧ (v.val=15+u.val/3 ∨ 6≤v.val ∧ v.val<15 ∧ (if u.val<3 then (v.val-6)/3 else (v.val-6)%3)=u.val % 3)) → u≠v := by decide +kernel
    let y : Fin 17 → Bool := PEqualNP.Outside.L_meta_18910.DagProof.single i
    have zero : C.eval (List.ofFn y)=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨a,b,e,ha,hb⟩ := (spec y).1.mp ht
      exact rel a b e ((of_decide_eq_true ha : a=i).trans (of_decide_eq_true hb : b=i).symm)
    have h := (spec y).2 zero
    have ii : i=15 ∨ i=16 := by simpa using hi
    rcases ii with rfl|rfl <;> simpa [y,PEqualNP.Outside.L_meta_18910.DagProof.single] using h
  · have zero : C.eval (List.ofFn (fun _ : Fin 17 => false))=false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨_,_,_,_,h'⟩ := (spec _).1.mp h
      contradiction
    exact (spec _).2 zero

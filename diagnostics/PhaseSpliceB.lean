import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9762_Fold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

@[simp] theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl
@[simp] theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def unitsOn (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => u.1 ∈ K)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

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

theorem val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

theorem val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

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

abbrev Ref := Bool ⊕ ℕ

def refVal (W : List Bool) : Ref → Bool
  | Sum.inl b => b
  | Sum.inr k => W.getD k false

def na_look (m : List Ref) (i : ℕ) : Ref := m.getD i (Sum.inl false)

def na_comb (t : Bool) : Ref → Ref → Ref ⊕ (ℕ × ℕ)
  | Sum.inl a, r => Sum.inl (if a = t then r else Sum.inl a)
  | Sum.inr i, Sum.inl b => Sum.inl (if b = t then Sum.inr i else Sum.inl b)
  | Sum.inr i, Sum.inr j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)

def na_isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def na_step (n : ℕ) (st : List Ref × Dag) (g : Gate) : List Ref × Dag :=
  match g.inputs with
  | [] => (st.1 ++ [Sum.inl (na_isAnd g.op)], st.2)
  | [a] => (st.1 ++ [na_look st.1 a], st.2)
  | a :: b :: _ =>
    match na_comb (na_isAnd g.op) (na_look st.1 a) (na_look st.1 b) with
    | Sum.inl r => (st.1 ++ [r], st.2)
    | Sum.inr p => (st.1 ++ [Sum.inr (n + st.2.length)], st.2 ++ [(na_isAnd g.op, p.1, p.2)])

def na_ok (B : ℕ) : Ref → Prop
  | Sum.inl _ => True
  | Sum.inr k => k < B

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


end PEqualNP.Outside.L_meta_9762_Fold
namespace PEqualNP.Outside.L_meta_9762_Phase
open PEqualNP.CircuitLowerBounds

def flip (s x : Bool) : Bool := if s then !x else x
def op (a : Bool) : GateOp := if a then .and else .or
def bin (a x y : Bool) : Bool := if a then x && y else x || y
def go (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]

-- One global phase may be shared arbitrarily. A NOT reverses its input phase.
inductive Step (p : Nat → Bool) (k : Nat) : Gate → Gate → Prop where
  | bin (d : Bool) (a b : Nat) (av : a<k) (bv : b<k)
      (ea : p a=p k) (eb : p b=p k) :
    Step p k ⟨op d,[a,b]⟩ ⟨op (flip (p k) d),[a,b]⟩
  | inv (a : Nat) (av : a<k) (ea : p a= !(p k)) :
    Step p k ⟨.not,[a]⟩ ⟨.or,[a]⟩

inductive Chain (p : Nat → Bool) : Nat → List Gate → List Gate → Prop where
  | nil (k : Nat) : Chain p k [] []
  | cons {k g m gs ms} (a : Step p k g m) (b : Chain p (k+1) gs ms) :
    Chain p k (g::gs) (m::ms)

def linked (p : Nat → Bool) (k : Nat) (w v : List Bool) : Prop :=
  w.length=k ∧ v.length=k ∧ ∀ j<k, v.getD j false=flip (p j) (w.getD j false)

theorem snoc' (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by
  simp [List.getD_eq_getElem?_getD]

theorem old' (w : List Bool) (v : Bool) {i : Nat} (h : i<w.length) :
    (w++[v]).getD i false=w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem linked_push {p k w v} (h : linked p k w v) (x : Bool) :
    linked p (k+1) (w++[x]) (v++[flip (p k) x]) := by
  obtain ⟨hw,hv,hs⟩ := h
  refine ⟨by simp [hw],by simp [hv],?_⟩
  intro j hj
  by_cases prev : j<k
  · rw [old' v _ (by omega),old' w _ (by omega)]
    exact hs j prev
  · have ej : j=k := by omega
    subst j
    rw [← hv, snoc']
    rw [hv,← hw,snoc']

theorem op_eval (d a b : Bool) : (op d).eval [a,b]=bin d a b := by
  cases d <;> simp [op,bin,GateOp.eval]

theorem demorgan (s d a b : Bool) :
    bin (flip s d) (flip s a) (flip s b)=flip s (bin d a b) := by
  cases s <;> cases d <;> cases a <;> cases b <;> rfl

theorem step_link {p k g m w v} (h : Step p k g m) (z : linked p k w v) :
    linked p (k+1) (go w g) (go v m) := by
  cases h with
  | bin d a b av bv ea eb =>
    simp only [go,List.map_cons,List.map_nil,op_eval,z.2.2 a av,z.2.2 b bv,ea,eb,demorgan]
    exact linked_push z _
  | inv a av ea =>
    have neg : flip (!(p k)) (w.getD a false)=flip (p k) (!(w.getD a false)) := by
      cases p k <;> cases w.getD a false <;> rfl
    have ev : GateOp.or.eval [v.getD a false]=flip (p k) (!(w.getD a false)) := by
      rw [z.2.2 a av,ea,neg]
      simp [GateOp.eval]
    change linked p (k+1) (w ++ [GateOp.not.eval [w.getD a false]]) (v ++ [GateOp.or.eval [v.getD a false]])
    rw [ev]
    exact linked_push z (!(w.getD a false))

theorem steps_link {p k gs ms} (h : Chain p k gs ms) {w v} (z : linked p k w v) :
    linked p (k+gs.length) (gs.foldl go w) (ms.foldl go v) := by
  induction h generalizing w v with
  | nil => simpa using z
  | cons a b ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step_link a z)

theorem init_link (p : Nat → Bool) {n} (x : Fin n → Bool) :
    linked p n (List.ofFn x) (List.ofFn (fun i : Fin n => flip (p i) (x i))) := by
  refine ⟨by simp,by simp,?_⟩
  intro j hj
  simp [List.getD_eq_getElem?_getD,hj]

theorem chain_edges {p k gs ms} (h : Chain p k gs ms) :
    gs.length=ms.length ∧ ∀ m∈ms,
      m.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ m.inputs.length≤2 := by
  induction h with
  | nil => simp
  | cons a b ih =>
    refine ⟨by simp [ih.1],?_⟩
    intro m hm
    rcases List.mem_cons.mp hm with rfl | tail
    · cases a with
      | bin d a b av bv ea eb =>
        cases flip _ d <;> simp [op]
      | inv => simp
    · exact ih.2 m tail

theorem physical {p n} {C M : Circuit} (h : Chain p n C.gates M.gates)
    (port : C.output<n+C.gates.length) (out : M.output=C.output)
    (pos : p C.output=false) :
    M.size=C.size ∧ PEqualNP.MetaComplexity.Monotone2 M ∧
    ∀ x : Fin n → Bool,
      M.eval (List.ofFn (fun i : Fin n => flip (p i) (x i)))=C.eval (List.ofFn x) := by
  refine ⟨(chain_edges h).1.symm,(chain_edges h).2,?_⟩
  intro x
  have hx := (steps_link h (init_link p x)).2.2 C.output port
  change (M.gates.foldl go (List.ofFn (fun i : Fin n => flip (p i) (x i)))).getD M.output false =
    (C.gates.foldl go (List.ofFn x)).getD C.output false
  rw [out]
  rw [pos] at hx
  exact hx

def below {V : Type} (x y : V → Bool) : Prop := ∀ i, x i=true → y i=true
def increasing {V : Type} (h : (V → Bool) → Bool) : Prop := ∀ x y, below x y → h x=true → h y=true
def zeroNeg {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) (i : Fin n) :=
  if p i then false else x i
def posBits {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) (i : Fin n) :=
  if p i then true else x i

theorem clamp_order {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) :
    below (zeroNeg p x) x ∧ below (fun i : Fin n => flip (p i) (x i)) (posBits p x) ∧
    (fun i : Fin n => flip (p i) (zeroNeg p x i))=posBits p x := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    cases h : p i <;> simp_all [zeroNeg]
  · intro i hi
    cases h : p i <;> simp_all [flip,posBits]
  · funext i
    cases h : p i <;> simp [flip,zeroNeg,posBits,h]

theorem clamp_splice {n : Nat} (p : Nat → Bool)
    (f r m : (Fin n → Bool) → Bool) (mf : increasing f) (mm : increasing m)
    (eqn : ∀ x, (r x || m (fun i : Fin n => flip (p i) (x i)))=f x) :
    ∀ x, (r x || m (posBits p x))=f x := by
  intro x
  obtain ⟨down,up,norm⟩ := clamp_order p x
  cases h : f x with
  | false =>
    have rr : r x=false := by
      have z := (eqn x).trans h
      cases hr : r x <;> simp_all
    have rm : m (posBits p x)=false := by
      cases hm : m (posBits p x) with
      | false => rfl
      | true =>
        have t : f (zeroNeg p x)=true := by rw [← eqn,norm,hm]; simp
        exact Bool.noConfusion ((mf _ _ down t).symm.trans h)
    simp [rr,rm]
  | true =>
    have z := (eqn x).trans h
    cases hr : r x with
    | true => simp [hr]
    | false =>
      have hm : m (fun i : Fin n => flip (p i) (x i))=true := by simpa [hr] using z
      simp [hr,mm _ _ up hm]



namespace Bank
def good (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
def readGate (g : Gate) (w : List Bool) := g.op.eval (g.inputs.map fun i => w.getD i false)
def stage (w : List Bool) (g : Gate) := w ++ [readGate g w]
def run (gs : List Gate) (w : List Bool) := gs.foldl stage w
def below (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true
theorem extend {a b : List Bool} {v w : Bool} (h : below a b) (hv : v=true → w=true) :
    below (a++[v]) (b++[w]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases lt : i<a.length
  · have lt' : i<b.length := h.1 ▸ lt
    simpa [List.getD_eq_getElem?_getD,List.getElem?_append_left lt,
      List.getElem?_append_left lt'] using h.2 i
  · by_cases eq : i=a.length
    · subst i
      have last (l : List Bool) (x : Bool) : (l++[x]).getD l.length false=x := by
        simp [List.getD_eq_getElem?_getD]
      rw [last,h.1,last]
      exact hv
    · have lo : (a++[v]).length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none lo]
theorem gate_mono {a b : List Bool} {g : Gate} (h : below a b) (hg : good g) :
    readGate g a=true → readGate g b=true := by
  have op : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using hg.1
  rcases op with ha | ho
  · simp only [readGate,ha,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
    intro ht i hi
    exact h.2 i (ht i hi)
  · simp only [readGate,ho,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    rintro ⟨i,hi,hh⟩
    exact ⟨i,hi,h.2 i hh⟩
theorem run_mono {a b : List Bool} (gs : List Gate) (ok : ∀ g ∈ gs, good g)
    (h : below a b) : below (run gs a) (run gs b) := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun t ht => ok _ (by simp [ht])) (extend h (gate_mono h (ok _ (by simp))))

end Bank
open PEqualNP.Outside.L_meta_9762_Fold
open PEqualNP.MetaComplexity

theorem increasing_eval {n : Nat} (C : Circuit) (ok : Monotone2 C) :
    increasing (fun x : Fin n → Bool => C.eval (List.ofFn x)) := by
  intro x y hxy
  have b : Bank.below (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro j
    by_cases hj : j<n
    · simpa [List.getD_eq_getElem?_getD,hj] using hxy ⟨j,hj⟩
    · simp [List.getD_eq_getElem?_getD,hj]
  exact (Bank.run_mono C.gates ok b).2 C.output

def source {n : Nat} (p : Nat → Bool) (i : Fin n) : Ref :=
  if p i then Sum.inl true else Sum.inr i.val

theorem source_good (n : Nat) (p : Nat → Bool) :
    na_Good n (List.ofFn (source (n:=n) p), []) := by
  refine ⟨fun j hj => absurd hj (by simp),?_⟩
  intro r hr
  simp only [List.mem_ofFn] at hr
  obtain ⟨i,rfl⟩ := hr
  cases h : p i <;> simp [source,h,na_ok,i.isLt]

theorem source_val {n : Nat} (p : Nat → Bool) (x : Fin n → Bool) :
    (List.ofFn (source (n:=n) p)).map (refVal (wl ([] : Dag) (List.ofFn x))) =
      List.ofFn (posBits p x) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i<n := by simpa using h2
    cases h : p i <;> simp [source,posBits,refVal,wl,List.getD_eq_getElem?_getD,hi,h]

def stored (g : Bool × Nat × Nat) : Gate := ⟨op g.1,[g.2.1,g.2.2]⟩
def realize (d : Dag) (i : Nat) : Circuit := ⟨d.map stored,i⟩

theorem realize_mono (d : Dag) (i : Nat) : Monotone2 (realize d i) := by
  intro g hg
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hg
  cases h : z.1 <;> simp [stored,op,h]

theorem realize_run (d : Dag) (w : List Bool) :
    (d.map stored).foldl go w=wl d w := by
  induction d generalizing w with
  | nil => rfl
  | cons g d ih =>
    have h : go w (stored g)=wstep w g := by
      cases g with
      | mk tag ab =>
        cases tag <;> simp [go,stored,op,wstep,gop,GateOp.eval]
    change (d.map stored).foldl go (go w (stored g))=wl d (wstep w g)
    rw [h,ih]

theorem realize_eval {n : Nat} (d : Dag) (i : Nat) (x : Fin n → Bool) :
    (realize d i).eval (List.ofFn x)=val d x i := by
  exact congrArg (fun w : List Bool => w.getD i false) (realize_run d _)

def binaryPaid (gs : List Gate) : Nat := (gs.filter (fun g => g.inputs.length==2)).length

theorem fold_binary {p k gs ms} (h : Chain p k gs ms) {n : Nat}
    (st : List Ref × Dag) (hst : na_Good n st) :
    (ms.foldl (na_step n) st).2.length≤st.2.length+binaryPaid gs := by
  induction h generalizing st with
  | nil => simp [binaryPaid]
  | @cons k g m gs ms a b ih =>
    have hm : m.op ∈ ({GateOp.and,GateOp.or}:Set GateOp) ∧ m.inputs.length≤2 := by
      cases a with
      | bin d _ _ _ _ _ _ =>
        constructor
        · change (if _ then GateOp.and else GateOp.or) ∈ _
          split <;> simp
        · decide
      | inv => simp
    obtain ⟨sg,sl,_⟩ := na_step_spec n st m hm hst
    have htail := ih (na_step n st m) sg
    cases a with
    | bin => simp [binaryPaid] at htail ⊢; omega
    | inv => simpa [na_step,binaryPaid] using htail

theorem physical_splice {n : Nat} {p : Nat → Bool} {C M : Circuit}
    (h : Chain p n C.gates M.gates) (port : C.output<n+C.gates.length)
    (out : M.output=C.output) (pos : p C.output=false)
    (f r : (Fin n → Bool) → Bool) (mf : increasing f)
    (ground : f (fun _ => false)=false)
    (target : ∀ x, (r x || C.eval (List.ofFn x))=f x) :
    ∃ N : Circuit, Monotone2 N ∧ N.size≤binaryPaid C.gates ∧
      ∀ x, (r x || N.eval (List.ofFn x))=f x := by
  obtain ⟨_,ok,env⟩ := physical h port out pos
  have cl := clamp_splice p f r (fun x => M.eval (List.ofFn x)) mf (increasing_eval M ok)
    (fun x => by rw [env]; exact target x)
  let start : List Ref × Dag := (List.ofFn (source (n:=n) p),[])
  let st := M.gates.foldl (na_step n) start
  obtain ⟨_,_,sem⟩ := na_fold_spec n M.gates ok start (source_good n p)
  have size : st.2.length≤binaryPaid C.gates := by
    simpa [st,start] using fold_binary h start (source_good n p)
  have eqref (x : Fin n → Bool) :
      refVal (wl st.2 (List.ofFn x)) (na_look st.1 M.output)=M.eval (List.ofFn (posBits p x)) := by
    rw [na_look_val,sem x _ (source_val p x)]
    rfl
  rcases e : na_look st.1 M.output with bit | j
  · cases bit with
    | false =>
      refine ⟨⟨[],n⟩,by intro g hg; simp at hg,by simp [Circuit.size],?_⟩
      intro x
      have hx := eqref x
      rw [e] at hx
      have z : (⟨[],n⟩ : Circuit).eval (List.ofFn x)=false := by
        simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem?_getD]
      rw [z,show false=M.eval (List.ofFn (posBits p x)) from hx]
      exact cl x
    | true =>
      have hx := eqref (fun _ => false)
      rw [e] at hx
      have z := (cl (fun _ => false)).trans ground
      rw [← (show true=M.eval (List.ofFn (posBits p (fun _ => false))) from hx)] at z
      simp at z
  · refine ⟨realize st.2 j,realize_mono _ _,by simpa [Circuit.size,realize] using size,?_⟩
    intro x
    have hlocal := eqref x
    rw [e] at hlocal
    rw [realize_eval,show val st.2 x j=M.eval (List.ofFn (posBits p x)) from hlocal]
    exact cl x

end PEqualNP.Outside.L_meta_9762_Phase

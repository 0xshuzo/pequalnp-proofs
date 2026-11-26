import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9934_partial
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The pointwise monotonicity proof adapts the published L-meta-1892.
def m1892_stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem m1892_eval_eq (C : Circuit) (x : List Bool) :
    C.eval x = (C.gates.foldl m1892_stp x).getD C.output false := rfl

theorem m1892_getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem m1892_ev_and (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.and) :
    (g.op.eval (g.inputs.map f) = true ↔ ∀ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_ev_or (g : Gate) (f : ℕ → Bool) (h : g.op = GateOp.or) :
    (g.op.eval (g.inputs.map f) = true ↔ ∃ i ∈ g.inputs, f i = true) := by
  rw [h]
  simp [GateOp.eval]

theorem m1892_mono : ∀ (gs : List Gate) (W1 W2 : List Bool), W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl m1892_stp W1).getD i false = true → (gs.foldl m1892_stp W2).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (m1892_stp W1 g) (m1892_stp W2 g) (by simp [m1892_stp, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [m1892_stp, m1892_getD_snoc, hl]
    split_ifs
    · rcases hop g List.mem_cons_self with ha | ho
      · rw [m1892_ev_and g _ ha, m1892_ev_and g _ ha]
        intro h k hk
        exact H k (h k hk)
      · rw [m1892_ev_or g _ ho, m1892_ev_or g _ ho]
        rintro ⟨k, hk, h⟩
        exact ⟨k, hk, H k h⟩
    · exact H i

theorem m1892_all_idx (n : ℕ) (x y : List Bool) (hx : x.length = n)
    (H : ∀ i < n, x.getD i false = true → y.getD i false = true) :
    ∀ i, x.getD i false = true → y.getD i false = true := by
  intro i hi
  by_cases h : i < n
  · exact H i h hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.noConfusion hi


def Upper (v w : List Bool) : Prop :=
  v.length=w.length ∧ ∀ j, v.getD j false=true → w.getD j false=true
def Mono (p : List Gate) : Prop := ∀ g ∈ p, g.op=.and ∨ g.op=.or
def run (p : List Gate) (w : List Bool) := p.foldl m1892_stp w
theorem run_len (p : List Gate) (w : List Bool) : (run p w).length = w.length+p.length := by
  induction p generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (m1892_stp w g)).length = _
    rw [ih]
    simp [m1892_stp,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
theorem run_upper (p : List Gate) (hp : Mono p) {v w} (h : Upper v w) :
    Upper (run p v) (run p w) :=
  ⟨by rw [run_len,run_len,h.1], m1892_mono p v w h.1 hp h.2⟩
def H (a b : Bool) : Prop := a=true → b=true
theorem snoc_upper {v w} (h : Upper v w) {a b : Bool} (h' : H a b) :
    Upper (v++[a]) (w++[b]) := by
  refine ⟨by simp [h.1],?_⟩
  intro i
  rw [m1892_getD_snoc,m1892_getD_snoc,h.1]
  split
  · exact h'
  · exact h.2 i

def negwire (pins : List Nat) (w : List Bool) :=
  GateOp.not.eval (pins.map fun i => w.getD i false)
theorem neg_anti (pins : List Nat) {v w} (h : Upper v w) : H (negwire pins w) (negwire pins v) := by
  cases pins with
  | nil => exact fun _ => rfl
  | cons j js =>
    have hj := h.2 j
    cases a : v.getD j false <;> cases b : w.getD j false <;>
      simp_all [negwire,GateOp.eval,H]

def first (p : List Gate) (pins : List Nat) (x : Fin 11 → Bool) :=
  negwire pins (run p (List.ofFn x))
def afterFirst (p : List Gate) (pins : List Nat) (x : Fin 11 → Bool) :=
  (run p (List.ofFn x)) ++ [first p pins x]
def mid (p : List Gate) (pins : List Nat) (q : List Gate) (x : Fin 11 → Bool) :=
  run q (afterFirst p pins x)
def two (p : List Gate) (pins : List Nat) (q : List Gate) (keys : List Nat)
    (r : List Gate) (out : Nat) : Circuit :=
  ⟨p ++ [⟨.not,pins⟩] ++ q ++ [⟨.not,keys⟩] ++ r,out⟩

theorem two_eval (p pins q keys r out) (x : Fin 11 → Bool) :
    (two p pins q keys r out).eval (List.ofFn x) =
    (run r (mid p pins q x ++ [negwire keys (mid p pins q x)])).getD out false := by
  change ((p ++ [⟨.not,pins⟩] ++ q ++ [⟨.not,keys⟩] ++ r).foldl m1892_stp (List.ofFn x)).getD out false = _
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] <;> rfl

def mux (x : Fin 11 → Bool) :=
  (List.ofFn x).getD (3+(1*(x 0).toNat+2*(x 1).toNat+4*(x 2).toNat)) false

def rowNumbers : Fin 6 → Fin 6 → Nat := ![![168, 169, 185, 187, 251, 255],![168, 169, 185, 189, 445, 447],![152, 154, 186, 187, 251, 255],![152, 154, 186, 190, 702, 703],![56, 60, 188, 189, 445, 447],![56, 60, 188, 190, 702, 703]]

def rows (k t : Fin 6) (i : Fin 11) := (rowNumbers k t).testBit i.val
def special (a : Fin 8) (i : Fin 11) := (a.val+8*23).testBit i.val
def maj (a : Fin 8) : Bool := decide (a.val ∈ ([3,5,6,7] : List Nat))
theorem rows_inc : ∀ (k i j : Fin 6), i≤j → ∀ v : Fin 11, rows k i v=true → rows k j v=true := by decide +kernel
theorem mux_rows : ∀ (k : Fin 6), mux (rows k 0)=true ∧ mux (rows k 1)=false ∧ mux (rows k 2)=true ∧
    mux (rows k 3)=false ∧ mux (rows k 4)=true ∧ mux (rows k 5)=false := by decide +kernel
theorem upper_inputs (x y : Fin 11 → Bool) (h : ∀ i, x i=true → y i=true) :
    Upper (List.ofFn x) (List.ofFn y) :=
  ⟨by simp, m1892_all_idx 11 _ _ (by simp) (by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getD_eq_getElem _ _ (by simpa using hj)]
    simpa only [List.getElem_ofFn] using h ⟨j,hj⟩)⟩

theorem middle (a b t : Fin 6 → Bool)
    (ha : ∀ i j, i≤j → H (a j) (a i))
    (hb : ∀ i j, i≤j → H (a i) (a j) → H (b j) (b i))
    (ht : ∀ i j, i≤j → H (a i) (a j) → H (b i) (b j) → H (t i) (t j))
    (hf : t 0=true ∧ t 1=false ∧ t 2=true ∧ t 3=false ∧ t 4=true ∧ t 5=false) :
    a 2=true ∧ a 3=false := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := hf
  have bad (i j : Fin 6) (ij : i≤j) (same : H (a i) (a j))
      (v : t i=true) (w : t j=false) : b i=true ∧ b j=false := by
    have no : ¬ H (b i) (b j) := by
      intro h
      have hv := ht i j ij same h v
      simp [w] at hv
    cases hi : b i <;> cases hj : b j <;> simp_all [H]
  constructor
  · by_contra! h
    have f2 : a 2=false := by cases e : a 2 <;> simp_all
    have f3 : a 3=false := by
      cases e : a 3
      · rfl
      · exact (Bool.false_ne_true (f2.symm.trans (ha 2 3 (by decide) e))).elim
    have f4 : a 4=false := by
      cases e : a 4
      · rfl
      · exact (Bool.false_ne_true (f2.symm.trans (ha 2 4 (by decide) e))).elim
    have x := bad 2 3 (by decide) (by simp [H,f2]) h2 h3
    have y := bad 4 5 (by decide) (by simp [H,f4]) h4 h5
    have z := hb 3 4 (by decide) (by simp [H,f3]) y.1
    simp [x.2] at z
  · by_contra! h
    have t3 : a 3=true := by cases e : a 3 <;> simp_all
    have t2 := ha 2 3 (by decide) t3
    have t1 := ha 1 3 (by decide) t3
    have x := bad 0 1 (by decide) (by simp [H,t1]) h0 h1
    have y := bad 2 3 (by decide) (by simp [H,t3]) h2 h3
    have z := hb 1 2 (by decide) (by simp [H,t2]) y.1
    simp [x.2] at z

theorem first_cut (p pins q keys r out) (pM : Mono p) (qM : Mono q) (rM : Mono r)
    (ev : ∀ x, (two p pins q keys r out).eval (List.ofFn x)=mux x) (k : Fin 6) :
    first p pins (rows k 2)=true ∧ first p pins (rows k 3)=false := by
  let a := fun t => first p pins (rows k t)
  let b := fun t => negwire keys (mid p pins q (rows k t))
  have pp (i j : Fin 6) (h : i≤j) :=
    run_upper p pM (upper_inputs _ _ (rows_inc k i j h))
  have mm (i j : Fin 6) (h : i≤j) (ha : H (a i) (a j)) :
      Upper (mid p pins q (rows k i)) (mid p pins q (rows k j)) :=
    run_upper q qM (snoc_upper (pp i j h) ha)
  apply middle a b (fun t => mux (rows k t))
  · intro i j h
    exact neg_anti pins (pp i j h)
  · intro i j h u
    exact neg_anti keys (mm i j h u)
  · intro i j h u v
    have hh := (run_upper r rM (snoc_upper (mm i j h u) v)).2 out
    rw [← two_eval, ← two_eval, ev,ev] at hh
    exact hh
  · exact mux_rows k

theorem first_majority (p pins q keys r out) (pM : Mono p) (qM : Mono q) (rM : Mono r)
    (ev : ∀ x, (two p pins q keys r out).eval (List.ofFn x)=mux x) (d : Fin 8) :
    first p pins (special d)= !(maj d) := by
  have known := first_cut p pins q keys r out pM qM rM ev
  have atRow (v : Fin 8) (k t : Fin 6) (eq : ∀ i, special v i=rows k t i) :
      first p pins (special v)=first p pins (rows k t) :=
    congrArg (first p pins) (funext eq)
  have one : first p pins (special 1)=true := (atRow 1 0 2 (by decide +kernel)).trans (known 0).1
  have three : first p pins (special 3)=false := (atRow 3 0 3 (by decide +kernel)).trans (known 0).2
  fin_cases d
  · have h := neg_anti pins (run_upper p pM (upper_inputs (special 0) (special 1) (by decide +kernel)))
    exact h one
  · exact (atRow 1 0 2 (by decide +kernel)).trans (known 0).1
  · exact (atRow 2 2 2 (by decide +kernel)).trans (known 2).1
  · exact (atRow 3 0 3 (by decide +kernel)).trans (known 0).2
  · exact (atRow 4 4 2 (by decide +kernel)).trans (known 4).1
  · exact (atRow 5 1 3 (by decide +kernel)).trans (known 1).2
  · exact (atRow 6 3 3 (by decide +kernel)).trans (known 3).2
  · have h := neg_anti pins (run_upper p pM (upper_inputs (special 3) (special 7) (by decide +kernel)))
    change first p pins (special 7)=false
    cases e : first p pins (special 7)
    · rfl
    · exact (Bool.false_ne_true (three.symm.trans (h e))).elim

end PEqualNP.Outside.L_meta_9934_partial

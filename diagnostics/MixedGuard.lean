import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9939_rank
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
  change ((p ++ [Gate.mk .not pins] ++ q ++ [Gate.mk .not keys] ++ r).foldl m1892_stp (List.ofFn x)).getD out false = _
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

def row (x : Nat) (i : Fin 11) : Bool := x.testBit i.val
set_option maxHeartbeats 0 in
def slice (a : Fin 4) (c : Bool) (d : Nat) := row (a.val+4*c.toNat+8*d)
def makeLow (a : Fin 4) (d : Fin 256) := d.val ||| (1 <<< a.val)
def clearHigh (a : Fin 4) (d : Fin 256) := d.val &&& (255 ^^^ (1 <<< (a.val+4)))
def leAddr (x y : Fin 11 → Bool) : Prop :=
  (∀ i, x i=true → y i=true) ∧ x 0 = y 0 ∧ x 1 = y 1
def pre (x : Fin 11→Bool) := ((List.ofFn x) ++ [!(x 0)]) ++ [!(x 1)]
def guardWire (p : List Gate) (pins : List Nat) (x : Fin 11→Bool) := negwire pins (run p (pre x))
def guarded (p : List Gate) (pins : List Nat) (q : List Gate) (out : Nat) (x : Fin 11→Bool) :=
  (run q ((run p (pre x)) ++ [guardWire p pins x])).getD out false
theorem comp_pre {x y : Fin 11→Bool} (h : leAddr x y) : Upper (pre x) (pre y) := by
  exact snoc_upper (snoc_upper (upper_inputs x y h.1) (by rw [h.2.1]; exact id))
    (by rw [h.2.2]; exact id)
theorem antitone_guard (p pins) (pm : Mono p) {x y} (h : leAddr x y) :
    H (guardWire p pins y) (guardWire p pins x) :=
  neg_anti pins (run_upper p pm (comp_pre h))
theorem guard_fall (p pins q out) (pm : Mono p) (qm : Mono q)
    (ev : ∀ x, guarded p pins q out x = mux x) {x y} (h : leAddr x y)
    (yes : mux x=true) (no : mux y=false) :
    guardWire p pins x=true ∧ guardWire p pins y=false := by
  have bad (z : H (guardWire p pins x) (guardWire p pins y)) : False := by
    have u := (run_upper q qm (snoc_upper (run_upper p pm (comp_pre h)) z)).2 out
    change guarded p pins q out x=true → guarded p pins q out y=true at u
    rw [ev,ev,yes,no] at u
    exact Bool.noConfusion (u rfl)
  cases a : guardWire p pins x <;> cases b : guardWire p pins y <;> simp_all [H]
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem test_slices : ∀ (a : Fin 4) (d : Fin 256),
    (d.val.testBit (a.val+4)=false →
      leAddr (slice a false d.val) (slice a false (makeLow a d)) ∧
      leAddr (slice a false (makeLow a d)) (slice a true (makeLow a d)) ∧
      mux (slice a false (makeLow a d))=true ∧ mux (slice a true (makeLow a d))=false) ∧
    (d.val.testBit a.val=true →
      leAddr (slice a true (clearHigh a d)) (slice a true d.val) ∧
      leAddr (slice a false (clearHigh a d)) (slice a true (clearHigh a d)) ∧
      mux (slice a false (clearHigh a d))=true ∧ mux (slice a true (clearHigh a d))=false) := by
  unfold leAddr
  decide +kernel
theorem guard_sandwich (p pins q out) (pm : Mono p) (qm : Mono q)
    (ev : ∀ x, guarded p pins q out x=mux x) (a : Fin 4) (d : Fin 256) :
    (d.val.testBit (a.val+4)=false → guardWire p pins (slice a false d.val)=true) ∧
    (d.val.testBit a.val=true → guardWire p pins (slice a true d.val)=false) := by
  constructor
  · intro h
    obtain ⟨inc0,inc1,y,n⟩ := (test_slices a d).1 h
    exact antitone_guard p pins pm inc0 (guard_fall p pins q out pm qm ev inc1 y n).1
  · intro h
    obtain ⟨inc0,inc1,y,n⟩ := (test_slices a d).2 h
    have bound := antitone_guard p pins pm inc0
    have nope := (guard_fall p pins q out pm qm ev inc1 y n).2
    cases e : guardWire p pins (slice a true d.val)
    · rfl
    · exact False.elim (by have z := bound e; rw [nope] at z; contradiction)

end PEqualNP.Outside.L_meta_9939_rank

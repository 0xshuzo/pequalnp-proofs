import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17661


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


open PEqualNP.HeptadCover PEqualNP.GenericRejection

abbrev PS := Finset (Fin 13)
def qrow (Q : PS) := incidenceInput Q (missLines singerLines3 Q)
def faults (C : Circuit) := (quadrangles singerLines3).filter fun Q => C.eval (qrow Q) = true
def Good (C : Circuit) := RightOnIncidentPairs singerLines3 C ∧ (faults C).Nonempty

def Covers (x y z : List Bool) := ∀ i, x.getD i false = true → y.getD i false = true → z.getD i false = true

theorem covers_step {x y z : List Bool} (xy : x.length = y.length) (xz : x.length = z.length)
    (h : Covers x y z) {g : Gate} (op : g.op = .and) : Covers (step x g) (step y g) (step z g) := by
  intro i a b
  by_cases lt : i < x.length
  · rw [step_lt _ _ _ lt] at a
    rw [step_lt _ _ _ (by omega)] at b ⊢
    exact h i a b
  · by_cases eq : i = x.length
    · rw [step_last _ _ _ eq,op] at a
      rw [step_last _ _ _ (by omega),op] at b ⊢
      exact (eval_and_iff _ _).mpr (fun j hj => h j ((eval_and_iff _ _).mp a j hj) ((eval_and_iff _ _).mp b j hj))
    · rw [getD_ge _ _ (by rw [step_len]; omega)] at a
      contradiction

theorem covers_fold (gs : List Gate) (ops : ∀ g∈gs, g.op = .and) {x y z : List Bool}
    (xy : x.length = y.length) (xz : x.length = z.length) (h : Covers x y z) :
    Covers (W gs x) (W gs y) (W gs z) := by
  induction gs generalizing x y z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun a ha => ops a (List.mem_cons_of_mem _ ha)) (by simpa only [step_len] using congrArg (· + 1) xy)
      (by simpa only [step_len] using congrArg (· + 1) xz) (covers_step xy xz h (ops g List.mem_cons_self))

def flag0 := incidenceInput ({0} : PS) ({0} : PS)
def flag1 := incidenceInput ({1} : PS) ({1} : PS)

theorem disjointRaw : ∀ i : Fin 26, ¬(flag0.getD i.val false = true ∧ flag1.getD i.val false = true) := by decide

theorem requires_or (C D : Circuit) (hm : Monotone2 C) (good : Good C) (other : Good D)
    (dis : Disjoint (faults C) (faults D)) : ∃ k g, C.gates[k]?=some g ∧ g.op=.or := by
  classical
  by_contra no
  have onlyAnd (g : Gate) (hg : g∈C.gates) : g.op = .and := by
    rcases (hm g hg).1 with hand|hor
    · exact hand
    · obtain ⟨k,hk,eq⟩ := List.getElem_of_mem hg
      exact (no ⟨k,g,List.getElem?_eq_some_iff.mpr ⟨hk,eq⟩,hor⟩).elim
  obtain ⟨Q,Qd⟩ := other.2
  have r0 : C.eval flag0 = true := good.1 0 0 (by decide)
  have r1 : C.eval flag1 = true := good.1 1 1 (by decide)
  have inp : Covers flag0 flag1 (qrow Q) := by
    intro i a b
    by_cases lt : i<26
    · exact (disjointRaw ⟨i,lt⟩ ⟨a,b⟩).elim
    · rw [getD_ge _ _ (by change 26 ≤ i; omega)] at a
      contradiction
  have row : (qrow Q).length=26 := by simp [qrow,incidenceInput]
  have cov := covers_fold C.gates onlyAnd (x:=flag0) (y:=flag1) (z:=qrow Q)
    (by decide) (by rw [row]; decide) inp
  have Qc : Q∈faults C := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp Qd).1,cov C.output r0 r1⟩
  exact Finset.disjoint_left.mp dis Qc Qd

theorem requires_and (C : Circuit) {k : Nat} (op : (gateAt C k).op=.and) :
    ∃ i g, C.gates[i]?=some g ∧ g.op=.and := by
  by_cases h : k<C.gates.length
  · exact ⟨k,C.gates[k],List.getElem?_eq_getElem h, by rwa [gateAt_eq h] at op⟩
  · rw [gateAt_ge (by omega)] at op
    contradiction

theorem sibling_equivalence : (let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.or) → False) ↔ (let x1 : Type := PEqualNP.CircuitLowerBounds.Circuit; have x2 : ℕ := (26 : ℕ); have x3 : x1 → Finset (Finset (Fin (13 : ℕ))) := fun (x3 : x1) => {x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3 | PEqualNP.CircuitLowerBounds.Circuit.eval x3 (PEqualNP.GenericRejection.incidenceInput x4 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x4)) = Bool.true}; have x4 : x1 → Prop := fun (x4 : x1) => PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 x4 ∧ (x3 x4).Nonempty; have x5 : x1 → ℕ → x1 := fun (x5 : x1) (x6 : ℕ) => { gates := x5.gates.set x6 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate }, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit }; have x6 : x1 → ℕ → Prop := fun (x6 : x1) (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and; ∀ (x7 x8 : x1), x7.gates = x8.gates → PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack x2 x7 → PEqualNP.CircuitLowerBounds.Circuit.size x7 < (63 : ℕ) → (∃ (x13 : ℕ) (x14 : ℕ), x6 x7 x13 ∧ x6 x7 x14 ∧ PEqualNP.EdgeOwnership.InCone x2 x7 x13 x14) → x4 x7 → x4 x8 → Disjoint (x3 x7) (x3 x8) → (∀ x17 < PEqualNP.CircuitLowerBounds.Circuit.size x7, ¬(x4 (x5 x7 x17) ∧ x4 (x5 x8 x17)) ∧ (x6 x7 x17 → ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x17).inputs, ¬Disjoint (x3 (PEqualNP.CircuitMoves.eraseGate x2 x7 x17 x20)) (x3 (PEqualNP.CircuitMoves.eraseGate x2 x8 x17 x20)))) → (∃ (x18 : ℕ) (x19 : PEqualNP.CircuitLowerBounds.Gate), x7.gates[x18]? = Option.some x19 ∧ x19.op = PEqualNP.CircuitLowerBounds.GateOp.and) → False) := by
  dsimp only
  constructor
  · intro h C D eq mono back size nested cgood dgood dis fragile _
    exact h C D eq mono back size nested cgood dgood dis fragile (requires_or C D mono cgood dgood dis)
  · intro h C D eq mono back size nested cgood dgood dis fragile _
    obtain ⟨i,j,hi,hj,path⟩ := nested
    exact h C D eq mono back size ⟨i,j,hi,hj,path⟩ cgood dgood dis fragile (requires_and C hi)

end PEqualNP.Outside.L_meta_17661

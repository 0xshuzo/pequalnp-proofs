import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2082_clone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

-- The prefix evaluation identities are from L_meta_7933.
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)





def stepAnd (n : ℕ) (C : Circuit) : Gate := ⟨.and,[C.output,n+C.size]⟩
def extend (n : ℕ) (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g,stepAnd n C], n+C.size+1⟩

theorem duplicate {n : ℕ} (C : Circuit) (i : ℕ) (hi : i<C.size)
    (out : C.output=n+i) (legal : IsAO2 n C) (nd : ∀ g∈C.gates,g.inputs.Nodup) :
    let g := gateAt C i
    let D := extend n C g
    D.size = C.size+2 ∧ IsAO2 n D ∧ (∀ h∈D.gates,h.inputs.Nodup) ∧
    (∀ x : List Bool, x.length=n → D.eval x=C.eval x ∧
      (D.wires x).getD C.output false=C.eval x ∧
      (D.wires x).getD (n+C.size) false=C.eval x) ∧
    D.gates[C.size+1]?=some (stepAnd n C) := by
  let g := gateAt C i
  let D := extend n C g
  change D.size = _ ∧ _
  have hg : g = C.gates[i] := List.getD_eq_getElem _ _ hi
  have mem : g ∈ C.gates := hg ▸ List.getElem_mem _
  have idx : ∀ j, j<C.size → gateAt D j=gateAt C j := by
    intro j hj
    exact List.getD_append _ _ _ _ hj
  have opAt : gateAt D C.size = g := by
    change (C.gates ++ [g,stepAnd n C]).getD C.gates.length _ = g
    simp [List.getD_eq_getElem?_getD]
  have andAt : gateAt D (C.size+1) = stepAnd n C := by
    change (C.gates ++ [g,stepAnd n C]).getD (C.gates.length+1) _ = _
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  have terminal : D.gates[C.size+1]?=some (stepAnd n C) := by
    change (C.gates ++ [g,stepAnd n C])[C.gates.length+1]?=_
    simp [List.getElem?_append_right]
  have size : D.size = C.size+2 := by simp [D,extend,Circuit.size]
  have splitMem (h : Gate) (hh : h∈D.gates) : h∈C.gates ∨ h=g ∨ h=stepAnd n C := by
    simpa [D,extend] using hh
  have ao : IsAO2 n D := by
    refine ⟨?_,?_,?_⟩
    · intro h hh
      rcases splitMem h hh with ha|rfl|rfl
      · exact legal.1 h ha
      · exact legal.1 g mem
      · exact Or.inl rfl
    · intro j hj w hw
      have hj' : j < C.size+2 := by change j < D.size at hj; omega
      rcases Nat.lt_trichotomy j C.size with h|rfl|h
      · rw [idx j h] at hw
        exact legal.2.1 j h w hw
      · rw [opAt] at hw
        have := legal.2.1 i hi w hw
        omega
      · have eq : j = C.size+1 := by omega
        subst j
        rw [andAt] at hw
        simp only [stepAnd,List.mem_cons,List.mem_singleton] at hw
        omega
    · intro h hh
      rcases splitMem h hh with ha|rfl|rfl
      · exact legal.2.2 h ha
      · exact legal.2.2 g mem
      · rfl
  refine ⟨size,ao,?_,?_,terminal⟩
  · intro h hh
    rcases splitMem h hh with ha|rfl|rfl
    · exact nd h ha
    · exact nd g mem
    · have diff : C.output ≠ n+C.size := by omega
      simpa [stepAnd] using diff
  · intro x lx
    let w := run C.gates x
    let v := g.op.eval (g.inputs.map fun t => w.getD t false)
    have len : w.length=n+C.size := by simp [w,run_length,lx,Circuit.size]
    have shadow : w.getD C.output false=v := by
      rw [out,← lx]
      change (run C.gates x).getD (x.length+i) false = _
      rw [run_gate _ _ i hi]
      rw [← hg]
      congr 1
      apply List.map_congr_left
      intro t ht
      have bound := legal.2.1 i hi t ht
      rw [if_pos (by omega)]
    have old : (D.wires x).getD C.output false = w.getD C.output false :=
      run_prefix C.gates _ x C.output (by change C.output < x.length+C.size; omega)
    have intermediate : run (C.gates++[g]) x=w++[v] := run_snoc _ _ _
    have allW : D.wires x = (w++[v]) ++ [v] := by
      change run (C.gates++[g,stepAnd n C]) x = _
      rw [show C.gates++[g,stepAnd n C]=(C.gates++[g])++[stepAnd n C] by simp]
      rw [run_snoc,intermediate]
      have a : (w++[v]).getD C.output false=v :=
        (getD_lt _ _ _ (by omega)).trans shadow
      have b : (w++[v]).getD (n+C.size) false=v := by rw [← len,getD_at]
      simp [stepAnd,GateOp.eval,a,b]
    have copy : (D.wires x).getD (n+C.size) false=v := by
      rw [allW, getD_lt _ _ _ (by simp; omega),← len,getD_at]
    have answer : D.eval x=v := by
      change (D.wires x).getD (n+C.size+1) false=v
      rw [allW,show n+C.size+1=(w++[v]).length by simp; omega,getD_at]
    exact ⟨answer.trans shadow.symm,old,copy.trans shadow.symm⟩

end PEqualNP.Outside.L_meta_2082_clone

-- Totality of the mark recurrence is the published L_meta_2621.



namespace PEqualNP.Outside.L_meta_2621
open PEqualNP.CircuitLowerBounds

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fl_at (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < gs.length) :
    (fl F gs w).getD (w.length + k) false = F (fl F (gs.take k) w) gs[k] ∧
      ∀ a, a < w.length + k → (fl F gs w).getD a false = (fl F (gs.take k) w).getD a false := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (fl F (gs.take k) w).length = w.length + k := by
    rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have e : fl F gs w = fl F (gs.drop (k + 1))
      (fl F (gs.take k) w ++ [F (fl F (gs.take k) w) gs[k]]) := by
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  constructor
  · rw [e, fl_keep _ _ _ _ (by simp; omega), ← hlen]
    simp
  · intro a ha
    rw [e, fl_keep _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]

def sel (op : GateOp) (p q : Bool) : Bool :=
  match op with
  | GateOp.and => p
  | _ => q

end PEqualNP.Outside.L_meta_2621

open PEqualNP.Outside.L_meta_2621 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro C hC x3 x4
  obtain ⟨_, hrb, _⟩ := hC
  let F : List Bool → Gate → Bool := fun D g =>
    sel g.op
      (x4.getD (g.inputs.getD 0 0) false && D.getD (g.inputs.getD 1 0) false
        || D.getD (g.inputs.getD 0 0) false && x4.getD (g.inputs.getD 1 0) false)
      (D.getD (g.inputs.getD 0 0) false || D.getD (g.inputs.getD 1 0) false)
  let W0 : List Bool := (List.range 26).map (fun i => decide (i = x3))
  have hW0 : W0.length = 26 := by simp [W0]
  refine ⟨fun w => (fl F C.gates W0).getD w false, ?_, ?_⟩
  · intro w hw
    show (fl F C.gates W0).getD w false = _
    rw [fl_keep _ _ _ _ (by omega)]
    simp [W0, List.getD_eq_getElem?_getD, hw]
  · intro k g a b hk hin
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hk
    have hlt2 : ∀ i ∈ [a, b], i < 26 + k := by
      intro i hi
      refine hrb k hlt i ?_
      have : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hlt]
      rw [this, hg, hin]
      exact hi
    obtain ⟨h1, h2⟩ := fl_at F C.gates W0 k hlt
    rw [hW0, hg] at h1
    rw [hW0] at h2
    have ea := h2 a (hlt2 a (by simp))
    have eb := h2 b (hlt2 b (by simp))
    have hF : F (fl F (C.gates.take k) W0) g
        = sel g.op
          (x4.getD a false && (fl F (C.gates.take k) W0).getD b false
            || (fl F (C.gates.take k) W0).getD a false && x4.getD b false)
          ((fl F (C.gates.take k) W0).getD a false || (fl F (C.gates.take k) W0).getD b false) := by
      show sel g.op _ _ = _
      rw [hin]
      rfl
    constructor
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = (x4.getD a false && (fl F C.gates W0).getD b false
          || (fl F C.gates W0).getD a false && x4.getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = ((fl F C.gates W0).getD a false || (fl F C.gates W0).getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl


-- The final cold conjunction criterion is adapted from R_meta_2081_317.


open PEqualNP.CircuitLowerBounds

-- A final conjunction has zero mark if both ordinary operands are false.
-- The two factors need this property on the point singleton and the line singleton.
-- On every input their intersection must be exactly the incidence function.

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_2082_factor (budget : ℕ)
    (factor :
      ∃ C : Circuit, C.size ≤ budget ∧ PEqualNP.TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13 → Bool,
          C.eval (List.ofFn (Fin.addCases p l)) = true ↔
          ∃ j : Fin 13, l j = true ∧
            (p j || p (j + 1) || p (j + 3) || p (j + 9)) = true) ∧
        ∃ k a b : Nat, C.output = 26 + k ∧
          C.gates[k]? = some ⟨.and,[a,b]⟩ ∧
          ∀ s : Bool,
            let ws := C.wires (List.ofFn fun i : Fin 26 =>
              decide (i.val = if s = true then 13 else 0))
            ws.getD a false = false ∧ ws.getD b false = false)
    (traces : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C →
      ∀ (r : Nat) (ws : List Bool), ∃ d : Nat → Bool,
        (∀ n < 26, d n = decide (n = r)) ∧
        ∀ (k : Nat) (g : Gate) (a b : Nat), C.gates[k]? = some g →
          g.inputs = [a,b] →
          (g.op = .and → d (26 + k) = ((ws.getD a false && d b) || (d a && ws.getD b false))) ∧
          (g.op = .or → d (26 + k) = (d a || d b))) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ budget ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  classical
  dsimp only
  obtain ⟨C, hs, hAO, hnd, heval, k, a, b, hout, hgate, hcold⟩ := factor
  refine ⟨C, hs, hAO, hnd, ?_, ?_, ?_⟩
  · intro i j hij
    apply (heval (fun t => decide (t = i)) (fun t => decide (t = j))).2
    refine ⟨j, by simp, ?_⟩
    rcases hij with h | h | h | h <;> subst i <;> simp
  · intro p _
    let l : Fin 13 → Bool := fun j => !(p j || p (j + 1) || p (j + 3) || p (j + 9))
    change C.eval (List.ofFn (Fin.addCases p l)) = false
    cases hv : C.eval (List.ofFn (Fin.addCases p l)) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hp⟩ := (heval p l).1 hv
      change (!(p j || p (j + 1) || p (j + 3) || p (j + 9))) = true at hj
      rw [hp] at hj
      contradiction
  · intro s
    let ws := C.wires (List.ofFn fun i : Fin 26 =>
      decide (i.val = if s = true then 13 else 0))
    obtain ⟨d, hraw, hrec⟩ := traces C hAO (if s = true then 0 else 13) ws
    refine ⟨d, hraw, hrec, ?_⟩
    obtain ⟨ha, hb⟩ := hcold s
    change ws.getD a false = false at ha
    change ws.getD b false = false at hb
    rw [hout, (hrec k ⟨.and,[a,b]⟩ a b hgate rfl).1 rfl, ha, hb]
    simp

namespace PEqualNP.Outside.L_meta_2082_clone

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

def plane (x : Fin 26 → Bool) : Prop :=
  ∃ j : Fin 13, x (Fin.natAdd 13 j) = true ∧
    (x (Fin.castAdd 13 j) || x (Fin.castAdd 13 (j+1)) ||
      x (Fin.castAdd 13 (j+3)) || x (Fin.castAdd 13 (j+9))) = true

def full (C : Circuit) : Prop := ∀ x : Fin 26 → Bool, C.eval (List.ofFn x)=true ↔ plane x

def ordinary (k : ℕ) : Prop :=
  ∃ C : Circuit, C.size ≤ k ∧ IsAO2 26 C ∧ (∀ g∈C.gates,g.inputs.Nodup) ∧ full C

def flagged (k : ℕ) : Prop := have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ k ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false

private theorem coldTable : ∀ u : Fin 26, ¬ plane (fun i : Fin 26 => decide (i.val=u.val)) := by
  unfold plane
  decide +kernel

private theorem outputGate {C : Circuit} (fullC : full C) :
    ∃ i < C.size, C.output=26+i := by
  have lower : 26 ≤ C.output := by
    by_contra! sm
    let u : Fin 26 := ⟨C.output,sm⟩
    let x := fun i : Fin 26 => decide (i.val=u.val)
    have live : C.eval (List.ofFn x) = true := by
      change (run C.gates (List.ofFn x)).getD C.output false = true
      rw [run_input _ _ _ (by simpa using sm),List.getD_eq_getElem _ _ (by simpa using sm)]
      simp [x,u]
    exact coldTable u ((fullC x).mp live)
  have upper : C.output < 26+C.size := by
    by_contra! big
    have on : plane (fun _ => true) := ⟨0,rfl,rfl⟩
    have live := (fullC (fun _ => true)).mpr on
    change (run C.gates (List.ofFn (fun _ : Fin 26 => true))).getD C.output false = true at live
    rw [List.getD_eq_default _ _ (by simpa [run_length,Circuit.size] using big)] at live
    contradiction
  exact ⟨C.output-26,by omega,by omega⟩

theorem inflate (k : ℕ) (existsC : ordinary k) : flagged (k+2) := by
  obtain ⟨C,sz,ao,nd,fc⟩ := existsC
  obtain ⟨i,hi,hout⟩ := outputGate fc
  let D := extend 26 C (gateAt C i)
  obtain ⟨ds,da,dn,ev,terminal⟩ := duplicate C i hi hout ao nd
  change D.size=C.size+2 at ds
  apply PEqualNP.Outside.L_meta_2082_factor (k+2) _ PEqualNP.Outside.L_meta_2621
  refine ⟨D,by omega,da,dn,?_,C.size+1,C.output,26+C.size,?_,terminal,?_⟩
  · intro p l
    rw [(ev (List.ofFn (Fin.addCases p l)) (by simp)).1]
    simpa [plane] using fc (Fin.addCases p l)
  · change 26+C.size+1=26+(C.size+1)
    omega
  · intro side
    let u : Fin 26 := if side then 13 else 0
    let x := fun i : Fin 26 => decide (i.val = if side = true then 13 else 0)
    have cold : C.eval (List.ofFn x) = false := by
      cases hv : C.eval (List.ofFn x)
      · rfl
      · have raw := (fc x).mp hv
        have same : x = (fun i : Fin 26 => decide (i.val=u.val)) := by cases side <;> rfl
        rw [same] at raw
        exact (coldTable u raw).elim
    obtain ⟨_,a,b⟩ := ev (List.ofFn x) (by simp)
    exact ⟨a.trans cold,b.trans cold⟩

theorem floor_from_L2082 (h : ¬ flagged 64) (C : Circuit) (ao : IsAO2 26 C)
    (nd : ∀ g ∈ C.gates,g.inputs.Nodup) (fc : full C) : 63 ≤ C.size := by
  by_contra! low
  exact h (inflate 62 ⟨C,by omega,ao,nd,fc⟩)

end PEqualNP.Outside.L_meta_2082_clone

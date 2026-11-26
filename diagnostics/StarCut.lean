import PEqualNP.Outside.L_meta_9785

namespace L9736StarCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := Fin 10
def fullEdges : List (Nat × Nat) := [(0,4),(0,5),(1,2),(1,6),(2,3),(2,7),(3,4),(3,8),(4,9),(5,7),(5,8),(6,8),(6,9),(7,9)]
def full (x : V → Bool) : Prop := ∃ u v : V, (u.val,v.val) ∈ fullEdges ∧ x u = true ∧ x v = true
def lift (x : V → Bool) (i : V) : Bool :=
  if i = 2 then x 2 && (x 1 || x 7) else x i
def source (x : V → Bool) : List Bool :=
  [x 0,x 1,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 1 || x 7,x 2 && ((x 1 || x 7) || x 3)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lift_correct : ∀ x : V → Bool, full (lift x) ↔ PEqualNP.Outside.L_meta_9785_aux.G10Edge x := by
  unfold full PEqualNP.Outside.L_meta_9785_aux.G10Edge
  decide +kernel

def ren (w : Nat) : Nat := ([0,1,3,4,5,6,7,8,9,10,11] : List Nat).getD w (w + 1)
theorem ren_lt : ∀ i : Fin 11, ren i.val < 12 := by decide
theorem ren_ge {w : Nat} (h : 11 ≤ w) : ren w = w + 1 := List.getD_eq_default _ _ h

theorem getD_ge (w : List Bool) (i : Nat) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def gstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem gstep_length (w : List Bool) (g : Gate) : (gstep w g).length = w.length + 1 := by
  simp [gstep]

theorem gstep_getD_lt (w : List Bool) (g : Gate) {i : ℕ} (h : i < w.length) :
    (gstep w g).getD i false = w.getD i false :=
  List.getD_append _ _ _ _ h

theorem gstep_getD_last (w : List Bool) (g : Gate) :
    (gstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [gstep, List.getD_eq_getElem?_getD]

theorem gstep_or (w : List Bool) (a b : ℕ) :
    (gstep w ⟨.or, [a, b]⟩).getD w.length false = (w.getD a false || w.getD b false) := by
  rw [gstep_getD_last]; simp [GateOp.eval]

theorem fold_length (gs : List Gate) : ∀ w : List Bool,
    (gs.foldl gstep w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih => intro w; rw [List.foldl_cons, ih, gstep_length, List.length_cons]; omega

theorem fold_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl gstep w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ _ (by rw [gstep_length]; omega), gstep_getD_lt _ _ h]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

-- A gate with its wires renamed.
def renGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ren⟩

-- The wire list `w'` carries every wire of `w` at its renamed place.
def Agree (w w' : List Bool) : Prop :=
  w'.length = w.length + 1 ∧ 11 ≤ w.length ∧ ∀ i, w'.getD (ren i) false = w.getD i false

-- Evaluating gates on `w` and the renamed gates on `w'` keeps the two wire lists in agreement.
theorem agree_fold (gs : List Gate) : ∀ w w' : List Bool, Agree w w' →
    Agree (gs.foldl gstep w) ((gs.map renGate).foldl gstep w') := by
  induction gs with
  | nil => intro w w' h; exact h
  | cons g gs ih =>
    rintro w w' ⟨hl, h12, hr⟩
    refine ih _ _ ⟨by rw [gstep_length, gstep_length, hl], by rw [gstep_length]; omega,
      fun i => ?_⟩
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · have hi' : ren i < w'.length := by
        by_cases h : i < 11
        · exact (ren_lt ⟨i, h⟩).trans_le (by omega)
        · rw [ren_ge (by omega)]; omega
      rw [gstep_getD_lt _ _ hi', gstep_getD_lt _ _ hi, hr]
    · rw [ren_ge h12, ← hl, gstep_getD_last, gstep_getD_last]
      simp only [renGate, List.map_map, Function.comp_def, hr]
    · rw [ren_ge (by omega), getD_ge _ _ (by rw [gstep_length]; omega),
        getD_ge _ _ (by rw [gstep_length]; omega)]


def prep : List Gate := [⟨.or,[1,7]⟩,⟨.and,[2,10]⟩]
def prepW (x : V → Bool) := prep.foldl gstep (List.ofFn x)
theorem prep_length (x : V → Bool) : (prepW x).length = 12 := by
  rw [prepW, fold_length, List.length_ofFn]; rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem prep_inputs : ∀ (x : V → Bool) (i : Fin 11),
    (prepW x).getD (ren i.val) false = (source (lift x)).getD i.val false := by decide +kernel

theorem prep_agree (x : V → Bool) : Agree (source (lift x)) (prepW x) := by
  refine ⟨by rw [prep_length]; rfl, by decide, fun i => ?_⟩
  by_cases h : i < 11
  · exact prep_inputs x ⟨i,h⟩
  · rw [ren_ge (by omega), getD_ge _ _ (by rw [prep_length]; omega),
      getD_ge _ _ (by change 11 ≤ i; omega)]

def shifted (C : Circuit) : Circuit := ⟨prep ++ C.gates.map renGate, ren C.output⟩
theorem shifted_size (C : Circuit) : (shifted C).size = C.size + 2 := by
  simp [shifted, Circuit.size, prep] <;> omega

theorem shifted_monotone (C : Circuit) (h : Monotone2 C) : Monotone2 (shifted C) := by
  simp only [Monotone2, shifted, List.forall_mem_append, List.forall_mem_map]
  exact ⟨by simp [prep], fun g hg => by simpa [renGate] using h g hg⟩

theorem shifted_eval (C : Circuit) (x : V → Bool) :
    (shifted C).eval (List.ofFn x) = C.eval (source (lift x)) := by
  obtain ⟨-, -, hr⟩ := agree_fold C.gates _ _ (prep_agree x)
  change ((prep ++ C.gates.map renGate).foldl gstep (List.ofFn x)).getD (ren C.output) false = _
  rw [List.foldl_append]
  exact hr C.output

theorem star_tail_bound (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : V → Bool, C.eval (source x) = true ↔ full x) : 16 ≤ C.size := by
  by_contra! h
  apply PEqualNP.Outside.L_meta_9785_aux.g10_lb_18 (shifted C) (shifted_monotone C hm)
  · intro x
    rw [shifted_eval]
    exact (hc (lift x)).trans (lift_correct x)
  · rw [shifted_size]
    omega

end L9736StarCut

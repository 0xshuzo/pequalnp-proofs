import PEqualNP.Outside.L_meta_971
namespace Bridge9731
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_971_aux

def subEdges : List (ℕ × ℕ) := [(0, 7), (0, 11), (1, 6), (1, 10), (1, 11), (2, 9), (2, 10), (3, 8), (3, 9), (3, 11), (4, 7), (4, 8), (4, 10), (5, 6), (5, 7), (5, 9)]

def ren (w : ℕ) : ℕ := ([0, 1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 7] : List ℕ).getD w (w + 7)

theorem ren_lt : ∀ i : Fin 12, ren i.val < 14 := by decide

theorem ren_ge {w : ℕ} (h : 12 ≤ w) : ren w = w + 7 := List.getD_eq_default _ _ h

-- The embedding of the step's graph into the Heawood graph.
def emb (i : Fin 12) : Fin 14 := ⟨ren i.val, ren_lt i⟩

-- The missing stars, as a function of a Heawood input.
def stars (y : Fin 14 → Bool) : Bool :=
  y 6 && (y 8 || y 9 || y 11) || (y 0 || y 2) && y 8

-- The embedding maps edges to Heawood edges, and the other Heawood edges are the two stars.
theorem emb_edge : ∀ a b : Fin 12, (a.val, b.val) ∈ subEdges →
    ((emb a).val, (emb b).val) ∈ edgeList := by
  decide +kernel

theorem edge_cases : ∀ u v : Fin 14, (u.val, v.val) ∈ edgeList →
    (∃ a b : Fin 12, (a.val, b.val) ∈ subEdges ∧ emb a = u ∧ emb b = v) ∨
      u = 6 ∧ (v = 8 ∨ v = 9 ∨ v = 11) ∨ (u = 0 ∨ u = 2) ∧ v = 8 := by
  decide +kernel

theorem heawood_split (y : Fin 14 → Bool) : HeawoodEdge y ↔
    (∃ u v : Fin 12, (u.val, v.val) ∈ subEdges ∧ y (emb u) = true ∧ y (emb v) = true) ∨
      stars y = true := by
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases edge_cases u v h with ⟨a, b, hab, rfl, rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ |
      ⟨rfl | rfl, rfl⟩
    · exact Or.inl ⟨a, b, hab, hu, hv⟩
    all_goals simp [stars, hu, hv]
  · rintro (⟨a, b, hab, ha, hb⟩ | h)
    · exact ⟨_, _, emb_edge a b hab, ha, hb⟩
    · simp only [stars, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hp, (h | h) | h⟩ | ⟨hp | hp, h⟩ <;> exact ⟨_, _, by decide, hp, h⟩

-- One evaluation step of the official model: `C.wires x` is `C.gates.foldl gstep x`.
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
  w'.length = w.length + 7 ∧ 12 ≤ w.length ∧ ∀ i, w'.getD (ren i) false = w.getD i false

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
        by_cases h : i < 12
        · exact (ren_lt ⟨i, h⟩).trans_le (by omega)
        · rw [ren_ge (by omega)]; omega
      rw [gstep_getD_lt _ _ hi', gstep_getD_lt _ _ hi, hr]
    · rw [ren_ge h12, ← hl, gstep_getD_last, gstep_getD_last]
      simp only [renGate, List.map_map, Function.comp_def, hr]
    · rw [ren_ge (by omega), getD_ge _ _ (by rw [gstep_length]; omega),
        getD_ge _ _ (by rw [gstep_length]; omega)]

-- Five gates compute the missing stars on wires 16 and 18.
def starGates : List Gate :=
  [⟨.or, [8, 9]⟩, ⟨.or, [14, 11]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [17, 8]⟩]

-- The wires of the star gates on a Heawood input.
def starWires (y : Fin 14 → Bool) : List Bool := starGates.foldl gstep (List.ofFn y)

theorem starWires_length (y : Fin 14 → Bool) : (starWires y).length = 19 := by
  rw [starWires, fold_length, List.length_ofFn]; rfl

theorem starWires_out (y : Fin 14 → Bool) :
    ((starWires y).getD 16 false || (starWires y).getD 18 false) = stars y := by
  simp [starWires, starGates, gstep, GateOp.eval, stars]

-- They carry the input of the step's graph that `y` restricts to.
theorem starWires_agree (y : Fin 14 → Bool) :
    Agree (List.ofFn fun i => y (emb i)) (starWires y) := by
  refine ⟨by rw [starWires_length, List.length_ofFn], by rw [List.length_ofFn], fun i => ?_⟩
  by_cases h : i < 12
  · rw [starWires, fold_getD_lt _ _ _ (by rw [List.length_ofFn]; exact ren_lt ⟨i, h⟩),
      getD_ofFn _ _ (ren_lt ⟨i, h⟩), getD_ofFn _ _ h]
    rfl
  · rw [ren_ge (by omega), getD_ge _ _ (by rw [starWires_length]; omega),
      getD_ge _ _ (by rw [List.length_ofFn]; omega)]

-- Re-adding the stars: the star gates, the renamed gates of `C`, and two OR gates that join
-- the output of `C` with the two stars. Seven gates more than `C`.
def addStars (C : Circuit) : Circuit :=
  ⟨starGates ++ C.gates.map renGate ++
    [⟨.or, [ren C.output, 16]⟩, ⟨.or, [C.size + 19, 18]⟩], C.size + 20⟩

theorem addStars_size (C : Circuit) : (addStars C).size = C.size + 7 := by
  simp [addStars, Circuit.size, starGates]

theorem addStars_monotone {C : Circuit} (h : Monotone2 C) : Monotone2 (addStars C) := by
  simp only [Monotone2, addStars, List.forall_mem_append, List.forall_mem_map]
  exact ⟨⟨by simp [starGates], fun g hg => by simpa [renGate] using h g hg⟩, by simp⟩

-- On a Heawood input, `addStars C` is `C` on the restricted input, or one of the two stars.
theorem addStars_eval (C : Circuit) (y : Fin 14 → Bool) :
    (addStars C).eval (List.ofFn y) = (C.eval (List.ofFn fun i => y (emb i)) || stars y) := by
  obtain ⟨hl, -, hr⟩ := agree_fold C.gates _ _ (starWires_agree y)
  have hs := starWires_length y
  have hl' : ((C.gates.map renGate).foldl gstep (starWires y)).length = C.size + 19 := by
    rw [hl, fold_length, List.length_ofFn, Circuit.size]; omega
  show ((starGates ++ C.gates.map renGate ++ _).foldl gstep (List.ofFn y)).getD
    (C.size + 19 + 1) false = _
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    ← starWires, ← hl', ← gstep_length _ ⟨.or, [ren C.output, 16]⟩, gstep_or, gstep_or,
    gstep_getD_lt _ _ (by omega), hr, fold_getD_lt _ (starWires y) 16 (by omega),
    fold_getD_lt _ (starWires y) 18 (by omega), Bool.or_assoc, starWires_out]
  rfl

-- No monotone circuit with at most 19 gates computes the edge function of the step's graph:
-- with the stars re-added it would be a Heawood circuit with at most 26 gates.
theorem sub_no_circuit (C : Circuit) (hmono : Monotone2 C) (hsize : C.size ≤ 19)
    (hC : ∀ x : Fin 12 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 12, (u.val, v.val) ∈ subEdges ∧ x u = true ∧ x v = true) : False := by
  have h := heawood_lb_27 (addStars C) (addStars_monotone hmono)
    (fun y => by rw [addStars_eval, Bool.or_eq_true, hC, heawood_split])
  rw [addStars_size] at h
  omega

end Bridge9731

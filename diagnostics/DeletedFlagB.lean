import PEqualNP.Defs

namespace DeletedFlag9764
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def smallF (x : Fin 41 → Bool) := (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 0 && x 40) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 3 && x 40) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 13 && x 40) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 15 && x 40) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39) || (x 20 && x 24) || (x 20 && x 26) || (x 20 && x 36) || (x 20 && x 39) || (x 20 && x 40)
def flagF (x : Fin 42 → Bool) := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)

def raw (i : Fin 41) : Fin 42 :=
  ⟨if i.val < 21 then i.val else i.val + 1, by split <;> omega⟩
def proj (x : Fin 42 → Bool) (i : Fin 41) := x (raw i)
def star (x : Fin 42 → Bool) := (((x 1 || x 4) || x 14) || x 16) && x 21

theorem graph_split (x : Fin 42 → Bool) : (smallF (proj x) || star x) = flagF x := by
  change (((x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) || ((((x 1 || x 4) || x 14) || x 16) && x 21)) = _
  unfold flagF
  simp only [Bool.and_or_distrib_right]
  ac_rfl

def ren (i : Nat) := if i < 21 then i else if i < 41 then i + 1 else i + 5
theorem ren_lt : ∀ i : Fin 41, ren i.val < 46 := by decide +kernel
theorem ren_ge {w : Nat} (h : 41 ≤ w) : ren w = w + 5 := by
  simp [ren, show ¬ w < 21 by omega, show ¬ w < 41 by omega]
theorem ren_raw (i : Fin 41) : ren i.val = (raw i).val := by
  simp [ren, raw, i.isLt]

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
  w'.length = w.length + 5 ∧ 41 ≤ w.length ∧ ∀ i, w'.getD (ren i) false = w.getD i false

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
        by_cases h : i < 41
        · exact (ren_lt ⟨i, h⟩).trans_le (by omega)
        · rw [ren_ge (by omega)]; omega
      rw [gstep_getD_lt _ _ hi', gstep_getD_lt _ _ hi, hr]
    · rw [ren_ge h12, ← hl, gstep_getD_last, gstep_getD_last]
      simp only [renGate, List.map_map, Function.comp_def, hr]
    · rw [ren_ge (by omega), getD_ge _ _ (by rw [gstep_length]; omega),
        getD_ge _ _ (by rw [gstep_length]; omega)]



def prep : List Gate := [⟨.or,[1,4]⟩,⟨.or,[42,14]⟩,⟨.or,[43,16]⟩,⟨.and,[44,21]⟩]
def prepared (x : Fin 42 → Bool) := prep.foldl gstep (List.ofFn x)
theorem prepared_length (x : Fin 42 → Bool) : (prepared x).length = 46 := by
  rw [prepared,fold_length,List.length_ofFn]; rfl
theorem prepared_star (x : Fin 42 → Bool) : (prepared x).getD 45 false = star x := by
  change ((((x 1 || (x 4 || false)) || (x 14 || false)) ||
    (x 16 || false)) && (x 21 && true)) = _
  simp [star]

theorem prepared_agree (x : Fin 42 → Bool) : Agree (List.ofFn (proj x)) (prepared x) := by
  refine ⟨by rw [prepared_length,List.length_ofFn], by rw [List.length_ofFn], fun i => ?_⟩
  by_cases hi : i < 41
  · let j : Fin 41 := ⟨i,hi⟩
    change (prep.foldl gstep (List.ofFn x)).getD (ren j.val) false = _
    rw [ren_raw,fold_getD_lt _ _ _ (by rw [List.length_ofFn]; exact (raw j).isLt),
      getD_ofFn _ _ (raw j).isLt, getD_ofFn _ _ hi]
    rfl
  · rw [ren_ge (by omega), getD_ge _ _ (by rw [prepared_length]; omega),
      getD_ge _ _ (by rw [List.length_ofFn]; omega)]

def lastGate (C : Circuit) : Gate := ⟨.or,[ren C.output,45]⟩
def grow (C : Circuit) : Circuit := ⟨(prep ++ C.gates.map renGate) ++ [lastGate C],46+C.size⟩
theorem grow_size (C : Circuit) : (grow C).size = C.size+5 := by
  simp [grow,Circuit.size,prep] <;> omega
theorem grow_legal (C : Circuit) (h : FanInTwo C) : FanInTwo (grow C) := by
  intro g hg
  rcases List.mem_append.mp hg with h1 | h2
  · rcases List.mem_append.mp h1 with hp | hm
    · simp only [prep,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
      simpa [renGate] using h f hf
  · have eq : g = lastGate C := by simpa using h2
    subst g; simp [lastGate]

theorem grow_eval (C : Circuit) (x : Fin 42 → Bool) :
    (grow C).eval (List.ofFn x) = (C.eval (List.ofFn (proj x)) || star x) := by
  let W := (C.gates.map renGate).foldl gstep (prepared x)
  have hw : W.length = 46+C.size := by
    simp [W,fold_length,prepared_length,Circuit.size]
  obtain ⟨_,_,hr⟩ := agree_fold C.gates _ _ (prepared_agree x)
  have old : W.getD (ren C.output) false = C.eval (List.ofFn (proj x)) := hr _
  have hs : W.getD 45 false = star x := by
    rw [show W = (C.gates.map renGate).foldl gstep (prepared x) by rfl,
      fold_getD_lt _ _ _ (by rw [prepared_length]; decide),prepared_star]
  change (((prep ++ C.gates.map renGate) ++ [lastGate C]).foldl gstep (List.ofFn x)).getD (46+C.size) false = _
  rw [List.foldl_append,List.foldl_append]
  change (gstep W ⟨.or,[ren C.output,45]⟩).getD (46+C.size) false = _
  rw [←hw,gstep_or,old,hs]

theorem extend_bound {s : Nat} (h : HasCircuitSize 41 smallF s) : HasCircuitSize 42 flagF (s+5) := by
  obtain ⟨C,hf,hs,hc⟩ := h
  exact ⟨grow C,grow_legal C hf,by rw [grow_size]; omega,fun x => by rw [grow_eval,hc,graph_split]⟩

theorem positive_transfer (h : PEqualNP.MetaComplexity.HasCircuitSize 41 (fun x : Fin 41 → Bool => (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 0 && x 40) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 3 && x 40) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 13 && x 40) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 15 && x 40) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39) || (x 20 && x 24) || (x 20 && x 26) || (x 20 && x 36) || (x 20 && x 39) || (x 20 && x 40)) 118) :
    PEqualNP.MetaComplexity.HasCircuitSize 42 (fun x : Fin 42 → Bool => (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) 123 := extend_bound h

theorem negative_transfer (h : ¬ (PEqualNP.MetaComplexity.HasCircuitSize 42 (fun x : Fin 42 → Bool => (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) 123)) :
    ¬ (PEqualNP.MetaComplexity.HasCircuitSize 41 (fun x : Fin 41 → Bool => (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 0 && x 40) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 3 && x 40) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 13 && x 40) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 15 && x 40) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39) || (x 20 && x 24) || (x 20 && x 26) || (x 20 && x 36) || (x 20 && x 39) || (x 20 && x 40)) 118) := fun h₀ => h (positive_transfer h₀)

theorem conditional_lower (larger : ∀ s, HasCircuitSize 42 flagF s → 62 ≤ s)
    (s : Nat) (hs : HasCircuitSize 41 smallF s) : 57 ≤ s := by
  have h := larger (s+5) (extend_bound hs)
  omega

end DeletedFlag9764

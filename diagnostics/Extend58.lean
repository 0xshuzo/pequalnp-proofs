import PEqualNP.Defs

namespace L9791Extend
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def raw (i : Fin 24) : Fin 25 :=
  ⟨if i.val < 13 then i.val else i.val + 1, by split <;> omega⟩
def proj (x : Fin 25 → Bool) (i : Fin 24) := x (raw i)
def star (x : Fin 25 → Bool) := (((x 1 || x 2) || x 4) || x 10) && x 13

def ren (i : Nat) := if i < 13 then i else if i < 24 then i + 1 else i + 5
theorem ren_lt : ∀ i : Fin 24, ren i.val < 29 := by decide +kernel
theorem ren_ge {w : Nat} (h : 24 ≤ w) : ren w = w + 5 := by
  simp [ren, show ¬ w < 13 by omega, show ¬ w < 24 by omega]
theorem ren_raw (i : Fin 24) : ren i.val = (raw i).val := by
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
  w'.length = w.length + 5 ∧ 24 ≤ w.length ∧ ∀ i, w'.getD (ren i) false = w.getD i false

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
        by_cases h : i < 24
        · exact (ren_lt ⟨i, h⟩).trans_le (by omega)
        · rw [ren_ge (by omega)]; omega
      rw [gstep_getD_lt _ _ hi', gstep_getD_lt _ _ hi, hr]
    · rw [ren_ge h12, ← hl, gstep_getD_last, gstep_getD_last]
      simp only [renGate, List.map_map, Function.comp_def, hr]
    · rw [ren_ge (by omega), getD_ge _ _ (by rw [gstep_length]; omega),
        getD_ge _ _ (by rw [gstep_length]; omega)]



def prep : List Gate := [⟨.or,[1,2]⟩,⟨.or,[25,4]⟩,⟨.or,[26,10]⟩,⟨.and,[27,13]⟩]
def prepared (x : Fin 25 → Bool) := prep.foldl gstep (List.ofFn x)
theorem prepared_length (x : Fin 25 → Bool) : (prepared x).length = 29 := by
  rw [prepared,fold_length,List.length_ofFn]; rfl
theorem prepared_star (x : Fin 25 → Bool) : (prepared x).getD 28 false = star x := by
  change ((((x 1 || (x 2 || false)) || (x 4 || false)) || (x 10 || false)) && (x 13 && true)) = _
  simp [star]

theorem prepared_agree (x : Fin 25 → Bool) : Agree (List.ofFn (proj x)) (prepared x) := by
  refine ⟨by rw [prepared_length,List.length_ofFn], by rw [List.length_ofFn], fun i => ?_⟩
  by_cases hi : i < 24
  · let j : Fin 24 := ⟨i,hi⟩
    change (prep.foldl gstep (List.ofFn x)).getD (ren j.val) false = _
    rw [ren_raw,fold_getD_lt _ _ _ (by rw [List.length_ofFn]; exact (raw j).isLt),
      getD_ofFn _ _ (raw j).isLt, getD_ofFn _ _ hi]
    rfl
  · rw [ren_ge (by omega), getD_ge _ _ (by rw [prepared_length]; omega),
      getD_ge _ _ (by rw [List.length_ofFn]; omega)]

def lastGate (C : Circuit) : Gate := ⟨.or,[ren C.output,28]⟩
def grow (C : Circuit) : Circuit := ⟨(prep ++ C.gates.map renGate) ++ [lastGate C],29+C.size⟩
theorem grow_size (C : Circuit) : (grow C).size = C.size+5 := by
  simp [grow,Circuit.size,prep] <;> omega
theorem grow_legal (C : Circuit) (h : Monotone2 C) : Monotone2 (grow C) := by
  intro g hg
  rcases List.mem_append.mp hg with h1 | h2
  · rcases List.mem_append.mp h1 with hp | hm
    · simp only [prep,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hm
      simpa [renGate] using h f hf
  · have eq : g = lastGate C := by simpa using h2
    subst g; simp [lastGate]

theorem grow_eval (C : Circuit) (x : Fin 25 → Bool) :
    (grow C).eval (List.ofFn x) = (C.eval (List.ofFn (proj x)) || star x) := by
  let W := (C.gates.map renGate).foldl gstep (prepared x)
  have hw : W.length = 29+C.size := by
    simp [W,fold_length,prepared_length,Circuit.size]
  obtain ⟨_,_,hr⟩ := agree_fold C.gates _ _ (prepared_agree x)
  have old : W.getD (ren C.output) false = C.eval (List.ofFn (proj x)) := hr _
  have hs : W.getD 28 false = star x := by
    rw [show W = (C.gates.map renGate).foldl gstep (prepared x) by rfl,
      fold_getD_lt _ _ _ (by rw [prepared_length]; decide),prepared_star]
  change (((prep ++ C.gates.map renGate) ++ [lastGate C]).foldl gstep (List.ofFn x)).getD (29+C.size) false = _
  rw [List.foldl_append,List.foldl_append]
  change (gstep W ⟨.or,[ren C.output,28]⟩).getD (29+C.size) false = _
  rw [←hw,gstep_or,old,hs]


def smallEdges : List (Nat × Nat) := [(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)]
def largeEdges : List (Nat × Nat) := [(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)]

def drop (i : Fin 25) : Fin 24 :=
  ⟨if i.val < 13 then i.val else i.val - 1, by split <;> omega⟩

theorem restore : ∀ i : Fin 25, i ≠ 13 → raw (drop i) = i := by decide +kernel
theorem liftEdge : ∀ i j : Fin 24, (i.val,j.val) ∈ smallEdges →
    ((raw i).val,(raw j).val) ∈ largeEdges := by decide +kernel
theorem splitEdge : ∀ i j : Fin 25, (i.val,j.val) ∈ largeEdges →
    (i≠13 ∧ j≠13 ∧ ((drop i).val,(drop j).val) ∈ smallEdges) ∨
    ((i=1 ∨ i=2 ∨ i=4 ∨ i=10) ∧ j=13) := by decide +kernel

theorem transfer {s : Nat} (C : Circuit) (mc : Monotone2 C) (size : C.size ≤ s)
    (ok : ∀ x : Fin 24 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ a b : Fin 24, (a.val,b.val) ∈ smallEdges ∧ x a=true ∧ x b=true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s+5 ∧
      (∀ x : Fin 25 → Bool, D.eval (List.ofFn x) = true ↔
       ∃ a b : Fin 25, (a.val,b.val) ∈ largeEdges ∧ x a=true ∧ x b=true) := by
  refine ⟨grow C,grow_legal C mc,by rw [grow_size]; omega,?_⟩
  intro x
  rw [grow_eval,Bool.or_eq_true,ok]
  simp only [star,Bool.and_eq_true,Bool.or_eq_true]
  constructor
  · rintro (⟨i,j,ij,hi,hj⟩ | ⟨hh,h13⟩)
    · exact ⟨raw i,raw j,liftEdge i j ij,hi,hj⟩
    · rcases hh with ((h1|h2)|h4)|h10
      · exact ⟨1,13,by decide,h1,h13⟩
      · exact ⟨2,13,by decide,h2,h13⟩
      · exact ⟨4,13,by decide,h4,h13⟩
      · exact ⟨10,13,by decide,h10,h13⟩
  · rintro ⟨i,j,ij,hi,hj⟩
    rcases splitEdge i j ij with ⟨ni,nj,hmem⟩ | ⟨h,j13⟩
    · refine Or.inl ⟨drop i,drop j,hmem,?_,?_⟩
      · simpa [proj,restore i ni] using hi
      · simpa [proj,restore j nj] using hj
    · subst j
      right
      refine ⟨?_,hj⟩
      rcases h with rfl|rfl|rfl|rfl <;> tauto

theorem positive_transfer (hyp : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 53 ∧ (∀ x : Fin 24 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 24, (u.val, v.val) ∈ ([(0, 15), (0, 21), (0, 23), (1, 16), (1, 22), (2, 13), (2, 17), (2, 23), (3, 13), (3, 14), (3, 18), (4, 14), (4, 15), (4, 19), (5, 13), (5, 15), (5, 16), (5, 20), (6, 14), (6, 16), (6, 17), (6, 21), (7, 15), (7, 17), (7, 18), (7, 22), (8, 16), (8, 18), (8, 19), (8, 23), (9, 17), (9, 19), (9, 20), (10, 18), (10, 20), (10, 21), (11, 13), (11, 19), (11, 21), (11, 22), (12, 14), (12, 20), (12, 22), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true))) : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 58 ∧ (∀ x : Fin 25 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 25, (u.val, v.val) ∈ ([(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14), (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16), (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18), (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20), (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22), (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨C,mc,hs,ok⟩ := hyp
  exact transfer C mc hs ok
end L9791Extend

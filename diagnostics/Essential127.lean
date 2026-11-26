import PEqualNP.Defs

namespace Essential9768
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- DNF reflection from the published L2428.
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wstep_len (w : List Bool) (g : Gate) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wstep_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD, List.getElem?_append_left hi]

lemma wstep_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (wstep w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [wstep, List.getD]

lemma tsnoc_lt (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i < T.length) :
    (T ++ [a]).getD i [] = T.getD i [] := by
  simp [List.getD, List.getElem?_append_left h]

lemma tsnoc_eq (T : List (List (List ℕ))) (a : List (List ℕ)) (i : ℕ) (h : i = T.length) :
    (T ++ [a]).getD i [] = a := by
  subst h
  simp [List.getD]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  first
  | rw [List.getElem_ofFn]
  | simp

def evalD (v : ℕ → Bool) (D : List (List ℕ)) : Bool := D.any fun c => c.all v

def prodD (D1 D2 : List (List ℕ)) : List (List ℕ) :=
  D1.flatMap fun c1 => D2.map fun c2 => c1 ++ c2

lemma evalD_append (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (D1 ++ D2) = (evalD v D1 || evalD v D2) := by
  unfold evalD
  rw [List.any_append]

lemma evalD_prod (v : ℕ → Bool) (D1 D2 : List (List ℕ)) :
    evalD v (prodD D1 D2) = (evalD v D1 && evalD v D2) := by
  rw [Bool.eq_iff_iff]
  simp only [evalD, prodD, List.any_eq_true, List.mem_flatMap, List.mem_map, Bool.and_eq_true,
    List.all_eq_true]
  constructor
  · rintro ⟨c, ⟨c1, h1, c2, h2, rfl⟩, hc⟩
    exact ⟨⟨c1, h1, fun i hi => hc i (List.mem_append_left _ hi)⟩,
      ⟨c2, h2, fun i hi => hc i (List.mem_append_right _ hi)⟩⟩
  · rintro ⟨⟨c1, h1, a1⟩, ⟨c2, h2, a2⟩⟩
    refine ⟨c1 ++ c2, ⟨c1, h1, c2, h2, rfl⟩, fun i hi => ?_⟩
    rcases List.mem_append.mp hi with h | h
    · exact a1 i h
    · exact a2 i h

def gD (T : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.and => (g.inputs.map fun i => T.getD i []).foldr prodD [[]]
  | _ => (g.inputs.map fun i => T.getD i []).foldr (fun a b => a ++ b) []

def okb (g : Gate) : Bool :=
  match g.op with
  | GateOp.and => decide (g.inputs.length ≤ 2)
  | GateOp.or => decide (g.inputs.length ≤ 2)
  | _ => false

def tstep (T : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) := T ++ [gD T g]

lemma all_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).all id
      = evalD v ((l.map fun i => T.getD i []).foldr prodD [[]]) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) && (l.map fun i => w.getD i false).all id)
      = evalD v (prodD (T.getD a []) ((l.map fun i => T.getD i []).foldr prodD [[]]))
    rw [evalD_prod, ← ih, h a]
    rfl

lemma any_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (l : List ℕ) :
    (l.map fun i => w.getD i false).any id
      = evalD v ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (id (w.getD a false) || (l.map fun i => w.getD i false).any id)
      = evalD v (T.getD a [] ++ ((l.map fun i => T.getD i []).foldr (fun a b => a ++ b) []))
    rw [evalD_append, ← ih, h a]
    rfl

lemma gD_spec (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ)))
    (h : ∀ i, w.getD i false = evalD v (T.getD i [])) (g : Gate) (hg : okb g = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = evalD v (gD T g) := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact all_spec v w T h ins
  | or => exact any_spec v w T h ins
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

lemma okb_spec (g : Gate) (hg : okb g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := g
  cases op with
  | and => exact ⟨Or.inl rfl, of_decide_eq_true hg⟩
  | or => exact ⟨Or.inr rfl, of_decide_eq_true hg⟩
  | not => exact absurd hg Bool.false_ne_true
  | mod m => exact absurd hg Bool.false_ne_true
  | maj => exact absurd hg Bool.false_ne_true

def Good (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) : Prop :=
  w.length = T.length ∧ ∀ i, w.getD i false = evalD v (T.getD i [])

lemma good_step (v : ℕ → Bool) (w : List Bool) (T : List (List (List ℕ))) (g : Gate)
    (hg : okb g = true) (h : Good v w T) : Good v (wstep w g) (tstep T g) := by
  obtain ⟨hl, hv⟩ := h
  refine ⟨?_, fun i => ?_⟩
  · show (wstep w g).length = (T ++ [gD T g]).length
    rw [wstep_len, List.length_append, List.length_singleton, hl]
  · show (wstep w g).getD i false = evalD v ((T ++ [gD T g]).getD i [])
    by_cases hlt : i < T.length
    · rw [tsnoc_lt T _ i hlt, wstep_lt _ _ _ (by rw [hl]; exact hlt)]
      exact hv i
    · by_cases heq : i = T.length
      · rw [tsnoc_eq T _ i heq, wstep_last _ _ _ (by rw [hl]; exact heq)]
        exact gD_spec v w T hv g hg
      · have h1 : (T ++ [gD T g]).getD i [] = [] :=
          List.getD_eq_default _ _ (by rw [List.length_append, List.length_singleton]; omega)
        have h2 : (wstep w g).getD i false = false :=
          List.getD_eq_default _ _ (by rw [wstep_len, hl]; omega)
        rw [h1, h2]
        rfl

lemma good_fold (v : ℕ → Bool) (gs : List Gate) (hg : ∀ g ∈ gs, okb g = true) :
    ∀ (w : List Bool) (T : List (List (List ℕ))), Good v w T →
      Good v (gs.foldl wstep w) (gs.foldl tstep T) := by
  induction gs with
  | nil =>
    intro w T h
    exact h
  | cons g gs ih =>
    intro w T h
    exact ih (fun g' hg' => hg g' (List.mem_cons.mpr (Or.inr hg'))) _ _
      (good_step v w T g (hg g (List.mem_cons.mpr (Or.inl rfl))) h)


def neg : Gate := ⟨.not, [0]⟩

def leaf (b : Bool) (i : Nat) : List (List Nat) :=
  if i = 0 then (if b then [[]] else [])
  else if i = 42 then (if b then [] else [[]]) else [[i]]

def ts (b : Bool) := (List.range 43).map (leaf b)

theorem table_len (b : Bool) : (ts b).length = 43 := by simp [ts]

theorem table_get : ∀ (b : Bool) (i : Nat), i < 43 → (ts b).getD i [] = leaf b i := by
  decide +kernel

def val (x : Fin 42 → Bool) (i : Nat) := x (Fin.ofNat 42 i)

theorem start_good (x : Fin 42 → Bool) :
    Good (val x) (wstep (List.ofFn x) neg) (ts (x 0)) := by
  refine ⟨by simp [wstep_len, table_len], fun i => ?_⟩
  by_cases hi : i < 42
  · rw [wstep_lt (List.ofFn x) neg i (by simpa using hi), ofFn_getD _ _ hi, table_get _ _ (by omega)]
    by_cases hz : i = 0
    · subst i
      cases hv : x 0 <;> simp [leaf, evalD, hv]
    · have h42 : i ≠ 42 := by omega
      simp only [leaf, if_neg hz, if_neg h42, evalD, List.any_cons, List.all_cons,
        List.all_nil, List.any_nil, Bool.and_true, Bool.or_false]
      exact congrArg x (Fin.ext (Nat.mod_eq_of_lt hi).symm)
  · by_cases hl : i = 42
    · subst i
      rw [wstep_last (List.ofFn x) neg 42 (by simp), table_get _ _ (by decide)]
      have h0 : (List.ofFn x).getD 0 false = x 0 := ofFn_getD _ _ (by decide)
      cases hv : x 0 <;> simp [neg, GateOp.eval, leaf, evalD, h0, hv]
    · have hw : (wstep (List.ofFn x) neg).getD i false = false :=
        List.getD_eq_default _ _ (by simp [wstep_len]; omega)
      have ht : (ts (x 0)).getD i [] = [] := List.getD_eq_default _ _ (by rw [table_len]; omega)
      rw [hw, ht]
      rfl

def refines (A B : List (List Nat)) : Bool :=
  A.all fun a => B.any fun b => b.all fun k => a.contains k

theorem refinement (v : Nat → Bool) {A B : List (List Nat)} (h : refines A B = true)
    (hA : evalD v A = true) : evalD v B = true := by
  obtain ⟨a, ha, hv⟩ := List.any_eq_true.mp hA
  obtain ⟨b, hb, hk⟩ := List.any_eq_true.mp ((List.all_eq_true.mp h) a ha)
  apply List.any_eq_true.mpr
  refine ⟨b, hb, List.all_eq_true.mpr (fun k hkb => ?_)⟩
  exact (List.all_eq_true.mp hv) k (by simpa using (List.all_eq_true.mp hk) k hkb)

def agree (A B : List (List Nat)) := refines A B && refines B A

theorem agreement (v : Nat → Bool) {A B : List (List Nat)} (h : agree A B = true) :
    evalD v A = evalD v B := by
  have hh : refines A B = true ∧ refines B A = true := by simpa [agree] using h
  rw [Bool.eq_iff_iff]
  exact ⟨refinement v hh.1, refinement v hh.2⟩

def tail : List Gate := [⟨.or, [27,39]⟩,⟨.or, [22,32]⟩,⟨.or, [22,34]⟩,⟨.or, [34,41]⟩,⟨.or, [21,36]⟩,⟨.or, [35,36]⟩,⟨.or, [35,38]⟩,⟨.or, [27,35]⟩,⟨.or, [25,31]⟩,⟨.or, [22,33]⟩,⟨.or, [33,39]⟩,⟨.or, [38,45]⟩,⟨.or, [25,49]⟩,⟨.or, [25,30]⟩,⟨.or, [41,48]⟩,⟨.or, [44,57]⟩,⟨.or, [26,52]⟩,⟨.or, [23,39]⟩,⟨.or, [28,50]⟩,⟨.or, [46,53]⟩,⟨.or, [30,31]⟩,⟨.or, [26,34]⟩,⟨.or, [24,33]⟩,⟨.or, [29,37]⟩,⟨.or, [24,54]⟩,⟨.or, [55,60]⟩,⟨.and, [15,58]⟩,⟨.or, [24,40]⟩,⟨.or, [23,24]⟩,⟨.or, [23,32]⟩,⟨.or, [32,39]⟩,⟨.or, [61,65]⟩,⟨.or, [28,37]⟩,⟨.or, [34,40]⟩,⟨.or, [40,41]⟩,⟨.or, [64,72]⟩,⟨.or, [25,77]⟩,⟨.or, [51,59]⟩,⟨.or, [27,63]⟩,⟨.or, [26,35]⟩,⟨.or, [26,70]⟩,⟨.and, [5,80]⟩,⟨.and, [7,74]⟩,⟨.or, [41,71]⟩,⟨.or, [30,62]⟩,⟨.or, [38,81]⟩,⟨.or, [27,37]⟩,⟨.or, [29,43]⟩,⟨.or, [28,29]⟩,⟨.or, [31,76]⟩,⟨.and, [18,68]⟩,⟨.or, [30,82]⟩,⟨.or, [21,56]⟩,⟨.or, [25,34]⟩,⟨.or, [36,96]⟩,⟨.or, [33,47]⟩,⟨.or, [37,67]⟩,⟨.or, [31,73]⟩,⟨.or, [21,92]⟩,⟨.or, [31,86]⟩,⟨.or, [79,89]⟩,⟨.and, [17,99]⟩,⟨.or, [35,101]⟩,⟨.and, [38,42]⟩,⟨.or, [24,95]⟩,⟨.or, [41,42]⟩,⟨.or, [75,100]⟩,⟨.or, [26,108]⟩,⟨.or, [40,106]⟩,⟨.or, [23,98]⟩,⟨.or, [37,112]⟩,⟨.or, [22,28]⟩,⟨.and, [14,105]⟩,⟨.and, [16,113]⟩,⟨.or, [36,88]⟩,⟨.or, [22,90]⟩,⟨.or, [30,40]⟩,⟨.and, [11,109]⟩,⟨.or, [38,110]⟩,⟨.or, [32,107]⟩,⟨.and, [10,117]⟩,⟨.or, [21,118]⟩,⟨.or, [29,102]⟩,⟨.or, [36,83]⟩,⟨.and, [20,103]⟩,⟨.or, [28,121]⟩,⟨.and, [4,122]⟩,⟨.or, [116,123]⟩,⟨.or, [84,129]⟩,⟨.or, [23,114]⟩,⟨.or, [27,78]⟩,⟨.and, [6,133]⟩,⟨.or, [66,94]⟩,⟨.or, [119,132]⟩,⟨.or, [115,131]⟩,⟨.or, [91,97]⟩,⟨.and, [8,138]⟩,⟨.and, [2,136]⟩,⟨.or, [85,139]⟩,⟨.and, [13,87]⟩,⟨.and, [3,125]⟩,⟨.or, [39,126]⟩,⟨.or, [104,143]⟩,⟨.and, [0,128]⟩,⟨.or, [134,142]⟩,⟨.or, [93,146]⟩,⟨.and, [19,144]⟩,⟨.and, [9,135]⟩,⟨.and, [1,124]⟩,⟨.or, [137,150]⟩,⟨.or, [120,127]⟩,⟨.or, [29,111]⟩,⟨.or, [32,154]⟩,⟨.or, [130,152]⟩,⟨.or, [147,153]⟩,⟨.or, [33,155]⟩,⟨.or, [69,157]⟩,⟨.or, [145,156]⟩,⟨.or, [141,160]⟩,⟨.and, [12,158]⟩,⟨.or, [140,162]⟩,⟨.or, [151,163]⟩,⟨.or, [149,164]⟩,⟨.or, [161,165]⟩,⟨.or, [159,166]⟩,⟨.or, [148,167]⟩]
def C : Circuit := ⟨neg :: tail, 168⟩
def edges : List (Nat × Nat) := [(0,26),(0,28),(0,38),(0,41),(1,21),(1,22),(1,27),(1,29),(1,39),(2,22),(2,23),(2,28),(2,30),(2,40),(3,23),(3,24),(3,29),(3,31),(3,41),(4,21),(4,24),(4,25),(4,30),(4,32),(5,22),(5,25),(5,26),(5,31),(5,33),(6,23),(6,26),(6,27),(6,32),(6,34),(7,24),(7,27),(7,28),(7,33),(7,35),(8,25),(8,28),(8,29),(8,34),(8,36),(9,26),(9,29),(9,30),(9,35),(9,37),(10,27),(10,30),(10,31),(10,36),(10,38),(11,28),(11,31),(11,32),(11,37),(11,39),(12,29),(12,32),(12,33),(12,38),(12,40),(13,30),(13,33),(13,34),(13,39),(13,41),(14,21),(14,31),(14,34),(14,35),(14,40),(15,22),(15,32),(15,35),(15,36),(15,41),(16,21),(16,23),(16,33),(16,36),(16,37),(17,22),(17,24),(17,34),(17,37),(17,38),(18,23),(18,25),(18,35),(18,38),(18,39),(19,24),(19,26),(19,36),(19,39),(19,40),(20,25),(20,27),(20,37),(20,40),(20,41)]

def represented (b : Bool) := (tail.foldl tstep (ts b)).getD C.output []
def expected (b : Bool) := edges.flatMap fun e => prodD (leaf b e.1) (leaf b e.2)

theorem same_terms : ∀ b : Bool, agree (represented b) (expected b) = true := by decide +kernel

theorem reflection (x : Fin 42 → Bool) :
    C.eval (List.ofFn x) = evalD (val x) (expected (x 0)) := by
  have ok : ∀ g ∈ tail, okb g = true := by decide +kernel
  have h := (good_fold _ tail ok _ _ (start_good x)).2 C.output
  exact h.trans (agreement _ (same_terms _))

theorem eval_flat {α : Type} (v : Nat → Bool) (l : List α) (f : α → List (List Nat)) :
    evalD v (l.flatMap f) = l.any (fun e => evalD v (f e)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, evalD_append, ih, List.any_cons]

theorem leaf_val (x : Fin 42 → Bool) (i : Nat) (hi : i < 42) :
    evalD (val x) (leaf (x 0) i) = val x i := by
  by_cases hz : i = 0
  · subst i
    change evalD (val x) (leaf (x 0) 0) = x 0
    cases hv : x 0 <;> simp [leaf, evalD, hv]
  · have h42 : i ≠ 42 := by omega
    simp [leaf, hz, h42, evalD]

theorem eval_expected (x : Fin 42 → Bool) :
    evalD (val x) (expected (x 0)) = edges.any (fun e => val x e.1 && val x e.2) := by
  rw [expected, eval_flat]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have bounded : ∀ p ∈ edges, p.1 < 42 ∧ p.2 < 42 := by decide +kernel
  constructor <;> rintro ⟨e, he, hv⟩ <;> refine ⟨e, he, ?_⟩
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv

def target (x : Fin 42 → Bool) : Bool := (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)

theorem computes (x : Fin 42 → Bool) : C.eval (List.ofFn x) = target x := by
  rw [reflection, eval_expected]
  dsimp only [edges, List.any, val, target]
  simp only [Bool.or_false, Bool.or_assoc] <;> ac_rfl

def forced (b : Bool) : Circuit :=
  ⟨(if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩) :: tail, C.output⟩

def witness₀ (i : Fin 42) : Bool := [12,24,25,28,34,38,39,41].contains i.val
def witness₁ (i : Fin 42) : Bool := [0,1,11,16,24,25,34,35,40].contains i.val

theorem essential :
    (forced false).eval (List.ofFn witness₀) ≠ C.eval (List.ofFn witness₀) ∧
    (forced true).eval (List.ofFn witness₁) ≠ C.eval (List.ofFn witness₁) := by
  decide +kernel

theorem size : C.size = 127 := by decide +kernel

theorem admissible : FanInTwo C := by
  intro g hg
  change g ∈ neg :: tail at hg
  rcases List.mem_cons.mp hg with h | h
  · subst g
    exact ⟨Or.inr (Or.inr rfl), by decide⟩
  · have ok : ∀ g ∈ tail, okb g = true := by decide +kernel
    obtain ⟨hop, hn⟩ := okb_spec g (ok g h)
    refine ⟨?_, hn⟩
    rcases hop with h₁ | h₂
    · exact Or.inl h₁
    · exact Or.inr (Or.inl h₂)

theorem upper_essential : HasCircuitSize 42 target 127 :=
  ⟨C, admissible, by rw [size], computes⟩

end Essential9768

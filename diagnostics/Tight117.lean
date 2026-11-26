import PEqualNP.Defs

namespace Essential9838
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


def neg : Gate := ⟨.not, [27]⟩

def leaf (b : Bool) (i : Nat) : List (List Nat) :=
  if i = 27 then (if b then [[]] else [])
  else if i = 40 then (if b then [] else [[]]) else [[i]]

def ts (b : Bool) := (List.range 41).map (leaf b)

theorem table_len (b : Bool) : (ts b).length = 41 := by simp [ts]

theorem table_get : ∀ (b : Bool) (i : Nat), i < 41 → (ts b).getD i [] = leaf b i := by
  decide +kernel

def val (x : Fin 40 → Bool) (i : Nat) := x (Fin.ofNat 40 i)

theorem start_good (x : Fin 40 → Bool) :
    Good (val x) (wstep (List.ofFn x) neg) (ts (x 27)) := by
  refine ⟨by simp [wstep_len, table_len], fun i => ?_⟩
  by_cases hi : i < 40
  · rw [wstep_lt (List.ofFn x) neg i (by simpa using hi), ofFn_getD _ _ hi, table_get _ _ (by omega)]
    by_cases hz : i = 27
    · subst i
      cases hv : x 27 <;> simp [leaf, evalD, hv]
    · have h42 : i ≠ 40 := by omega
      simp only [leaf, if_neg hz, if_neg h42, evalD, List.any_cons, List.all_cons,
        List.all_nil, List.any_nil, Bool.and_true, Bool.or_false]
      exact congrArg x (Fin.ext (Nat.mod_eq_of_lt hi).symm)
  · by_cases hl : i = 40
    · subst i
      rw [wstep_last (List.ofFn x) neg 40 (by simp), table_get _ _ (by decide)]
      have h0 : (List.ofFn x).getD 27 false = x 27 := ofFn_getD _ _ (by decide)
      cases hv : x 27 <;> simp [neg, GateOp.eval, leaf, evalD, h0, hv]
    · have hw : (wstep (List.ofFn x) neg).getD i false = false :=
        List.getD_eq_default _ _ (by simp [wstep_len]; omega)
      have ht : (ts (x 27)).getD i [] = [] := List.getD_eq_default _ _ (by rw [table_len]; omega)
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

def tail : List Gate := [⟨.or,[4,18]⟩,⟨.or,[9,18]⟩,⟨.and,[8,40]⟩,⟨.or,[9,6]⟩,⟨.or,[0,13]⟩,⟨.or,[3,18]⟩,⟨.or,[5,12]⟩,⟨.or,[2,14]⟩,⟨.or,[16,43]⟩,⟨.or,[16,17]⟩,⟨.or,[19,10]⟩,⟨.or,[11,18]⟩,⟨.or,[11,14]⟩,⟨.or,[0,11]⟩,⟨.or,[9,50]⟩,⟨.or,[13,9]⟩,⟨.or,[5,19]⟩,⟨.or,[5,15]⟩,⟨.or,[5,10]⟩,⟨.or,[4,3]⟩,⟨.or,[11,55]⟩,⟨.or,[8,12]⟩,⟨.or,[1,52]⟩,⟨.or,[16,7]⟩,⟨.or,[13,47]⟩,⟨.or,[8,41]⟩,⟨.or,[1,58]⟩,⟨.or,[17,60]⟩,⟨.or,[3,62]⟩,⟨.or,[5,66]⟩,⟨.and,[36,61]⟩,⟨.or,[19,63]⟩,⟨.or,[15,49]⟩,⟨.or,[13,72]⟩,⟨.or,[15,45]⟩,⟨.or,[17,67]⟩,⟨.and,[38,74]⟩,⟨.or,[0,44]⟩,⟨.or,[3,53]⟩,⟨.or,[10,12]⟩,⟨.or,[6,46]⟩,⟨.or,[4,2]⟩,⟨.or,[19,68]⟩,⟨.or,[59,79]⟩,⟨.or,[9,1]⟩,⟨.or,[3,75]⟩,⟨.or,[2,7]⟩,⟨.or,[10,82]⟩,⟨.or,[18,80]⟩,⟨.or,[7,83]⟩,⟨.or,[8,87]⟩,⟨.and,[23,90]⟩,⟨.or,[17,89]⟩,⟨.or,[14,42]⟩,⟨.or,[14,6]⟩,⟨.or,[4,11]⟩,⟨.and,[30,84]⟩,⟨.and,[20,86]⟩,⟨.or,[1,6]⟩,⟨.and,[24,70]⟩,⟨.or,[51,73]⟩,⟨.or,[0,93]⟩,⟨.or,[2,76]⟩,⟨.or,[77,100]⟩,⟨.or,[7,99]⟩,⟨.and,[21,103]⟩,⟨.or,[10,105]⟩,⟨.or,[57,78]⟩,⟨.or,[16,81]⟩,⟨.or,[13,95]⟩,⟨.and,[37,102]⟩,⟨.or,[2,109]⟩,⟨.or,[19,48]⟩,⟨.or,[12,113]⟩,⟨.or,[17,110]⟩,⟨.or,[98,104]⟩,⟨.and,[22,112]⟩,⟨.and,[26,107]⟩,⟨.and,[39,114]⟩,⟨.or,[64,65]⟩,⟨.and,[35,101]⟩,⟨.or,[54,91]⟩,⟨.or,[43,115]⟩,⟨.or,[7,94]⟩,⟨.or,[56,88]⟩,⟨.and,[33,123]⟩,⟨.or,[15,124]⟩,⟨.or,[6,96]⟩,⟨.or,[15,128]⟩,⟨.or,[69,85]⟩,⟨.and,[34,127]⟩,⟨.and,[29,125]⟩,⟨.and,[32,120]⟩,⟨.and,[25,108]⟩,⟨.or,[40,122]⟩,⟨.or,[119,133]⟩,⟨.and,[27,135]⟩,⟨.or,[71,137]⟩,⟨.and,[28,130]⟩,⟨.or,[106,136]⟩,⟨.or,[117,132]⟩,⟨.or,[12,129]⟩,⟨.or,[121,141]⟩,⟨.or,[92,131]⟩,⟨.or,[97,139]⟩,⟨.or,[134,144]⟩,⟨.or,[118,143]⟩,⟨.or,[126,145]⟩,⟨.and,[31,142]⟩,⟨.or,[111,148]⟩,⟨.or,[149,150]⟩,⟨.or,[138,147]⟩,⟨.or,[146,151]⟩,⟨.or,[140,152]⟩,⟨.or,[153,154]⟩,⟨.or,[116,155]⟩]
def C : Circuit := ⟨neg :: tail,156⟩
def edges : List (Nat × Nat) := [(0,20),(0,25),(0,27),(0,37),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,20),(3,22),(3,23),(3,28),(3,30),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,20),(13,29),(13,32),(13,33),(13,38),(14,30),(14,33),(14,34),(14,39),(15,20),(15,21),(15,31),(15,34),(15,35),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39)]
def represented (b : Bool) := (tail.foldl tstep (ts b)).getD C.output []
def expected (b : Bool) := edges.flatMap fun e => prodD (leaf b e.1) (leaf b e.2)

theorem same_terms : ∀ b : Bool, agree (represented b) (expected b) = true := by decide +kernel

theorem reflection (x : Fin 40 → Bool) :
    C.eval (List.ofFn x) = evalD (val x) (expected (x 27)) := by
  have ok : ∀ g ∈ tail, okb g = true := by decide +kernel
  have h := (good_fold _ tail ok _ _ (start_good x)).2 C.output
  exact h.trans (agreement _ (same_terms _))

theorem eval_flat {α : Type} (v : Nat → Bool) (l : List α) (f : α → List (List Nat)) :
    evalD v (l.flatMap f) = l.any (fun e => evalD v (f e)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, evalD_append, ih, List.any_cons]

theorem leaf_val (x : Fin 40 → Bool) (i : Nat) (hi : i < 40) :
    evalD (val x) (leaf (x 27) i) = val x i := by
  by_cases hz : i = 27
  · subst i
    change evalD (val x) (leaf (x 27) 27) = x 27
    cases hv : x 27 <;> simp [leaf, evalD, hv]
  · have h42 : i ≠ 40 := by omega
    simp [leaf, hz, h42, evalD]

theorem eval_expected (x : Fin 40 → Bool) :
    evalD (val x) (expected (x 27)) = edges.any (fun e => val x e.1 && val x e.2) := by
  rw [expected, eval_flat]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have bounded : ∀ p ∈ edges, p.1 < 40 ∧ p.2 < 40 := by decide +kernel
  constructor <;> rintro ⟨e, he, hv⟩ <;> refine ⟨e, he, ?_⟩
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv

def target (x : Fin 40 → Bool) : Bool := (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)
theorem computes (x : Fin 40 → Bool) : C.eval (List.ofFn x) = target x := by
  rw [reflection, eval_expected]
  dsimp only [edges, List.any, val, target]
  simp only [Bool.or_false, Bool.or_assoc] <;> ac_rfl

def forced (b : Bool) : Circuit :=
  ⟨(if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩) :: tail, C.output⟩

def witness₀ (i : Fin 40) : Bool := [0, 4, 8, 19, 22, 26, 30, 33].contains i.val
def witness₁ (i : Fin 40) : Bool := [4, 21, 27, 28, 32, 39].contains i.val

theorem essential :
    (forced false).eval (List.ofFn witness₀) ≠ C.eval (List.ofFn witness₀) ∧
    (forced true).eval (List.ofFn witness₁) ≠ C.eval (List.ofFn witness₁) := by
  decide +kernel

theorem size : C.size = 117 := by decide +kernel

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

theorem upper_essential : HasCircuitSize 40 target 117 :=
  ⟨C, admissible, by rw [size], computes⟩

end Essential9838
namespace Prefix96
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def step (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def run (gs : List Gate) (w : List Bool) := gs.foldl step w
theorem run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    run (gs++[g]) w=step (run gs w) g := by simp [run,List.foldl_append]
theorem length_run (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [step,ih]; omega
theorem snoc_other (w : List Bool) (v : Bool) (q : Nat) (ne : q≠w.length) :
    (w++[v]).getD q false=w.getD q false := by
  by_cases h : q<w.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
theorem snoc_last (w : List Bool) (v : Bool) : (w++[v]).getD w.length false=v := by simp

def separates {k : Nat} (X Y : Fin k→List Bool) (T : Finset Nat) :=
  ∀ i,∃ t∈T,(X i).getD t false≠(Y i).getD t false

def useful (g : Gate) : List Nat :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def charge : GateOp → Nat
  | .not => 0
  | _ => 1

def mass (gs : List Gate) := (gs.map fun g => charge g.op).sum
def inverters (gs : List Gate) := (gs.map fun g => 1-charge g.op).sum

theorem mass_split (gs : List Gate) : mass gs + inverters gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have cap : charge g.op≤1 := by cases g.op <;> simp [charge]
    change charge g.op+mass gs+(1-charge g.op+inverters gs)=gs.length+1
    omega

theorem mass_snoc (gs : List Gate) (g : Gate) : mass (gs++[g])=mass gs+charge g.op := by
  simp [mass,List.sum_append]

theorem use_sound (g : Gate) (v : Nat→Bool) :
    g.op.eval (g.inputs.map v)=g.op.eval ((useful g).map v) := by
  rcases g with ⟨op,args⟩
  cases op <;> cases args <;> rfl

theorem use_count (g : Gate) (h : g.inputs.length≤2) : (useful g).length ≤ charge g.op+1 := by
  rcases g with ⟨op,args⟩
  cases op <;> simp_all [useful,charge]

theorem trace (k m : Nat) (X Y : Fin k→List Bool)
    (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (S : Finset Nat) (sep : separates (fun i=>run gs (X i)) (fun i=>run gs (Y i)) S) :
    ∃ T : Finset Nat,separates X Y T ∧ T.card≤S.card+mass gs := by
  classical
  induction gs using List.reverseRecOn generalizing S with
  | nil => exact ⟨S,sep,by simp [mass]⟩
  | append_singleton gs g ih =>
    let last := m+gs.length
    let V := fun i => run gs (X i)
    let W := fun i => run gs (Y i)
    have vl (i) : (V i).length=last := by rw [show V i=run gs (X i) by rfl,length_run,(lens i).1]
    have wl (i) : (W i).length=last := by rw [show W i=run gs (Y i) by rfl,length_run,(lens i).2]
    have stay (i : Fin k) (w : Nat) (ne : w≠last) :
        (run (gs++[g]) (X i)).getD w false ≠ (run (gs++[g]) (Y i)).getD w false →
          (V i).getD w false ≠ (W i).getD w false := by
      rw [run_snoc,run_snoc]
      change (V i++[_]).getD w false≠(W i++[_]).getD w false → _
      rw [snoc_other _ _ w (by rwa [vl]),snoc_other _ _ w (by rwa [wl])]
      exact id
    have old : ∀ a∈gs,a.inputs.length≤2 := fun a ha => fan a (by simp [ha])
    by_cases mem : last∈S
    · let R := S.erase last ∪ (useful g).toFinset
      have rsep : separates V W R := by
        intro i
        obtain ⟨w,ws,diff⟩ := sep i
        by_cases eq : w=last
        · subst w
          by_contra! blocked
          have same : (useful g).map (fun t => (V i).getD t false)=(useful g).map (fun t => (W i).getD t false) := by
            apply List.map_congr_left
            intro t ht
            exact blocked t (Finset.mem_union_right _ (List.mem_toFinset.mpr ht))
          change (run (gs++[g]) (X i)).getD last false≠(run (gs++[g]) (Y i)).getD last false at diff
          rw [run_snoc,run_snoc] at diff
          change (V i++[g.op.eval _]).getD last false≠(W i++[g.op.eval _]).getD last false at diff
          rw [←vl i,snoc_last,vl i,←wl i,snoc_last] at diff
          exact diff ((use_sound g _).trans ((congrArg g.op.eval same).trans (use_sound g _).symm))
        · exact ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ws⟩),stay i w eq diff⟩
      obtain ⟨T,st,card⟩ := ih old R rsep
      have maxfan := fan g (by simp)
      have usable := use_count g maxfan
      have len := List.toFinset_card_le (useful g)
      have union : R.card≤(S.erase last).card+(useful g).toFinset.card := Finset.card_union_le _ _
      have erase := Finset.card_erase_add_one mem
      exact ⟨T,st,by rw [mass_snoc]; omega⟩
    · have oldSep : separates V W S := by
        intro i
        obtain ⟨w,ws,h⟩ := sep i
        exact ⟨w,ws,stay i w (fun eq => mem (eq ▸ ws)) h⟩
      obtain ⟨T,st,card⟩ := ih old S oldSep
      exact ⟨T,st,by rw [mass_snoc]; omega⟩

theorem price {k m : Nat} (X Y : Fin k→List Bool) (lens : ∀ i,(X i).length=m ∧ (Y i).length=m)
    (unique : ∀ (w : Nat) (i j : Fin k),(X i).getD w false≠(Y i).getD w false →
       (X j).getD w false≠(Y j).getD w false → i=j)
    (gs : List Gate) (fan : ∀ g∈gs,g.inputs.length≤2)
    (root : Nat) (correct : ∀ i,(run gs (X i)).getD root false≠(run gs (Y i)).getD root false) :
    k≤mass gs+1 := by
  classical
  obtain ⟨T,sep,bound⟩ := trace k m X Y lens gs fan {root}
    (fun i=>⟨root,Finset.mem_singleton_self _,correct i⟩)
  let f := fun i => Classical.choose (sep i)
  have ok (i) := Classical.choose_spec (sep i)
  have cap : (Finset.univ : Finset (Fin k)).card≤T.card :=
    Finset.card_le_card_of_injOn f (fun i _ => (ok i).1) (fun i _ j _ eq =>
      unique (f j) i j (eq ▸ (ok i).2) (ok j).2)
  simp only [Finset.card_univ,Fintype.card_fin] at cap
  simp only [Finset.card_singleton] at bound
  omega
def target (x : Fin 40 → Bool) : Bool := (x 0 && x 20) || (x 0 && x 25) || (x 0 && x 27) || (x 0 && x 37) || (x 1 && x 21) || (x 1 && x 26) || (x 1 && x 28) || (x 1 && x 38) || (x 2 && x 21) || (x 2 && x 22) || (x 2 && x 27) || (x 2 && x 29) || (x 2 && x 39) || (x 3 && x 20) || (x 3 && x 22) || (x 3 && x 23) || (x 3 && x 28) || (x 3 && x 30) || (x 4 && x 23) || (x 4 && x 24) || (x 4 && x 29) || (x 4 && x 31) || (x 5 && x 21) || (x 5 && x 24) || (x 5 && x 25) || (x 5 && x 30) || (x 5 && x 32) || (x 6 && x 22) || (x 6 && x 25) || (x 6 && x 26) || (x 6 && x 31) || (x 6 && x 33) || (x 7 && x 23) || (x 7 && x 26) || (x 7 && x 27) || (x 7 && x 32) || (x 7 && x 34) || (x 8 && x 24) || (x 8 && x 27) || (x 8 && x 28) || (x 8 && x 33) || (x 8 && x 35) || (x 9 && x 25) || (x 9 && x 28) || (x 9 && x 29) || (x 9 && x 34) || (x 9 && x 36) || (x 10 && x 26) || (x 10 && x 29) || (x 10 && x 30) || (x 10 && x 35) || (x 10 && x 37) || (x 11 && x 27) || (x 11 && x 30) || (x 11 && x 31) || (x 11 && x 36) || (x 11 && x 38) || (x 12 && x 28) || (x 12 && x 31) || (x 12 && x 32) || (x 12 && x 37) || (x 12 && x 39) || (x 13 && x 20) || (x 13 && x 29) || (x 13 && x 32) || (x 13 && x 33) || (x 13 && x 38) || (x 14 && x 30) || (x 14 && x 33) || (x 14 && x 34) || (x 14 && x 39) || (x 15 && x 20) || (x 15 && x 21) || (x 15 && x 31) || (x 15 && x 34) || (x 15 && x 35) || (x 16 && x 22) || (x 16 && x 32) || (x 16 && x 35) || (x 16 && x 36) || (x 17 && x 21) || (x 17 && x 23) || (x 17 && x 33) || (x 17 && x 36) || (x 17 && x 37) || (x 18 && x 22) || (x 18 && x 24) || (x 18 && x 34) || (x 18 && x 37) || (x 18 && x 38) || (x 19 && x 23) || (x 19 && x 25) || (x 19 && x 35) || (x 19 && x 38) || (x 19 && x 39)
abbrev R := Fin 22
def pre : List Gate := [⟨.not,[27]⟩,⟨.or,[4,18]⟩,⟨.or,[9,18]⟩,⟨.and,[8,40]⟩,⟨.or,[9,6]⟩,⟨.or,[0,13]⟩,⟨.or,[3,18]⟩,⟨.or,[5,12]⟩,⟨.or,[2,14]⟩,⟨.or,[16,43]⟩,⟨.or,[16,17]⟩,⟨.or,[19,10]⟩,⟨.or,[11,18]⟩,⟨.or,[11,14]⟩,⟨.or,[0,11]⟩,⟨.or,[9,50]⟩,⟨.or,[13,9]⟩,⟨.or,[5,19]⟩,⟨.or,[5,15]⟩,⟨.or,[5,10]⟩,⟨.or,[4,3]⟩,⟨.or,[11,55]⟩,⟨.or,[8,12]⟩,⟨.or,[1,52]⟩,⟨.or,[16,7]⟩,⟨.or,[13,47]⟩,⟨.or,[8,41]⟩,⟨.or,[1,58]⟩,⟨.or,[17,60]⟩,⟨.or,[3,62]⟩,⟨.or,[5,66]⟩,⟨.and,[36,61]⟩,⟨.or,[19,63]⟩,⟨.or,[15,49]⟩,⟨.or,[13,72]⟩,⟨.or,[15,45]⟩,⟨.or,[17,67]⟩,⟨.and,[38,74]⟩,⟨.or,[0,44]⟩,⟨.or,[3,53]⟩,⟨.or,[10,12]⟩,⟨.or,[6,46]⟩,⟨.or,[4,2]⟩,⟨.or,[19,68]⟩,⟨.or,[59,79]⟩,⟨.or,[9,1]⟩,⟨.or,[3,75]⟩,⟨.or,[2,7]⟩,⟨.or,[10,82]⟩,⟨.or,[18,80]⟩,⟨.or,[7,83]⟩,⟨.or,[8,87]⟩,⟨.and,[23,90]⟩,⟨.or,[17,89]⟩,⟨.or,[14,42]⟩,⟨.or,[14,6]⟩,⟨.or,[4,11]⟩,⟨.and,[30,84]⟩,⟨.and,[20,86]⟩,⟨.or,[1,6]⟩,⟨.and,[24,70]⟩,⟨.or,[51,73]⟩,⟨.or,[0,93]⟩,⟨.or,[2,76]⟩,⟨.or,[77,100]⟩,⟨.or,[7,99]⟩,⟨.and,[21,103]⟩,⟨.or,[10,105]⟩,⟨.or,[57,78]⟩,⟨.or,[16,81]⟩,⟨.or,[13,95]⟩,⟨.and,[37,102]⟩,⟨.or,[2,109]⟩,⟨.or,[19,48]⟩,⟨.or,[12,113]⟩,⟨.or,[17,110]⟩,⟨.or,[98,104]⟩,⟨.and,[22,112]⟩,⟨.and,[26,107]⟩,⟨.and,[39,114]⟩,⟨.or,[64,65]⟩,⟨.and,[35,101]⟩,⟨.or,[54,91]⟩,⟨.or,[43,115]⟩,⟨.or,[7,94]⟩,⟨.or,[56,88]⟩,⟨.and,[33,123]⟩,⟨.or,[15,124]⟩,⟨.or,[6,96]⟩,⟨.or,[15,128]⟩,⟨.or,[69,85]⟩,⟨.and,[34,127]⟩,⟨.and,[29,125]⟩,⟨.and,[32,120]⟩,⟨.and,[25,108]⟩,⟨.or,[40,122]⟩]
def lo : Array Nat := #[2,16,362924737837,1,1,1,2,2,4,4,4,8,8,32,64,128,256,512,2282710570,1,5117757505,52747710546]
def hi : Array Nat := #[268435458,2147483664,362924741933,33554433,134217729,137438953473,2097154,67108866,4194308,536870916,549755813892,8388616,1073741832,4294967328,8589934656,17179869312,34359738624,68719477248,2282743338,1048577,5117757507,52747710802]
def lower : Array Nat := #[(9223373136366403586+2434970229308894745864*2^64),(1152924803141730320+2418829316669544595540*2^64),(6794781011952534829+2438214842321731574398*2^64),(18050682393198593+2361471489678042482688*2^64),(18050682393198593+2361471489678042482688*2^64),(18050682393198593+2361471489678042482688*2^64),(9223373136366403586+2434970229308894745864*2^64),(9223373136366403586+2434970229308894745864*2^64),(282574488338436+2363779285694940446720*2^64),(282574488338436+2363779285694940446720*2^64),(282574488338436+2363779285694940446720*2^64),(1152992972862652424+2434970534389082652720*2^64),(1152992972862652424+2434970534389082652720*2^64),(1008948153530974240+2361255317170803445834*2^64),(18691697672256+2417102601859971039232*2^64),(1099511627904+2371919833941799862273*2^64),(4612258863985459456+2435834908995689120356*2^64),(2413952490014769664+2447652371873598029824*2^64),(13817032663939114538+87121988457240190847*2^64),(18050682393198593+2361471489678042482688*2^64),(12032827660591351873+2427768815595495808792*2^64),(17403230625883893842+132085364052735253886*2^64)]
def upper : Array Nat := #[(9223373136634839042+2434970229308894745864*2^64),(1152924805289213968+2418829316669544595540*2^64),(6794781011952538925+2438214842321731574398*2^64),(18050682426753025+3542063110395453786112*2^64),(18049583015788545+2361471489678042482688*2^64),(18050819832152065+2361471630415530838016*2^64),(9223373136368500738+2434970233706941256968*2^64),(9223373136433512450+2434988243707404227848*2^64),(282574492532740+2363788292894195187712*2^64),(282575025209348+2658927190874293272576*2^64),(283124244152324+2363815314491959410688*2^64),(1152992972871041032+2434970534389351088176*2^64),(1152992973936394248+2434970534397672587312*2^64),(1008948157825941536+2951551127529509097546*2^64),(18700287606848+2421714287878398427136*2^64),(1116691497088+2519493786531476275201*2^64),(4612258898345197824+2435979024183764976228*2^64),(2413952558734246400+2447652371873598029952*2^64),(13817032663939147306+124015476604659294079*2^64),(18050682394247169+2361475993294849722368*2^64),(12032827660591351875+2501555791890336112408*2^64),(17403230625883894098+2493556835863843790206*2^64)]
def label : Array Nat := #[22,20,22,22,22,22,22,22,21,22,22,22,2,22,22,18,22,22,22,22,19,6,8,11,22,3,7,4,0,9,12,1,13,14,15,16,17,5,22,10,4,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,22,17,22,22,22,22,22,22,22,22,22,22,22,22,22,20,22,22,22,22,22,21,11,22,22,22,22,12,19,22,22,22,22,22,22,22,6,22,22,22,22,5,22,22,22,22,19,8,7,10,22,16,21,22,22,22,14,22,22,18,20,15,9,13,3,21]
def sample (v : Nat) (i : Fin 40) := v.testBit i.val
def X (i : R) := run pre (List.ofFn (sample lo[i.val]!))
def Y (i : R) := run pre (List.ofFn (sample hi[i.val]!))
def decode (v : Nat) := List.ofFn fun w : Fin 136 => v.testBit w.val
theorem outputs : ∀ i : R,target (sample lo[i.val]!)≠target (sample hi[i.val]!) := by decide +kernel
theorem replay : ∀ i : R,X i=decode lower[i.val]! ∧ Y i=decode upper[i.val]! := by decide +kernel
theorem classify : ∀ (i : R) (w : Fin 136),lower[i.val]!.testBit w.val ≠ upper[i.val]!.testBit w.val →
    label[w.val]! = i.val := by decide +kernel
theorem lengths (i : R) : (X i).length=136 ∧ (Y i).length=136 := by
  rw [(replay i).1,(replay i).2];simp [decode]
theorem uniqueColumn (w : Nat) (i j : R) (h : (X i).getD w false≠(Y i).getD w false)
    (h' : (X j).getD w false≠(Y j).getD w false) : i=j := by
  by_cases wr : w<136
  · have diff (t : R) (d : (X t).getD w false≠(Y t).getD w false) :
        lower[t.val]!.testBit w ≠ upper[t.val]!.testBit w := by
      rw [(replay t).1,(replay t).2] at d
      simpa only [decode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos wr,Option.getD_some] using d
    exact Fin.ext ((classify i ⟨w,wr⟩ (diff i h)).symm.trans (classify j ⟨w,wr⟩ (diff j h')))
  · exfalso; apply h
    rw [List.getD_eq_default _ _ (by have := (lengths i).1; omega),
      List.getD_eq_default _ _ (by have := (lengths i).2; omega)]
theorem signed_prefix_price (tail : List Gate) (out : Nat)
    (fan : FanInTwo (⟨pre++tail,out⟩ : Circuit))
    (works : ∀ x : Fin 40→Bool,(⟨pre++tail,out⟩ : Circuit).eval (List.ofFn x)=target x) :
    117+inverters tail≤(⟨pre++tail,out⟩ : Circuit).size := by
  have ft (g) (hg : g∈tail) : g.inputs.length≤2 := (fan g (by
    change g∈pre++tail; exact List.mem_append_right _ hg)).2
  have sim (x : Fin 40→Bool) : (run tail (run pre (List.ofFn x))).getD out false=target x := by
    have h := works x
    change ((pre++tail).foldl step (List.ofFn x)).getD out false=_ at h
    simpa only [run,List.foldl_append] using h
  have required := price X Y lengths uniqueColumn tail ft out (fun i => by
    change (run tail (run pre _)).getD out false≠(run tail (run pre _)).getD out false
    rw [sim,sim]
    exact outputs i)
  have plen : pre.length=96 := by decide
  have total := mass_split tail
  change 117+inverters tail≤(pre++tail).length
  rw [List.length_append,plen]; omega
end Prefix96

namespace Tight9838
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000

theorem optimal_under_prefix :
    (∃ (suffix : List Gate) (out : Nat),
      let witness : Circuit := ⟨Prefix96.pre ++ suffix,out⟩
      FanInTwo witness ∧ witness.size=117 ∧
      ∀ x : Fin 40 → Bool,witness.eval (List.ofFn x)=Essential9838.target x) ∧
    ∀ (suffix : List Gate) (out : Nat),
      let witness : Circuit := ⟨Prefix96.pre ++ suffix,out⟩
      FanInTwo witness → (∀ x : Fin 40 → Bool,witness.eval (List.ofFn x)=Essential9838.target x) →
        117+Prefix96.inverters suffix ≤ witness.size := by
  constructor
  · refine ⟨Essential9838.C.gates.drop 96,Essential9838.C.output,?_⟩
    change FanInTwo Essential9838.C ∧ Essential9838.C.size=117 ∧
      ∀ x : Fin 40 → Bool,Essential9838.C.eval (List.ofFn x)=Essential9838.target x
    exact ⟨Essential9838.admissible,Essential9838.size,Essential9838.computes⟩
  · intro suffix out fan works
    exact Prefix96.signed_prefix_price suffix out fan works
end Tight9838

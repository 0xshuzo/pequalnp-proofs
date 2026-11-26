import PEqualNP.Defs

namespace Essential9766
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
  else if i = 26 then (if b then [] else [[]]) else [[i]]

def ts (b : Bool) := (List.range 27).map (leaf b)

theorem table_len (b : Bool) : (ts b).length = 27 := by simp [ts]

theorem table_get (b : Bool) (i : Nat) (hi : i<27) : (ts b).getD i [] = leaf b i := by
  have check : ∀ (a : Bool) (k : Fin 27), (ts a).getD k.val []=leaf a k.val := by decide +kernel
  exact check b ⟨i,hi⟩

def val (x : Fin 26 → Bool) (i : Nat) := x (Fin.ofNat 26 i)

theorem start_good (x : Fin 26 → Bool) :
    Good (val x) (wstep (List.ofFn x) neg) (ts (x 0)) := by
  refine ⟨by simp [wstep_len, table_len], fun i => ?_⟩
  by_cases hi : i < 26
  · rw [wstep_lt (List.ofFn x) neg i (by simpa using hi), ofFn_getD _ _ hi, table_get _ _ (by omega)]
    by_cases hz : i = 0
    · subst i
      cases hv : x 0 <;> simp [leaf, evalD, hv]
    · have h42 : i ≠ 26 := by omega
      simp only [leaf, if_neg hz, if_neg h42, evalD, List.any_cons, List.all_cons,
        List.all_nil, List.any_nil, Bool.and_true, Bool.or_false]
      exact congrArg x (Fin.ext (Nat.mod_eq_of_lt hi).symm)
  · by_cases hl : i = 26
    · subst i
      rw [wstep_last (List.ofFn x) neg 26 (by simp), table_get _ _ (by decide)]
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

def tail : List Gate := [⟨.or, [14,20]⟩,⟨.or, [15,20]⟩,⟨.or, [14,25]⟩,⟨.or, [13,16]⟩,⟨.and, [17,26]⟩,⟨.or, [21,23]⟩,⟨.or, [15,19]⟩,⟨.or, [17,25]⟩,⟨.or, [28,30]⟩,⟨.or, [23,26]⟩,⟨.or, [34,36]⟩,⟨.or, [16,31]⟩,⟨.or, [14,24]⟩,⟨.or, [15,17]⟩,⟨.or, [21,25]⟩,⟨.or, [16,24]⟩,⟨.or, [15,24]⟩,⟨.or, [25,42]⟩,⟨.or, [14,21]⟩,⟨.or, [17,24]⟩,⟨.or, [18,22]⟩,⟨.or, [38,45]⟩,⟨.and, [4,48]⟩,⟨.or, [40,47]⟩,⟨.and, [0,37]⟩,⟨.or, [32,43]⟩,⟨.or, [16,19]⟩,⟨.or, [23,27]⟩,⟨.or, [18,41]⟩,⟨.or, [22,44]⟩,⟨.or, [20,55]⟩,⟨.or, [29,33]⟩,⟨.or, [22,54]⟩,⟨.and, [5,50]⟩,⟨.and, [2,58]⟩,⟨.and, [3,35]⟩,⟨.or, [13,19]⟩,⟨.or, [22,63]⟩,⟨.or, [13,39]⟩,⟨.or, [49,51]⟩,⟨.or, [18,65]⟩,⟨.and, [8,57]⟩,⟨.and, [1,67]⟩,⟨.or, [21,64]⟩,⟨.or, [62,69]⟩,⟨.or, [19,20]⟩,⟨.or, [23,53]⟩,⟨.and, [10,59]⟩,⟨.or, [18,73]⟩,⟨.and, [9,70]⟩,⟨.and, [12,56]⟩,⟨.or, [68,74]⟩,⟨.or, [60,78]⟩,⟨.or, [76,79]⟩,⟨.or, [66,77]⟩,⟨.and, [6,75]⟩,⟨.or, [46,72]⟩,⟨.and, [7,83]⟩,⟨.and, [11,52]⟩,⟨.or, [61,85]⟩,⟨.or, [82,84]⟩,⟨.or, [80,87]⟩,⟨.or, [71,88]⟩,⟨.or, [86,89]⟩,⟨.or, [81,90]⟩]
def C : Circuit := ⟨neg :: tail, 91⟩
def edges : List (Nat × Nat) := [(0,17),(0,23),(0,25),(1,13),(1,14),(1,18),(1,24),(2,14),(2,15),(2,19),(2,25),(3,13),(3,15),(3,16),(3,20),(4,14),(4,16),(4,17),(4,21),(5,15),(5,17),(5,18),(5,22),(6,16),(6,18),(6,19),(6,23),(7,17),(7,19),(7,20),(7,24),(8,18),(8,20),(8,21),(8,25),(9,13),(9,19),(9,21),(9,22),(10,14),(10,20),(10,22),(10,23),(11,15),(11,21),(11,23),(11,24),(12,16),(12,22),(12,24),(12,25)]

def represented (b : Bool) := (tail.foldl tstep (ts b)).getD C.output []
def expected (b : Bool) := edges.flatMap fun e => prodD (leaf b e.1) (leaf b e.2)

theorem same_terms : ∀ b : Bool, agree (represented b) (expected b) = true := by decide +kernel

theorem reflection (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = evalD (val x) (expected (x 0)) := by
  have ok : ∀ g ∈ tail, okb g = true := by decide +kernel
  have h := (good_fold _ tail ok _ _ (start_good x)).2 C.output
  exact h.trans (agreement _ (same_terms _))

theorem eval_flat {α : Type} (v : Nat → Bool) (l : List α) (f : α → List (List Nat)) :
    evalD v (l.flatMap f) = l.any (fun e => evalD v (f e)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, evalD_append, ih, List.any_cons]

theorem leaf_val (x : Fin 26 → Bool) (i : Nat) (hi : i < 26) :
    evalD (val x) (leaf (x 0) i) = val x i := by
  by_cases hz : i = 0
  · subst i
    change evalD (val x) (leaf (x 0) 0) = x 0
    cases hv : x 0 <;> simp [leaf, evalD, hv]
  · have h42 : i ≠ 26 := by omega
    simp [leaf, hz, h42, evalD]

theorem eval_expected (x : Fin 26 → Bool) :
    evalD (val x) (expected (x 0)) = edges.any (fun e => val x e.1 && val x e.2) := by
  rw [expected, eval_flat]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have bounded : ∀ p ∈ edges, p.1 < 26 ∧ p.2 < 26 := by decide +kernel
  constructor <;> rintro ⟨e, he, hv⟩ <;> refine ⟨e, he, ?_⟩
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv
  · simpa only [evalD_prod, leaf_val _ _ (bounded e he).1, leaf_val _ _ (bounded e he).2] using hv

def target (x : Fin 26 → Bool) : Bool := (x 0 && x 17) || (x 0 && x 23) || (x 0 && x 25) || (x 1 && x 13) || (x 1 && x 14) || (x 1 && x 18) || (x 1 && x 24) || (x 2 && x 14) || (x 2 && x 15) || (x 2 && x 19) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 16) || (x 3 && x 20) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 17) || (x 4 && x 21) || (x 5 && x 15) || (x 5 && x 17) || (x 5 && x 18) || (x 5 && x 22) || (x 6 && x 16) || (x 6 && x 18) || (x 6 && x 19) || (x 6 && x 23) || (x 7 && x 17) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 24) || (x 8 && x 18) || (x 8 && x 20) || (x 8 && x 21) || (x 8 && x 25) || (x 9 && x 13) || (x 9 && x 19) || (x 9 && x 21) || (x 9 && x 22) || (x 10 && x 14) || (x 10 && x 20) || (x 10 && x 22) || (x 10 && x 23) || (x 11 && x 15) || (x 11 && x 21) || (x 11 && x 23) || (x 11 && x 24) || (x 12 && x 16) || (x 12 && x 22) || (x 12 && x 24) || (x 12 && x 25)

theorem computes (x : Fin 26 → Bool) : C.eval (List.ofFn x) = target x := by
  rw [reflection, eval_expected]
  dsimp only [edges, List.any, val, target]
  simp only [Bool.or_false, Bool.or_assoc] <;> ac_rfl

def forced (b : Bool) : Circuit :=
  ⟨(if b then ⟨GateOp.and, []⟩ else ⟨GateOp.or, []⟩) :: tail, C.output⟩

def witness₀ (i : Fin 26) : Bool := [4, 17].contains i.val
def witness₁ (i : Fin 26) : Bool := [0, 1, 3, 9].contains i.val

theorem essential :
    (forced false).eval (List.ofFn witness₀) ≠ C.eval (List.ofFn witness₀) ∧
    (forced true).eval (List.ofFn witness₁) ≠ C.eval (List.ofFn witness₁) := by
  decide +kernel

theorem size : C.size = 66 := by decide +kernel

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

theorem upper_essential : HasCircuitSize 26 target 66 :=
  ⟨C, admissible, by rw [size], computes⟩

end Essential9766

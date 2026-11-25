import PEqualNP.Defs

namespace Upper9761
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

def T0 : List (List (List ℕ)) := (List.range 42).map fun i => [[i]]

lemma T0_len : T0.length = 42 := by decide +kernel

lemma T0_get : ∀ i < 42, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 42 → Bool) :
    Good (fun i => x (Fin.ofNat 42 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 42
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 42 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl


def C : Circuit := ⟨[⟨.or, [21,26]⟩,⟨.or, [42,28]⟩,⟨.or, [43,38]⟩,⟨.or, [44,41]⟩,⟨.and, [0,45]⟩,⟨.or, [21,22]⟩,⟨.or, [47,27]⟩,⟨.or, [48,29]⟩,⟨.or, [49,39]⟩,⟨.and, [1,50]⟩,⟨.or, [22,23]⟩,⟨.or, [52,28]⟩,⟨.or, [53,30]⟩,⟨.or, [54,40]⟩,⟨.and, [2,55]⟩,⟨.or, [23,24]⟩,⟨.or, [57,29]⟩,⟨.or, [58,31]⟩,⟨.or, [59,41]⟩,⟨.and, [3,60]⟩,⟨.or, [21,24]⟩,⟨.or, [62,25]⟩,⟨.or, [63,30]⟩,⟨.or, [64,32]⟩,⟨.and, [4,65]⟩,⟨.or, [22,25]⟩,⟨.or, [67,26]⟩,⟨.or, [68,31]⟩,⟨.or, [69,33]⟩,⟨.and, [5,70]⟩,⟨.or, [23,26]⟩,⟨.or, [72,27]⟩,⟨.or, [73,32]⟩,⟨.or, [74,34]⟩,⟨.and, [6,75]⟩,⟨.or, [24,27]⟩,⟨.or, [77,28]⟩,⟨.or, [78,33]⟩,⟨.or, [79,35]⟩,⟨.and, [7,80]⟩,⟨.or, [25,28]⟩,⟨.or, [82,29]⟩,⟨.or, [83,34]⟩,⟨.or, [84,36]⟩,⟨.and, [8,85]⟩,⟨.or, [26,29]⟩,⟨.or, [87,30]⟩,⟨.or, [88,35]⟩,⟨.or, [89,37]⟩,⟨.and, [9,90]⟩,⟨.or, [27,30]⟩,⟨.or, [92,31]⟩,⟨.or, [93,36]⟩,⟨.or, [94,38]⟩,⟨.and, [10,95]⟩,⟨.or, [28,31]⟩,⟨.or, [97,32]⟩,⟨.or, [98,37]⟩,⟨.or, [99,39]⟩,⟨.and, [11,100]⟩,⟨.or, [29,32]⟩,⟨.or, [102,33]⟩,⟨.or, [103,38]⟩,⟨.or, [104,40]⟩,⟨.and, [12,105]⟩,⟨.or, [30,33]⟩,⟨.or, [107,34]⟩,⟨.or, [108,39]⟩,⟨.or, [109,41]⟩,⟨.and, [13,110]⟩,⟨.or, [21,31]⟩,⟨.or, [112,34]⟩,⟨.or, [113,35]⟩,⟨.or, [114,40]⟩,⟨.and, [14,115]⟩,⟨.or, [22,32]⟩,⟨.or, [117,35]⟩,⟨.or, [118,36]⟩,⟨.or, [119,41]⟩,⟨.and, [15,120]⟩,⟨.or, [21,23]⟩,⟨.or, [122,33]⟩,⟨.or, [123,36]⟩,⟨.or, [124,37]⟩,⟨.and, [16,125]⟩,⟨.or, [22,24]⟩,⟨.or, [127,34]⟩,⟨.or, [128,37]⟩,⟨.or, [129,38]⟩,⟨.and, [17,130]⟩,⟨.or, [23,25]⟩,⟨.or, [132,35]⟩,⟨.or, [133,38]⟩,⟨.or, [134,39]⟩,⟨.and, [18,135]⟩,⟨.or, [24,26]⟩,⟨.or, [137,36]⟩,⟨.or, [138,39]⟩,⟨.or, [139,40]⟩,⟨.and, [19,140]⟩,⟨.or, [25,27]⟩,⟨.or, [142,37]⟩,⟨.or, [143,40]⟩,⟨.or, [144,41]⟩,⟨.and, [20,145]⟩,⟨.or, [46,51]⟩,⟨.or, [147,56]⟩,⟨.or, [148,61]⟩,⟨.or, [149,66]⟩,⟨.or, [150,71]⟩,⟨.or, [151,76]⟩,⟨.or, [152,81]⟩,⟨.or, [153,86]⟩,⟨.or, [154,91]⟩,⟨.or, [155,96]⟩,⟨.or, [156,101]⟩,⟨.or, [157,106]⟩,⟨.or, [158,111]⟩,⟨.or, [159,116]⟩,⟨.or, [160,121]⟩,⟨.or, [161,126]⟩,⟨.or, [162,131]⟩,⟨.or, [163,136]⟩,⟨.or, [164,141]⟩,⟨.or, [165,146]⟩],166⟩
def terms := (C.gates.foldl tstep T0).getD C.output []
def listTerms : List (List Nat) := [[0, 21], [0, 26], [0, 28], [0, 38], [0, 41], [1, 21], [1, 22], [1, 27], [1, 29], [1, 39], [2, 22], [2, 23], [2, 28], [2, 30], [2, 40], [3, 23], [3, 24], [3, 29], [3, 31], [3, 41], [4, 21], [4, 24], [4, 25], [4, 30], [4, 32], [5, 22], [5, 25], [5, 26], [5, 31], [5, 33], [6, 23], [6, 26], [6, 27], [6, 32], [6, 34], [7, 24], [7, 27], [7, 28], [7, 33], [7, 35], [8, 25], [8, 28], [8, 29], [8, 34], [8, 36], [9, 26], [9, 29], [9, 30], [9, 35], [9, 37], [10, 27], [10, 30], [10, 31], [10, 36], [10, 38], [11, 28], [11, 31], [11, 32], [11, 37], [11, 39], [12, 29], [12, 32], [12, 33], [12, 38], [12, 40], [13, 30], [13, 33], [13, 34], [13, 39], [13, 41], [14, 21], [14, 31], [14, 34], [14, 35], [14, 40], [15, 22], [15, 32], [15, 35], [15, 36], [15, 41], [16, 21], [16, 23], [16, 33], [16, 36], [16, 37], [17, 22], [17, 24], [17, 34], [17, 37], [17, 38], [18, 23], [18, 25], [18, 35], [18, 38], [18, 39], [19, 24], [19, 26], [19, 36], [19, 39], [19, 40], [20, 25], [20, 27], [20, 37], [20, 40], [20, 41]]
theorem checkedTerms : terms = listTerms := by decide +kernel
theorem reflection (x : Fin 42 → Bool) : C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 42 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output
theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 42 (fun x : Fin 42 → Bool => (x 0 && x 21) || (x 0 && x 26) || (x 0 && x 28) || (x 0 && x 38) || (x 0 && x 41) || (x 1 && x 21) || (x 1 && x 22) || (x 1 && x 27) || (x 1 && x 29) || (x 1 && x 39) || (x 2 && x 22) || (x 2 && x 23) || (x 2 && x 28) || (x 2 && x 30) || (x 2 && x 40) || (x 3 && x 23) || (x 3 && x 24) || (x 3 && x 29) || (x 3 && x 31) || (x 3 && x 41) || (x 4 && x 21) || (x 4 && x 24) || (x 4 && x 25) || (x 4 && x 30) || (x 4 && x 32) || (x 5 && x 22) || (x 5 && x 25) || (x 5 && x 26) || (x 5 && x 31) || (x 5 && x 33) || (x 6 && x 23) || (x 6 && x 26) || (x 6 && x 27) || (x 6 && x 32) || (x 6 && x 34) || (x 7 && x 24) || (x 7 && x 27) || (x 7 && x 28) || (x 7 && x 33) || (x 7 && x 35) || (x 8 && x 25) || (x 8 && x 28) || (x 8 && x 29) || (x 8 && x 34) || (x 8 && x 36) || (x 9 && x 26) || (x 9 && x 29) || (x 9 && x 30) || (x 9 && x 35) || (x 9 && x 37) || (x 10 && x 27) || (x 10 && x 30) || (x 10 && x 31) || (x 10 && x 36) || (x 10 && x 38) || (x 11 && x 28) || (x 11 && x 31) || (x 11 && x 32) || (x 11 && x 37) || (x 11 && x 39) || (x 12 && x 29) || (x 12 && x 32) || (x 12 && x 33) || (x 12 && x 38) || (x 12 && x 40) || (x 13 && x 30) || (x 13 && x 33) || (x 13 && x 34) || (x 13 && x 39) || (x 13 && x 41) || (x 14 && x 21) || (x 14 && x 31) || (x 14 && x 34) || (x 14 && x 35) || (x 14 && x 40) || (x 15 && x 22) || (x 15 && x 32) || (x 15 && x 35) || (x 15 && x 36) || (x 15 && x 41) || (x 16 && x 21) || (x 16 && x 23) || (x 16 && x 33) || (x 16 && x 36) || (x 16 && x 37) || (x 17 && x 22) || (x 17 && x 24) || (x 17 && x 34) || (x 17 && x 37) || (x 17 && x 38) || (x 18 && x 23) || (x 18 && x 25) || (x 18 && x 35) || (x 18 && x 38) || (x 18 && x 39) || (x 19 && x 24) || (x 19 && x 26) || (x 19 && x 36) || (x 19 && x 39) || (x 19 && x 40) || (x 20 && x 25) || (x 20 && x 27) || (x 20 && x 37) || (x 20 && x 40) || (x 20 && x 41)) 125 := by
  refine ⟨C,?_,by decide,?_⟩
  · intro g hg
    simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [reflection,checkedTerms]
    dsimp [evalD,listTerms,List.any,List.all]
    simp only [Bool.and_true,Bool.or_false,Bool.or_assoc] <;> ac_rfl
end Upper9761

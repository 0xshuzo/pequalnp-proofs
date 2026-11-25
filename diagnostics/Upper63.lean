import PEqualNP.Defs

namespace Upper9767
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

def T0 : List (List (List ℕ)) := (List.range 26).map fun i => [[i]]

lemma T0_len : T0.length = 26 := by decide +kernel

lemma T0_get : ∀ i < 26, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 26 → Bool) :
    Good (fun i => x (Fin.ofNat 26 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 26
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 26 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl


def C : Circuit := ⟨[⟨.or,[17,23]⟩,⟨.or,[26,25]⟩,⟨.and,[0,27]⟩,⟨.or,[13,14]⟩,⟨.or,[29,18]⟩,⟨.or,[30,24]⟩,⟨.and,[1,31]⟩,⟨.or,[14,15]⟩,⟨.or,[33,19]⟩,⟨.or,[34,25]⟩,⟨.and,[2,35]⟩,⟨.or,[13,15]⟩,⟨.or,[37,16]⟩,⟨.or,[38,20]⟩,⟨.and,[3,39]⟩,⟨.or,[14,16]⟩,⟨.or,[41,17]⟩,⟨.or,[42,21]⟩,⟨.and,[4,43]⟩,⟨.or,[15,17]⟩,⟨.or,[45,18]⟩,⟨.or,[46,22]⟩,⟨.and,[5,47]⟩,⟨.or,[16,18]⟩,⟨.or,[49,19]⟩,⟨.or,[50,23]⟩,⟨.and,[6,51]⟩,⟨.or,[17,19]⟩,⟨.or,[53,20]⟩,⟨.or,[54,24]⟩,⟨.and,[7,55]⟩,⟨.or,[18,20]⟩,⟨.or,[57,21]⟩,⟨.or,[58,25]⟩,⟨.and,[8,59]⟩,⟨.or,[13,19]⟩,⟨.or,[61,21]⟩,⟨.or,[62,22]⟩,⟨.and,[9,63]⟩,⟨.or,[14,20]⟩,⟨.or,[65,22]⟩,⟨.or,[66,23]⟩,⟨.and,[10,67]⟩,⟨.or,[15,21]⟩,⟨.or,[69,23]⟩,⟨.or,[70,24]⟩,⟨.and,[11,71]⟩,⟨.or,[16,22]⟩,⟨.or,[73,24]⟩,⟨.or,[74,25]⟩,⟨.and,[12,75]⟩,⟨.or,[28,32]⟩,⟨.or,[77,36]⟩,⟨.or,[78,40]⟩,⟨.or,[79,44]⟩,⟨.or,[80,48]⟩,⟨.or,[81,52]⟩,⟨.or,[82,56]⟩,⟨.or,[83,60]⟩,⟨.or,[84,64]⟩,⟨.or,[85,68]⟩,⟨.or,[86,72]⟩,⟨.or,[87,76]⟩],88⟩
def terms := (C.gates.foldl tstep T0).getD C.output []
def listTerms : List (List Nat) := [[0, 17], [0, 23], [0, 25], [1, 13], [1, 14], [1, 18], [1, 24], [2, 14], [2, 15], [2, 19], [2, 25], [3, 13], [3, 15], [3, 16], [3, 20], [4, 14], [4, 16], [4, 17], [4, 21], [5, 15], [5, 17], [5, 18], [5, 22], [6, 16], [6, 18], [6, 19], [6, 23], [7, 17], [7, 19], [7, 20], [7, 24], [8, 18], [8, 20], [8, 21], [8, 25], [9, 13], [9, 19], [9, 21], [9, 22], [10, 14], [10, 20], [10, 22], [10, 23], [11, 15], [11, 21], [11, 23], [11, 24], [12, 16], [12, 22], [12, 24], [12, 25]]
theorem checkedTerms : terms = listTerms := by decide +kernel
theorem reflection (x : Fin 26 → Bool) : C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output
theorem upper : PEqualNP.MetaComplexity.HasCircuitSize 26 (fun x : Fin 26 → Bool => (x 0 && x 17) || (x 0 && x 23) || (x 0 && x 25) || (x 1 && x 13) || (x 1 && x 14) || (x 1 && x 18) || (x 1 && x 24) || (x 2 && x 14) || (x 2 && x 15) || (x 2 && x 19) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 15) || (x 3 && x 16) || (x 3 && x 20) || (x 4 && x 14) || (x 4 && x 16) || (x 4 && x 17) || (x 4 && x 21) || (x 5 && x 15) || (x 5 && x 17) || (x 5 && x 18) || (x 5 && x 22) || (x 6 && x 16) || (x 6 && x 18) || (x 6 && x 19) || (x 6 && x 23) || (x 7 && x 17) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 24) || (x 8 && x 18) || (x 8 && x 20) || (x 8 && x 21) || (x 8 && x 25) || (x 9 && x 13) || (x 9 && x 19) || (x 9 && x 21) || (x 9 && x 22) || (x 10 && x 14) || (x 10 && x 20) || (x 10 && x 22) || (x 10 && x 23) || (x 11 && x 15) || (x 11 && x 21) || (x 11 && x 23) || (x 11 && x 24) || (x 12 && x 16) || (x 12 && x 22) || (x 12 && x 24) || (x 12 && x 25)) 63 := by
  refine ⟨C,?_,by decide,?_⟩
  · intro g hg
    simp only [C,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [reflection,checkedTerms]
    dsimp [evalD,listTerms,List.any,List.all]
    simp only [Bool.and_true,Bool.or_false,Bool.or_assoc] <;> ac_rfl
end Upper9767

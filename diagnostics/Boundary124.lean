import PEqualNP.Defs

namespace Witness9743
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


def C : Circuit := ⟨[⟨.or, [32,39]⟩,⟨.or, [29,32]⟩,⟨.or, [21,32]⟩,⟨.or, [22,33]⟩,⟨.or, [31,42]⟩,⟨.or, [26,38]⟩,⟨.or, [32,41]⟩,⟨.or, [39,41]⟩,⟨.or, [28,47]⟩,⟨.or, [24,34]⟩,⟨.or, [34,49]⟩,⟨.or, [22,37]⟩,⟨.or, [23,25]⟩,⟨.or, [36,37]⟩,⟨.or, [30,35]⟩,⟨.or, [41,50]⟩,⟨.or, [23,33]⟩,⟨.or, [38,39]⟩,⟨.or, [21,27]⟩,⟨.or, [22,28]⟩,⟨.or, [22,35]⟩,⟨.or, [51,53]⟩,⟨.or, [35,59]⟩,⟨.or, [24,27]⟩,⟨.or, [36,48]⟩,⟨.or, [23,30]⟩,⟨.or, [25,30]⟩,⟨.or, [28,36]⟩,⟨.and, [0,57]⟩,⟨.or, [38,40]⟩,⟨.or, [29,31]⟩,⟨.or, [21,34]⟩,⟨.or, [31,35]⟩,⟨.or, [24,26]⟩,⟨.or, [54,64]⟩,⟨.and, [18,76]⟩,⟨.or, [21,55]⟩,⟨.or, [26,29]⟩,⟨.or, [56,79]⟩,⟨.or, [37,80]⟩,⟨.or, [73,74]⟩,⟨.or, [34,69]⟩,⟨.or, [43,71]⟩,⟨.or, [40,82]⟩,⟨.or, [58,78]⟩,⟨.and, [9,81]⟩,⟨.or, [24,68]⟩,⟨.or, [25,83]⟩,⟨.or, [38,63]⟩,⟨.or, [33,65]⟩,⟨.or, [39,40]⟩,⟨.or, [39,60]⟩,⟨.or, [40,67]⟩,⟨.or, [28,91]⟩,⟨.or, [62,66]⟩,⟨.or, [30,33]⟩,⟨.or, [23,34]⟩,⟨.or, [35,95]⟩,⟨.or, [33,84]⟩,⟨.or, [44,88]⟩,⟨.and, [4,101]⟩,⟨.and, [7,99]⟩,⟨.or, [52,97]⟩,⟨.or, [29,89]⟩,⟨.and, [17,90]⟩,⟨.or, [26,27]⟩,⟨.or, [61,94]⟩,⟨.and, [16,86]⟩,⟨.and, [12,100]⟩,⟨.and, [8,105]⟩,⟨.and, [15,96]⟩,⟨.or, [75,92]⟩,⟨.or, [41,72]⟩,⟨.or, [70,112]⟩,⟨.or, [98,107]⟩,⟨.and, [13,104]⟩,⟨.and, [2,108]⟩,⟨.or, [28,37]⟩,⟨.or, [30,38]⟩,⟨.and, [14,85]⟩,⟨.or, [27,120]⟩,⟨.or, [36,122]⟩,⟨.or, [40,41]⟩,⟨.or, [26,31]⟩,⟨.or, [111,118]⟩,⟨.or, [37,124]⟩,⟨.or, [36,113]⟩,⟨.or, [32,116]⟩,⟨.or, [25,125]⟩,⟨.or, [29,93]⟩,⟨.or, [27,127]⟩,⟨.and, [19,128]⟩,⟨.or, [22,131]⟩,⟨.or, [23,114]⟩,⟨.or, [25,132]⟩,⟨.or, [31,123]⟩,⟨.or, [103,110]⟩,⟨.and, [10,137]⟩,⟨.or, [109,133]⟩,⟨.or, [45,130]⟩,⟨.or, [46,119]⟩,⟨.or, [102,117]⟩,⟨.and, [20,136]⟩,⟨.and, [6,129]⟩,⟨.or, [24,135]⟩,⟨.or, [143,145]⟩,⟨.and, [3,146]⟩,⟨.or, [126,138]⟩,⟨.and, [11,142]⟩,⟨.or, [140,149]⟩,⟨.and, [5,141]⟩,⟨.or, [87,148]⟩,⟨.or, [106,150]⟩,⟨.and, [1,134]⟩,⟨.or, [151,154]⟩,⟨.or, [152,153]⟩,⟨.or, [121,155]⟩,⟨.or, [77,144]⟩,⟨.or, [139,159]⟩,⟨.or, [158,160]⟩,⟨.or, [156,157]⟩,⟨.or, [147,162]⟩,⟨.or, [161,163]⟩,⟨.or, [115,164]⟩],165⟩
def terms := (C.gates.foldl tstep T0).getD C.output []
def ed : List (Fin 42 × Fin 42) := [(0,26),(0,28),(0,38),(0,41),(1,21),(1,22),(1,27),(1,29),(1,39),(2,22),(2,23),(2,28),(2,30),(2,40),(3,23),(3,24),(3,29),(3,31),(3,41),(4,21),(4,24),(4,25),(4,30),(4,32),(5,22),(5,25),(5,26),(5,31),(5,33),(6,23),(6,26),(6,27),(6,32),(6,34),(7,24),(7,27),(7,28),(7,33),(7,35),(8,25),(8,28),(8,29),(8,34),(8,36),(9,26),(9,29),(9,30),(9,35),(9,37),(10,27),(10,30),(10,31),(10,36),(10,38),(11,28),(11,31),(11,32),(11,37),(11,39),(12,29),(12,32),(12,33),(12,38),(12,40),(13,30),(13,33),(13,34),(13,39),(13,41),(14,21),(14,31),(14,34),(14,35),(14,40),(15,22),(15,32),(15,35),(15,36),(15,41),(16,21),(16,23),(16,33),(16,36),(16,37),(17,22),(17,24),(17,34),(17,37),(17,38),(18,23),(18,25),(18,35),(18,38),(18,39),(19,24),(19,26),(19,36),(19,39),(19,40),(20,25),(20,27),(20,37),(20,40),(20,41)]
def literal : List (Nat × Nat) := [(0,26),(0,28),(0,38),(0,41),(1,21),(1,22),(1,27),(1,29),(1,39),(2,22),(2,23),(2,28),(2,30),(2,40),(3,23),(3,24),(3,29),(3,31),(3,41),(4,21),(4,24),(4,25),(4,30),(4,32),(5,22),(5,25),(5,26),(5,31),(5,33),(6,23),(6,26),(6,27),(6,32),(6,34),(7,24),(7,27),(7,28),(7,33),(7,35),(8,25),(8,28),(8,29),(8,34),(8,36),(9,26),(9,29),(9,30),(9,35),(9,37),(10,27),(10,30),(10,31),(10,36),(10,38),(11,28),(11,31),(11,32),(11,37),(11,39),(12,29),(12,32),(12,33),(12,38),(12,40),(13,30),(13,33),(13,34),(13,39),(13,41),(14,21),(14,31),(14,34),(14,35),(14,40),(15,22),(15,32),(15,35),(15,36),(15,41),(16,21),(16,23),(16,33),(16,36),(16,37),(17,22),(17,24),(17,34),(17,37),(17,38),(18,23),(18,25),(18,35),(18,38),(18,39),(19,24),(19,26),(19,36),(19,39),(19,40),(20,25),(20,27),(20,37),(20,40),(20,41)]

theorem posted : ∀ (u v : Fin 42), (u,v) ∈ ed ↔ (u.val,v.val) ∈ literal := by decide +kernel
def sourceSound : Bool := terms.all fun c =>
  ed.any fun e => decide (e.1.val ∈ c ∧ e.2.val ∈ c)
def sourceComplete : Bool := ed.all fun e =>
  terms.any fun c => c.all fun w => decide (w=e.1.val ∨ w=e.2.val)
theorem sound_check : sourceSound = true := by decide +kernel
theorem complete_check : sourceComplete = true := by decide +kernel
theorem get_self (p : Fin 42) : Fin.ofNat 42 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
theorem exact_edge (x : Fin 42 → Bool) :
    C.eval (List.ofFn x)=true ↔ ∃ u v : Fin 42,
      (u.val,v.val) ∈ literal ∧ x u=true ∧ x v=true := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  have cr := (good_fold _ C.gates ok _ _ (good_init x)).2 C.output
  change C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 42 i)) terms at cr
  rw [cr]
  constructor
  · intro yes
    obtain ⟨cl,hcl,passed⟩ := List.any_eq_true.mp yes
    obtain ⟨e,he,parts⟩ := List.any_eq_true.mp (List.all_eq_true.mp sound_check cl hcl)
    obtain ⟨hp,hq⟩ := of_decide_eq_true parts
    refine ⟨e.1,e.2,(posted _ _).mp he,?_,?_⟩
    · simpa only [get_self] using List.all_eq_true.mp passed e.1.val hp
    · simpa only [get_self] using List.all_eq_true.mp passed e.2.val hq
  · rintro ⟨u,v,h,hU,hV⟩
    obtain ⟨cl,hcl,parts⟩ := List.any_eq_true.mp (List.all_eq_true.mp complete_check (u,v) ((posted _ _).mpr h))
    apply List.any_eq_true.mpr
    refine ⟨cl,hcl,List.all_eq_true.mpr ?_⟩
    intro w hw
    have hcase : w=u.val ∨ w=v.val := of_decide_eq_true (List.all_eq_true.mp parts w hw)
    rcases hcase with rfl|rfl
    · simpa only [get_self] using hU
    · simpa only [get_self] using hV
theorem monoC : Monotone2 C := by
  have good : ∀ g ∈ C.gates, okb g=true := by decide +kernel
  intro g hg
  exact okb_spec g (good g hg)
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 124 ∧ (∀ x : Fin 42 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 42, (u.val, v.val) ∈ ([(0, 26), (0, 28), (0, 38), (0, 41), (1, 21), (1, 22), (1, 27), (1, 29), (1, 39), (2, 22), (2, 23), (2, 28), (2, 30), (2, 40), (3, 23), (3, 24), (3, 29), (3, 31), (3, 41), (4, 21), (4, 24), (4, 25), (4, 30), (4, 32), (5, 22), (5, 25), (5, 26), (5, 31), (5, 33), (6, 23), (6, 26), (6, 27), (6, 32), (6, 34), (7, 24), (7, 27), (7, 28), (7, 33), (7, 35), (8, 25), (8, 28), (8, 29), (8, 34), (8, 36), (9, 26), (9, 29), (9, 30), (9, 35), (9, 37), (10, 27), (10, 30), (10, 31), (10, 36), (10, 38), (11, 28), (11, 31), (11, 32), (11, 37), (11, 39), (12, 29), (12, 32), (12, 33), (12, 38), (12, 40), (13, 30), (13, 33), (13, 34), (13, 39), (13, 41), (14, 21), (14, 31), (14, 34), (14, 35), (14, 40), (15, 22), (15, 32), (15, 35), (15, 36), (15, 41), (16, 21), (16, 23), (16, 33), (16, 36), (16, 37), (17, 22), (17, 24), (17, 34), (17, 37), (17, 38), (18, 23), (18, 25), (18, 35), (18, 38), (18, 39), (19, 24), (19, 26), (19, 36), (19, 39), (19, 40), (20, 25), (20, 27), (20, 37), (20, 40), (20, 41)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  exact ⟨C,monoC,by decide,exact_edge⟩
-- A conjunction of three disjunctions has a directed cross pair among two
-- true point-line pairs whenever its truth on point pairs and line pairs is excluded.
def meets (a b : Fin 8) : Prop := a.val ||| b.val = 7
instance (a b : Fin 8) : Decidable (meets a b) := inferInstanceAs (Decidable (_ = _))
theorem crossing_bits : ∀ a b c d : Fin 8,
    meets a b → meets c d → meets a c ∨ meets a d ∨ meets b c ∨ meets b d := by
  decide +kernel
theorem same_shore : ∀ p q : Fin 21,
    ¬ ((p.val,q.val) ∈ literal ∨ (q.val,p.val) ∈ literal) ∧
    ¬ ((21+p.val,21+q.val) ∈ literal ∨ (21+q.val,21+p.val) ∈ literal) := by
  decide +kernel
theorem clause_cross (w : Fin 42 → Fin 8)
    (safe : ∀ r s : Fin 42, meets (w r) (w s) → (r.val,s.val) ∈ literal ∨ (s.val,r.val) ∈ literal)
    (p q u v : Fin 21)
    (a : meets (w (Fin.castAdd 21 p)) (w (Fin.natAdd 21 u)))
    (b : meets (w (Fin.castAdd 21 q)) (w (Fin.natAdd 21 v))) :
    meets (w (Fin.castAdd 21 p)) (w (Fin.natAdd 21 v)) ∨
    meets (w (Fin.natAdd 21 u)) (w (Fin.castAdd 21 q)) := by
  rcases crossing_bits _ _ _ _ a b with h|h|h|h
  · exact False.elim ((same_shore p q).1 (safe _ _ h))
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim ((same_shore u v).2 (safe _ _ h))

end Witness9743

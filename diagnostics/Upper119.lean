import PEqualNP.Defs

namespace PuncturedUpper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 0

-- DNF reflection from the published L2418.
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

def T0 : List (List (List ℕ)) := (List.range 41).map fun i => [[i]]

lemma T0_len : T0.length = 41 := by decide +kernel

lemma T0_get : ∀ i < 41, T0.getD i [] = [[i]] := by decide +kernel

lemma good_init (x : Fin 41 → Bool) :
    Good (fun i => x (Fin.ofNat 41 i)) (List.ofFn x) T0 := by
  refine ⟨by rw [List.length_ofFn, T0_len], fun i => ?_⟩
  by_cases h : i < 41
  · rw [ofFn_getD x i h, T0_get i h]
    show x ⟨i, h⟩ = ((x (Fin.ofNat 41 i) && true) || false)
    rw [Bool.and_true, Bool.or_false]
    exact congrArg x (Fin.ext (Nat.mod_eq_of_lt h).symm)
  · have h1 : (List.ofFn x).getD i false = false :=
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)
    have h2 : T0.getD i [] = [] := List.getD_eq_default _ _ (by rw [T0_len]; omega)
    rw [h1, h2]
    rfl


def C : Circuit := ⟨[
  ⟨.or,[1,2]⟩,
  ⟨.or,[41,5]⟩,
  ⟨.or,[42,15]⟩,
  ⟨.or,[43,17]⟩,
  ⟨.and,[44,21]⟩,
  ⟨.or,[2,3]⟩,
  ⟨.or,[46,6]⟩,
  ⟨.or,[47,16]⟩,
  ⟨.or,[48,18]⟩,
  ⟨.and,[49,22]⟩,
  ⟨.or,[3,4]⟩,
  ⟨.or,[51,7]⟩,
  ⟨.or,[52,17]⟩,
  ⟨.or,[53,19]⟩,
  ⟨.and,[54,23]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[56,8]⟩,
  ⟨.or,[57,18]⟩,
  ⟨.or,[58,20]⟩,
  ⟨.and,[59,24]⟩,
  ⟨.or,[0,5]⟩,
  ⟨.or,[61,6]⟩,
  ⟨.or,[62,9]⟩,
  ⟨.or,[63,19]⟩,
  ⟨.and,[64,25]⟩,
  ⟨.or,[1,6]⟩,
  ⟨.or,[66,7]⟩,
  ⟨.or,[67,10]⟩,
  ⟨.or,[68,20]⟩,
  ⟨.and,[69,26]⟩,
  ⟨.or,[0,2]⟩,
  ⟨.or,[71,7]⟩,
  ⟨.or,[72,8]⟩,
  ⟨.or,[73,11]⟩,
  ⟨.and,[74,27]⟩,
  ⟨.or,[1,3]⟩,
  ⟨.or,[76,8]⟩,
  ⟨.or,[77,9]⟩,
  ⟨.or,[78,12]⟩,
  ⟨.and,[79,28]⟩,
  ⟨.or,[2,4]⟩,
  ⟨.or,[81,9]⟩,
  ⟨.or,[82,10]⟩,
  ⟨.or,[83,13]⟩,
  ⟨.and,[84,29]⟩,
  ⟨.or,[3,5]⟩,
  ⟨.or,[86,10]⟩,
  ⟨.or,[87,11]⟩,
  ⟨.or,[88,14]⟩,
  ⟨.and,[89,30]⟩,
  ⟨.or,[4,6]⟩,
  ⟨.or,[91,11]⟩,
  ⟨.or,[92,12]⟩,
  ⟨.or,[93,15]⟩,
  ⟨.and,[94,31]⟩,
  ⟨.or,[5,7]⟩,
  ⟨.or,[96,12]⟩,
  ⟨.or,[97,13]⟩,
  ⟨.or,[98,16]⟩,
  ⟨.and,[99,32]⟩,
  ⟨.or,[6,8]⟩,
  ⟨.or,[101,13]⟩,
  ⟨.or,[102,14]⟩,
  ⟨.or,[103,17]⟩,
  ⟨.and,[104,33]⟩,
  ⟨.or,[7,9]⟩,
  ⟨.or,[106,14]⟩,
  ⟨.or,[107,15]⟩,
  ⟨.or,[108,18]⟩,
  ⟨.and,[109,34]⟩,
  ⟨.or,[8,10]⟩,
  ⟨.or,[111,15]⟩,
  ⟨.or,[112,16]⟩,
  ⟨.or,[113,19]⟩,
  ⟨.and,[114,35]⟩,
  ⟨.or,[9,11]⟩,
  ⟨.or,[116,16]⟩,
  ⟨.or,[117,17]⟩,
  ⟨.or,[118,20]⟩,
  ⟨.and,[119,36]⟩,
  ⟨.or,[0,10]⟩,
  ⟨.or,[121,12]⟩,
  ⟨.or,[122,17]⟩,
  ⟨.or,[123,18]⟩,
  ⟨.and,[124,37]⟩,
  ⟨.or,[1,11]⟩,
  ⟨.or,[126,13]⟩,
  ⟨.or,[127,18]⟩,
  ⟨.or,[128,19]⟩,
  ⟨.and,[129,38]⟩,
  ⟨.or,[2,12]⟩,
  ⟨.or,[131,14]⟩,
  ⟨.or,[132,19]⟩,
  ⟨.or,[133,20]⟩,
  ⟨.and,[134,39]⟩,
  ⟨.or,[0,3]⟩,
  ⟨.or,[136,13]⟩,
  ⟨.or,[137,15]⟩,
  ⟨.or,[138,20]⟩,
  ⟨.and,[139,40]⟩,
  ⟨.or,[45,50]⟩,
  ⟨.or,[141,55]⟩,
  ⟨.or,[142,60]⟩,
  ⟨.or,[143,65]⟩,
  ⟨.or,[144,70]⟩,
  ⟨.or,[145,75]⟩,
  ⟨.or,[146,80]⟩,
  ⟨.or,[147,85]⟩,
  ⟨.or,[148,90]⟩,
  ⟨.or,[149,95]⟩,
  ⟨.or,[150,100]⟩,
  ⟨.or,[151,105]⟩,
  ⟨.or,[152,110]⟩,
  ⟨.or,[153,115]⟩,
  ⟨.or,[154,120]⟩,
  ⟨.or,[155,125]⟩,
  ⟨.or,[156,130]⟩,
  ⟨.or,[157,135]⟩,
  ⟨.or,[158,140]⟩],159⟩

def terms := (C.gates.foldl tstep T0).getD C.output []
def ed : List (Fin 41 × Fin 41) := [(0,25),(0,27),(0,37),(0,40),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,22),(3,23),(3,28),(3,30),(3,40),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,29),(13,32),(13,33),(13,38),(13,40),(14,30),(14,33),(14,34),(14,39),(15,21),(15,31),(15,34),(15,35),(15,40),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39),(20,24),(20,26),(20,36),(20,39),(20,40)]
def literal : List (Nat × Nat) := [(0,25),(0,27),(0,37),(0,40),(1,21),(1,26),(1,28),(1,38),(2,21),(2,22),(2,27),(2,29),(2,39),(3,22),(3,23),(3,28),(3,30),(3,40),(4,23),(4,24),(4,29),(4,31),(5,21),(5,24),(5,25),(5,30),(5,32),(6,22),(6,25),(6,26),(6,31),(6,33),(7,23),(7,26),(7,27),(7,32),(7,34),(8,24),(8,27),(8,28),(8,33),(8,35),(9,25),(9,28),(9,29),(9,34),(9,36),(10,26),(10,29),(10,30),(10,35),(10,37),(11,27),(11,30),(11,31),(11,36),(11,38),(12,28),(12,31),(12,32),(12,37),(12,39),(13,29),(13,32),(13,33),(13,38),(13,40),(14,30),(14,33),(14,34),(14,39),(15,21),(15,31),(15,34),(15,35),(15,40),(16,22),(16,32),(16,35),(16,36),(17,21),(17,23),(17,33),(17,36),(17,37),(18,22),(18,24),(18,34),(18,37),(18,38),(19,23),(19,25),(19,35),(19,38),(19,39),(20,24),(20,26),(20,36),(20,39),(20,40)]
theorem posted : ∀ (u v : Fin 41), (u,v) ∈ ed ↔ (u.val,v.val) ∈ literal := by decide +kernel
def sourceSound : Bool := terms.all fun c =>
  ed.any fun e => decide (e.1.val ∈ c ∧ e.2.val ∈ c)
def sourceComplete : Bool := ed.all fun e =>
  terms.any fun c => c.all fun w => decide (w=e.1.val ∨ w=e.2.val)
theorem sound_check : sourceSound = true := by decide +kernel
theorem complete_check : sourceComplete = true := by decide +kernel
theorem get_self (p : Fin 41) : Fin.ofNat 41 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
theorem exact_edge (x : Fin 41 → Bool) :
    C.eval (List.ofFn x)=true ↔ ∃ u v : Fin 41,
      (u.val,v.val) ∈ literal ∧ x u=true ∧ x v=true := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  have cr := (good_fold _ C.gates ok _ _ (good_init x)).2 C.output
  change C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 41 i)) terms at cr
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
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 119 ∧ (∀ x : Fin 41 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 41, (u.val, v.val) ∈ ([(0, 25), (0, 27), (0, 37), (0, 40), (1, 21), (1, 26), (1, 28), (1, 38), (2, 21), (2, 22), (2, 27), (2, 29), (2, 39), (3, 22), (3, 23), (3, 28), (3, 30), (3, 40), (4, 23), (4, 24), (4, 29), (4, 31), (5, 21), (5, 24), (5, 25), (5, 30), (5, 32), (6, 22), (6, 25), (6, 26), (6, 31), (6, 33), (7, 23), (7, 26), (7, 27), (7, 32), (7, 34), (8, 24), (8, 27), (8, 28), (8, 33), (8, 35), (9, 25), (9, 28), (9, 29), (9, 34), (9, 36), (10, 26), (10, 29), (10, 30), (10, 35), (10, 37), (11, 27), (11, 30), (11, 31), (11, 36), (11, 38), (12, 28), (12, 31), (12, 32), (12, 37), (12, 39), (13, 29), (13, 32), (13, 33), (13, 38), (13, 40), (14, 30), (14, 33), (14, 34), (14, 39), (15, 21), (15, 31), (15, 34), (15, 35), (15, 40), (16, 22), (16, 32), (16, 35), (16, 36), (17, 21), (17, 23), (17, 33), (17, 36), (17, 37), (18, 22), (18, 24), (18, 34), (18, 37), (18, 38), (19, 23), (19, 25), (19, 35), (19, 38), (19, 39), (20, 24), (20, 26), (20, 36), (20, 39), (20, 40)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  exact ⟨C,monoC,by decide,exact_edge⟩
end PuncturedUpper

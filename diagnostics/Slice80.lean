import PEqualNP.Defs

namespace Slice18757
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000

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


def C : Circuit := ⟨[⟨.or,[2,3]⟩,⟨.or,[42,6]⟩,⟨.or,[43,16]⟩,⟨.or,[44,18]⟩,⟨.and,[45,23]⟩,⟨.or,[3,4]⟩,⟨.or,[47,7]⟩,⟨.or,[48,17]⟩,⟨.or,[49,19]⟩,⟨.and,[50,24]⟩,⟨.or,[4,5]⟩,⟨.or,[52,8]⟩,⟨.or,[53,18]⟩,⟨.or,[54,20]⟩,⟨.and,[55,25]⟩,⟨.or,[2,4]⟩,⟨.or,[57,9]⟩,⟨.or,[58,10]⟩,⟨.or,[59,13]⟩,⟨.and,[60,30]⟩,⟨.or,[3,5]⟩,⟨.or,[62,10]⟩,⟨.or,[63,11]⟩,⟨.or,[64,14]⟩,⟨.and,[65,31]⟩,⟨.or,[4,6]⟩,⟨.or,[67,11]⟩,⟨.or,[68,12]⟩,⟨.or,[69,15]⟩,⟨.and,[70,32]⟩,⟨.or,[5,7]⟩,⟨.or,[72,12]⟩,⟨.or,[73,13]⟩,⟨.or,[74,16]⟩,⟨.and,[75,33]⟩,⟨.or,[6,8]⟩,⟨.or,[77,13]⟩,⟨.or,[78,14]⟩,⟨.or,[79,17]⟩,⟨.and,[80,34]⟩,⟨.or,[7,9]⟩,⟨.or,[82,14]⟩,⟨.or,[83,15]⟩,⟨.or,[84,18]⟩,⟨.and,[85,35]⟩,⟨.or,[8,10]⟩,⟨.or,[87,15]⟩,⟨.or,[88,16]⟩,⟨.or,[89,19]⟩,⟨.and,[90,36]⟩,⟨.or,[9,11]⟩,⟨.or,[92,16]⟩,⟨.or,[93,17]⟩,⟨.or,[94,20]⟩,⟨.and,[95,37]⟩,⟨.or,[2,12]⟩,⟨.or,[97,14]⟩,⟨.or,[98,19]⟩,⟨.or,[99,20]⟩,⟨.and,[100,40]⟩,⟨.or,[21,22]⟩,⟨.or,[102,26]⟩,⟨.or,[103,27]⟩,⟨.or,[104,28]⟩,⟨.or,[105,29]⟩,⟨.or,[106,38]⟩,⟨.or,[107,39]⟩,⟨.or,[108,41]⟩,⟨.or,[109,46]⟩,⟨.or,[110,51]⟩,⟨.or,[111,56]⟩,⟨.or,[112,61]⟩,⟨.or,[113,66]⟩,⟨.or,[114,71]⟩,⟨.or,[115,76]⟩,⟨.or,[116,81]⟩,⟨.or,[117,86]⟩,⟨.or,[118,91]⟩,⟨.or,[119,96]⟩,⟨.or,[120,101]⟩],121⟩
def terms := (C.gates.foldl tstep T0).getD C.output []
def listTerms : List (List Nat) := [[21], [22], [26], [27], [28], [29], [38], [39], [41], [2, 23], [3, 23], [6, 23], [16, 23], [18, 23], [3, 24], [4, 24], [7, 24], [17, 24], [19, 24], [4, 25], [5, 25], [8, 25], [18, 25], [20, 25], [2, 30], [4, 30], [9, 30], [10, 30], [13, 30], [3, 31], [5, 31], [10, 31], [11, 31], [14, 31], [4, 32], [6, 32], [11, 32], [12, 32], [15, 32], [5, 33], [7, 33], [12, 33], [13, 33], [16, 33], [6, 34], [8, 34], [13, 34], [14, 34], [17, 34], [7, 35], [9, 35], [14, 35], [15, 35], [18, 35], [8, 36], [10, 36], [15, 36], [16, 36], [19, 36], [9, 37], [11, 37], [16, 37], [17, 37], [20, 37], [2, 40], [12, 40], [14, 40], [19, 40], [20, 40]]
theorem checkedTerms : terms = listTerms := by decide +kernel

theorem goodOps : ∀ g ∈ C.gates, okb g=true := by decide +kernel

theorem reflection (x : Fin 42 → Bool) : C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 42 i)) terms := by
  exact (good_fold _ C.gates goodOps _ _ (good_init x)).2 C.output

theorem mono : Monotone2 C := fun g hg => okb_spec g (goodOps g hg)

def rawEdge (p l : Nat) := p < 21 ∧ 21 ≤ l ∧ l < 42 ∧ (l+21-p)%21 ∈ ([0,5,7,17,20]:List Nat)
instance (p l : Nat) : Decidable (rawEdge p l) := by unfold rawEdge; infer_instance

abbrev adjacent (p l : Fin 42) := p.val < 21 ∧ 21 ≤ l.val ∧ (l.val+21-p.val)%21 ∈ ([0,5,7,17,20]:List Nat)
abbrev hasEdge (x : Fin 42→Bool) := ∃ p l, adjacent p l ∧ x p=true ∧ x l=true
theorem soundTerms : listTerms.all (fun c => (0::1::c).any fun p => c.any fun l => decide (rawEdge p l))=true := by
  decide +kernel

theorem coverTerms : ∀ p l : Fin 42, adjacent p l →
    listTerms.any (fun c => c.all fun i => decide (i=p.val ∨ i=l.val))=true := by
  decide +kernel

theorem correct (x : Fin 42 → Bool) (x0 : x 0=true) (x1 : x 1=true) : C.eval (List.ofFn x)=true ↔ hasEdge x := by
  rw [reflection,checkedTerms]
  change (listTerms.any (fun c => c.all fun i => x (Fin.ofNat 42 i)))=true ↔ hasEdge x
  constructor
  · intro yes
    obtain ⟨c,hc,active⟩ := List.any_eq_true.mp yes
    obtain ⟨p,hp,found⟩ := List.any_eq_true.mp (List.all_eq_true.mp soundTerms c hc)
    obtain ⟨l,hl,edge⟩ := List.any_eq_true.mp found
    obtain ⟨hp21,hl21,hl42,hdiff⟩ := of_decide_eq_true edge
    have hp42 : p<42 := by omega
    have hp' : Fin.ofNat 42 p = (⟨p,hp42⟩ : Fin 42) := Fin.ext (Nat.mod_eq_of_lt hp42)
    have hl' : Fin.ofNat 42 l = (⟨l,hl42⟩ : Fin 42) := Fin.ext (Nat.mod_eq_of_lt hl42)
    refine ⟨⟨p,hp42⟩,⟨l,hl42⟩,⟨hp21,hl21,hdiff⟩,?_,?_⟩
    · simp only [List.mem_cons] at hp
      rcases hp with h|h|h
      · subst p
        simpa using x0
      · subst p
        simpa using x1
      · simpa only [hp'] using List.all_eq_true.mp active p h
    · simpa only [hl'] using List.all_eq_true.mp active l hl
  · rintro ⟨p,l,edge,hp,hl⟩
    obtain ⟨c,hc,choice⟩ := List.any_eq_true.mp (coverTerms p l edge)
    refine List.any_eq_true.mpr ⟨c,hc,List.all_eq_true.mpr (fun i hi => ?_)⟩
    have h := of_decide_eq_true (List.all_eq_true.mp choice i hi)
    rcases h with eq|eq
    · subst i
      have ef : Fin.ofNat 42 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
      simpa only [ef] using hp
    · subst i
      have ef : Fin.ofNat 42 l.val = l := Fin.ext (Nat.mod_eq_of_lt l.isLt)
      simpa only [ef] using hl

theorem slice_witness : ∃ D : Circuit, Monotone2 D ∧ D.size=80 ∧
    ∀ x : Fin 42→Bool, x 0=true → x 1=true → (D.eval (List.ofFn x)=true ↔ hasEdge x) :=
  ⟨C,mono,by decide +kernel,correct⟩
end Slice18757

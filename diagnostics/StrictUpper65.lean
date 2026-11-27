import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_7911.Upper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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


def body : Circuit := ⟨[⟨.or, [1,2]⟩,⟨.or, [26,4]⟩,⟨.or, [27,10]⟩,⟨.and, [14,28]⟩,⟨.or, [2,3]⟩,⟨.or, [30,5]⟩,⟨.or, [31,11]⟩,⟨.and, [15,32]⟩,⟨.or, [3,4]⟩,⟨.or, [34,6]⟩,⟨.or, [35,12]⟩,⟨.and, [16,36]⟩,⟨.or, [4,5]⟩,⟨.or, [38,7]⟩,⟨.or, [39,0]⟩,⟨.and, [17,40]⟩,⟨.or, [5,6]⟩,⟨.or, [42,8]⟩,⟨.or, [43,1]⟩,⟨.and, [18,44]⟩,⟨.or, [6,7]⟩,⟨.or, [46,9]⟩,⟨.or, [47,2]⟩,⟨.and, [19,48]⟩,⟨.or, [7,8]⟩,⟨.or, [50,10]⟩,⟨.or, [51,3]⟩,⟨.and, [20,52]⟩,⟨.or, [8,9]⟩,⟨.or, [54,11]⟩,⟨.or, [55,4]⟩,⟨.and, [21,56]⟩,⟨.or, [9,10]⟩,⟨.or, [58,12]⟩,⟨.or, [59,5]⟩,⟨.and, [22,60]⟩,⟨.or, [10,11]⟩,⟨.or, [62,0]⟩,⟨.or, [63,6]⟩,⟨.and, [23,64]⟩,⟨.or, [11,12]⟩,⟨.or, [66,1]⟩,⟨.or, [67,7]⟩,⟨.and, [24,68]⟩,⟨.or, [12,0]⟩,⟨.or, [70,2]⟩,⟨.or, [71,8]⟩,⟨.and, [25,72]⟩,⟨.or, [29,33]⟩,⟨.or, [74,37]⟩,⟨.or, [75,41]⟩,⟨.or, [76,45]⟩,⟨.or, [77,49]⟩,⟨.or, [78,53]⟩,⟨.or, [79,57]⟩,⟨.or, [80,61]⟩,⟨.or, [81,65]⟩,⟨.or, [82,69]⟩,⟨.or, [83,73]⟩,⟨.or, [0,1]⟩,⟨.or, [85,3]⟩,⟨.or, [86,9]⟩,⟨.or, [84,87]⟩,⟨.or, [84,13]⟩,⟨.and, [88,89]⟩],90⟩
abbrev Q := Fin 13
def Inc (p l : Q) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Q) : Decidable (Inc p l) := by unfold Inc; infer_instance
def flags : List (Q×Q) := [(0,0),(1,0),(3,0),(9,0),(1,1),(2,1),(4,1),(10,1),(2,2),(3,2),(5,2),(11,2),(3,3),(4,3),(6,3),(12,3),(0,4),(4,4),(5,4),(7,4),(1,5),(5,5),(6,5),(8,5),(2,6),(6,6),(7,6),(9,6),(3,7),(7,7),(8,7),(10,7),(4,8),(8,8),(9,8),(11,8),(5,9),(9,9),(10,9),(12,9),(0,10),(6,10),(10,10),(11,10),(1,11),(7,11),(11,11),(12,11),(0,12),(2,12),(8,12),(12,12)]
def listTerms := flags.map fun t => [t.1.val,13+t.2.val]
def combined := (body.gates.foldl tstep T0).getD 90 []
def contained (D E : List (List Nat)) : Bool :=
  D.all fun d => E.any fun e => e.all fun i => decide (i∈d)
theorem sound {D E : List (List Nat)} (rel : contained D E=true) (x : Nat → Bool) :
    evalD x D=true → evalD x E=true := by
  simp only [contained,List.all_eq_true,List.any_eq_true,decide_eq_true_eq] at rel
  simp only [evalD,List.any_eq_true,List.all_eq_true]
  rintro ⟨d,hd,hv⟩
  obtain ⟨e,he,sub⟩ := rel d hd
  exact ⟨e,he,fun i hi => hv i (sub i hi)⟩
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem bothChecks : contained combined listTerms=true ∧ contained listTerms combined=true := by decide +kernel
theorem table (x : Fin 26 → Bool) : circuitFun 26 body x=evalD (fun i => x (Fin.ofNat 26 i)) listTerms := by
  have ok : ∀g∈body.gates, okb g=true := by decide +kernel
  have computed := (good_fold _ body.gates ok _ _ (good_init x)).2 90
  change circuitFun 26 body x=evalD (fun i => x (Fin.ofNat 26 i)) combined at computed
  rw [computed,Bool.eq_iff_iff]
  exact ⟨sound bothChecks.1 _,sound bothChecks.2 _⟩
theorem member : ∀p l:Q, (p,l)∈flags ↔ Inc p l := by decide +kernel
theorem identP : ∀p:Q,Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide +kernel
theorem identL : ∀l:Q,Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide +kernel
theorem semantic (x : Fin 26 → Bool) : (circuitFun 26 body x)=true ↔
    ∃p l:Q, Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  rw [table]
  unfold evalD
  rw [List.any_eq_true]
  constructor
  · rintro ⟨s,hs,hv⟩
    obtain ⟨⟨p,l⟩,hin,rfl⟩ := List.mem_map.mp hs
    exact ⟨p,l,(member p l).mp hin,by
      simpa only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,identP,identL] using hv⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    refine ⟨[p.val,13+l.val],List.mem_map.mpr ⟨(p,l),(member p l).mpr hi,rfl⟩,?_⟩
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,identP,identL]
    exact ⟨hp,hl⟩
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem physical : body.size=65 ∧ Monotone2 body ∧ (∀ g∈body.gates,g.inputs.Nodup) ∧
    body.lineDeg 26 (Finset.range 13)=2 ∧ body.lineDeg 26 (Finset.Ico 13 26)=2 := by
  refine ⟨rfl,(by decide +kernel : ∀ g∈body.gates,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2),?_,?_,?_⟩ <;> decide +kernel
end PEqualNP.Outside.L_meta_7911.Upper

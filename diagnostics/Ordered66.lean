import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8089.Upper
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


def before : List Gate := [⟨.or, [13,14]⟩,⟨.or, [26,18]⟩,⟨.or, [27,24]⟩,⟨.and, [13,28]⟩,⟨.or, [29,17]⟩,⟨.or, [30,23]⟩,⟨.or, [31,25]⟩,⟨.and, [0,32]⟩,⟨.and, [1,28]⟩,⟨.or, [14,15]⟩,⟨.or, [35,19]⟩,⟨.or, [36,25]⟩,⟨.or, [13,15]⟩,⟨.or, [38,16]⟩,⟨.or, [39,20]⟩,⟨.and, [3,40]⟩,⟨.or, [14,16]⟩,⟨.or, [42,17]⟩,⟨.or, [43,21]⟩,⟨.and, [4,44]⟩,⟨.or, [15,17]⟩,⟨.or, [46,18]⟩,⟨.or, [47,22]⟩,⟨.and, [5,48]⟩,⟨.or, [16,18]⟩,⟨.or, [50,19]⟩,⟨.or, [51,23]⟩,⟨.and, [6,52]⟩,⟨.or, [17,19]⟩,⟨.or, [54,20]⟩,⟨.or, [55,24]⟩,⟨.and, [7,56]⟩,⟨.or, [18,20]⟩,⟨.or, [58,21]⟩,⟨.or, [59,25]⟩,⟨.and, [8,60]⟩,⟨.or, [13,19]⟩,⟨.or, [62,21]⟩,⟨.or, [63,22]⟩,⟨.and, [9,64]⟩,⟨.or, [14,20]⟩,⟨.or, [66,22]⟩,⟨.or, [67,23]⟩,⟨.and, [10,68]⟩,⟨.or, [15,21]⟩,⟨.or, [70,23]⟩,⟨.or, [71,24]⟩,⟨.and, [11,72]⟩,⟨.or, [16,22]⟩,⟨.or, [74,24]⟩,⟨.or, [75,25]⟩,⟨.and, [12,76]⟩,⟨.or, [33,34]⟩,⟨.or, [78,41]⟩,⟨.or, [79,45]⟩,⟨.or, [80,49]⟩,⟨.or, [81,53]⟩,⟨.or, [82,57]⟩,⟨.or, [83,61]⟩,⟨.or, [84,65]⟩,⟨.or, [85,69]⟩,⟨.or, [86,73]⟩,⟨.or, [87,77]⟩,⟨.or, [88,2]⟩,⟨.or, [88,37]⟩]
def u : ℕ := 89
def v : ℕ := 90
def body : Circuit := ⟨before++[⟨.and,[u,v]⟩],26+before.length⟩
abbrev Q := Fin 13
def Inc (p l : Q) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Q) : Decidable (Inc p l) := by unfold Inc; infer_instance
def flags : List (Q×Q) := [(0,0),(1,0),(3,0),(9,0),(1,1),(2,1),(4,1),(10,1),(2,2),(3,2),(5,2),(11,2),(3,3),(4,3),(6,3),(12,3),(0,4),(4,4),(5,4),(7,4),(1,5),(5,5),(6,5),(8,5),(2,6),(6,6),(7,6),(9,6),(3,7),(7,7),(8,7),(10,7),(4,8),(8,8),(9,8),(11,8),(5,9),(9,9),(10,9),(12,9),(0,10),(6,10),(10,10),(11,10),(1,11),(7,11),(11,11),(12,11),(0,12),(2,12),(8,12),(12,12)]
def listTerms := flags.map fun t => [t.1.val,13+t.2.val]
def combined := (body.gates.foldl tstep T0).getD 91 []
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
  have computed := (good_fold _ body.gates ok _ _ (good_init x)).2 91
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
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
attribute [local instance] gateOpDecEq

def F (x : Fin 26 → Bool) : Prop := ∃ p l : Q, (p-l)^4=p-l ∧ x (Fin.castAdd 13 p)=true ∧
  x (Fin.natAdd 13 l)=true
def row (b : Bool) (i : Fin 26) : Bool := if i.val<13 then b else !b
private theorem rowP (b : Bool) (p : Q) : row b (Fin.castAdd 13 p)=b := by simp [row,p.isLt]
private theorem rowL (b : Bool) (l : Q) : row b (Fin.natAdd 13 l)=!b := by simp [row]
private theorem maxRow (b : Bool) : Maximal (fun x => ¬ F x) (row b) := by
  constructor
  · rintro ⟨p,l,_,hp,hl⟩
    rw [rowP] at hp
    rw [rowL] at hl
    cases b <;> simp_all
  · intro y no le i
    refine Fin.addCases ?_ ?_ i
    · intro p
      rw [rowP]
      cases b
      · cases hy : y (Fin.castAdd 13 p)
        · rfl
        · have t := le (Fin.natAdd 13 p)
          rw [rowL] at t
          have ly : y (Fin.natAdd 13 p)=true := by cases h : y (Fin.natAdd 13 p) <;> simp_all
          exact (no ⟨p,p,by simp,hy,ly⟩).elim
      · cases y (Fin.castAdd 13 p) <;> decide
    · intro l
      rw [rowL]
      cases b
      · cases y (Fin.natAdd 13 l) <;> decide
      · cases hy : y (Fin.natAdd 13 l)
        · rfl
        · have t := le (Fin.castAdd 13 l)
          rw [rowP] at t
          have py : y (Fin.castAdd 13 l)=true := by cases h : y (Fin.castAdd 13 l) <;> simp_all
          exact (no ⟨l,l,by simp,py,hy⟩).elim

theorem law (x : Fin 26 → Bool) :
    ((wireVal 26 body u x && wireVal 26 body v x)=true) ↔ F x := by
  have w := List.foldl wstep (List.ofFn x) before
  have len : w.length=26+before.length := by
    change (List.foldl wstep (List.ofFn x) before).length=_
    have L (gs : List Gate) (xs : List Bool) : (gs.foldl wstep xs).length=xs.length+gs.length := by
      induction gs generalizing xs with
      | nil => simp
      | cons g gs ih => simp [List.foldl,ih,wstep_len,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    simp [L]
  have full : body.wires (List.ofFn x)=wstep w ⟨.and,[u,v]⟩ := by
    change (before++[_]).foldl wstep (List.ofFn x)=_
    rw [List.foldl_append]; rfl
  have hu : u<w.length := len.symm ▸ (by decide : u<26+before.length)
  have hv : v<w.length := len.symm ▸ (by decide : v<26+before.length)
  have out : circuitFun 26 body x=(wireVal 26 body u x && wireVal 26 body v x) := by
    change (body.wires _).getD (26+before.length) false=((body.wires _).getD u false && (body.wires _).getD v false)
    rw [full,wstep_last _ _ _ len.symm,wstep_lt _ _ _ hu,wstep_lt _ _ _ hv]
    simp [GateOp.eval]
  have inc : ∀p l:Q, Inc p l ↔ (p-l)^4=p-l := by decide +kernel
  rw [←out,semantic]
  exact exists_congr (fun p => exists_congr (fun l => and_congr_left (fun _ => inc p l)))

set_option maxRecDepth 18000 in
theorem laws : IsAO2 26 body ∧ (∀ g∈body.gates,g.inputs.Nodup) ∧
  InCone 26 body 3 65 ∧ (gateAt body 3).op=.and ∧ (gateAt body 65).op=.and ∧
  wireVal 26 body 29 (row false)=true ∧
  wireVal 26 body 29 (pairInput 0 13)=true ∧ wireVal 26 body 91 (pairInput 0 13)=true ∧
  (∀ b : Fin 2, wireVal 26 body (opnd body 3 b) (pairInput 0 0)=false) ∧
  (∀ b : Fin 2, wireVal 26 body (opnd body 65 b) (pairInput 13 13)=false) ∧
  (∀ b : Bool, wireVal 26 body u (row b)=b ∧ wireVal 26 body v (row b)=!b) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem relaxed : ¬ (∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 x3 : ℕ),   have x4 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x1 ++ [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x2, x3] : PEqualNP.CircuitLowerBounds.Gate }], output := (26 : ℕ) + x1.length : PEqualNP.CircuitLowerBounds.Circuit };   have x5 : (Fin (26 : ℕ) → Bool) → Prop := fun (x5 : Fin (26 : ℕ) → Bool) => ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 - x7) ^ (4 : ℕ) = x6 - x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true;   have x6 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x4;   have x7 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4;   have x8 : ℕ → Fin (26 : ℕ) → Prop := fun (x8 : ℕ) (x9 : Fin (26 : ℕ)) => (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x8 = x1.length ∨ x7 x8 x1.length) ∧ x6 ((26 : ℕ) + x8) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧ ∀ (x10 : Fin (2 : ℕ)), x6 (PEqualNP.TopForm.opnd x4 x8 x10) (PEqualNP.EdgeOwnership.pairInput x9 x9) = Bool.false;   x1.length = (65 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 → (∀ x11 ∈ x4.gates, x11.inputs.Nodup) → (∃ x12 < x1.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x13 : Fin (26 : ℕ) → Bool), Maximal (fun (x14 : Fin (26 : ℕ) → Bool) => ¬x5 x14) x13 ∧ x6 ((26 : ℕ) + x12) x13 = Bool.true) → (∃ (x13 : ℕ) (x14 : ℕ), x7 x13 x14 ∧ x8 x13 (0 : Fin (26 : ℕ)) ∧ x8 x14 (13 : Fin (26 : ℕ))) → (∀ (x14 : Fin (26 : ℕ) → Bool), Minimal x5 x14 → x6 x2 x14 = Bool.true ∧ x6 x3 x14 = Bool.true) → (∀ (x15 : Fin (26 : ℕ) → Bool), Maximal (fun (x16 : Fin (26 : ℕ) → Bool) => ¬x5 x16) x15 → (x6 x2 x15 && x6 x3 x15) = Bool.false) → (∀ (x16 : Bool), ∃ (x17 : Fin (26 : ℕ) → Bool), Maximal (fun (x18 : Fin (26 : ℕ) → Bool) => ¬x5 x18) x17 ∧ x6 x2 x17 = x16 ∧ x6 x3 x17 = !x16) → False) := by
  intro deny
  have h := deny before u v
  change before.length=65 → IsAO2 26 body → _ at h
  obtain ⟨ao,nodup,cone,opj,opk,dirty,pairj,pairk,sj,sk,rows⟩ := laws
  apply h rfl ao nodup
  · exact ⟨3,by decide,opj,row false,maxRow false,dirty⟩
  · exact ⟨3,65,cone,⟨opj,Or.inr cone,pairj,sj⟩,⟨opk,Or.inl rfl,pairk,sk⟩⟩
  · intro x mx
    have on := (law x).mpr mx.prop
    simpa only [Bool.and_eq_true] using on
  · intro x mx
    cases e : wireVal 26 body u x && wireVal 26 body v x
    · exact e
    · exact (mx.prop ((law x).mp e)).elim
  · intro b
    exact ⟨row b,maxRow b,(rows b).1,(rows b).2⟩

end PEqualNP.Outside.L_meta_8089.Upper

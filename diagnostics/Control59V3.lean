import PEqualNP.Defs

namespace Punctured9450
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



open PEqualNP.TopForm
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
def hintT : List (List (List Nat)) := T0 ++ [[[1],[2]]]
def hinput (x : Fin 26 → Bool) := List.ofFn x ++ [x 1 || x 2]
theorem hint_good (x : Fin 26 → Bool) :
    Good (fun i => x (Fin.ofNat 26 i)) (hinput x) hintT := by
  refine ⟨by simp [hinput,hintT,T0_len],fun i => ?_⟩
  rcases lt_trichotomy i 26 with lt|eq|gt
  · unfold hinput hintT
    rw [List.getD_append _ _ _ _ (by simpa using lt),tsnoc_lt _ _ _ (by rw [T0_len]; exact lt)]
    exact (good_init x).2 i
  · subst i
    unfold hinput hintT
    rw [tsnoc_eq _ _ _ T0_len.symm]
    have last (L : List Bool) (v : Bool) : (L++[v]).getD L.length false=v := by
      simp [List.getD_eq_getElem?_getD]
    have q := last (List.ofFn x) (x 1 || x 2)
    rw [List.length_ofFn] at q
    rw [q]
    simp [evalD]
  · have h : (hinput x).length ≤ i := by simp [hinput]; omega
    have t : hintT.length ≤ i := by simp [hintT,T0_len]; omega
    rw [List.getD_eq_default _ _ h,List.getD_eq_default _ _ t]
    rfl
def Inc (p l : Fin 13) := l ≠ 1 ∧ (p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9)
instance (p l : Fin 13) : Decidable (Inc p l) := by unfold Inc; infer_instance
def F (x : Fin 26 → Bool) := ∃p l:Fin 13,Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
def B : Circuit := ⟨[⟨.or,[0,1]⟩,⟨.or,[27,3]⟩,⟨.or,[28,9]⟩,⟨.and,[29,13]⟩,⟨.or,[2,3]⟩,⟨.or,[31,5]⟩,⟨.or,[32,11]⟩,⟨.and,[33,15]⟩,⟨.or,[3,4]⟩,⟨.or,[35,6]⟩,⟨.or,[36,12]⟩,⟨.and,[37,16]⟩,⟨.or,[0,4]⟩,⟨.or,[39,5]⟩,⟨.or,[40,7]⟩,⟨.and,[41,17]⟩,⟨.or,[1,5]⟩,⟨.or,[43,6]⟩,⟨.or,[44,8]⟩,⟨.and,[45,18]⟩,⟨.or,[2,6]⟩,⟨.or,[47,7]⟩,⟨.or,[48,9]⟩,⟨.and,[49,19]⟩,⟨.or,[3,7]⟩,⟨.or,[51,8]⟩,⟨.or,[52,10]⟩,⟨.and,[53,20]⟩,⟨.or,[4,8]⟩,⟨.or,[55,9]⟩,⟨.or,[56,11]⟩,⟨.and,[57,21]⟩,⟨.or,[5,9]⟩,⟨.or,[59,10]⟩,⟨.or,[60,12]⟩,⟨.and,[61,22]⟩,⟨.or,[0,6]⟩,⟨.or,[63,10]⟩,⟨.or,[64,11]⟩,⟨.and,[65,23]⟩,⟨.or,[1,7]⟩,⟨.or,[67,11]⟩,⟨.or,[68,12]⟩,⟨.and,[69,24]⟩,⟨.or,[0,2]⟩,⟨.or,[71,8]⟩,⟨.or,[72,12]⟩,⟨.and,[73,25]⟩],0⟩
abbrev W := Fin (27+B.size)
def a : W := 30
def rest : List W := [34, 38, 42, 46, 50, 54, 58, 62, 66, 70, 74]
def outputs := a::rest
def flags : List (Fin 13 × Fin 13) := [(0, 0), (1, 0), (3, 0), (9, 0), (2, 2), (3, 2), (5, 2), (11, 2), (3, 3), (4, 3), (6, 3), (12, 3), (0, 4), (4, 4), (5, 4), (7, 4), (1, 5), (5, 5), (6, 5), (8, 5), (2, 6), (6, 6), (7, 6), (9, 6), (3, 7), (7, 7), (8, 7), (10, 7), (4, 8), (8, 8), (9, 8), (11, 8), (5, 9), (9, 9), (10, 9), (12, 9), (0, 10), (6, 10), (10, 10), (11, 10), (1, 11), (7, 11), (11, 11), (12, 11), (0, 12), (2, 12), (8, 12), (12, 12)]

def table := B.gates.foldl tstep hintT
def terms := outputs.flatMap fun i => table.getD i.val []
def targetTerms := flags.map fun t => [t.1.val,13+t.2.val]
theorem checked : terms=targetTerms := by decide +kernel
theorem good (x : Fin 26 → Bool) : Good (fun i => x (Fin.ofNat 26 i)) (B.wires (hinput x)) table :=
  good_fold _ B.gates (by decide +kernel) _ _ (hint_good x)
theorem reflects (x : Fin 26 → Bool) :
    (outputs.any fun i => (B.wires (hinput x)).getD i.val false) =
    evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true,evalD,terms,List.mem_flatMap]
  constructor
  · rintro ⟨w,hw,h⟩
    rw [(good x).2 w.val] at h
    obtain ⟨t,ht,val⟩ := List.any_eq_true.mp h
    exact ⟨t,⟨w,hw,ht⟩,val⟩
  · rintro ⟨t,⟨w,hw,ht⟩,val⟩
    exact ⟨w,hw,((good x).2 w.val).trans (List.any_eq_true.mpr ⟨t,ht,val⟩)⟩
theorem flag_mem : ∀p l:Fin 13,(p,l)∈flags ↔ Inc p l := by decide +kernel
theorem pointIdx : ∀p:Fin 13,Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide +kernel
theorem lineIdx : ∀l:Fin 13,Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide +kernel
theorem agrees (x : Fin 26 → Bool) : (outputs.any fun i => (B.wires (hinput x)).getD i.val false)=true ↔ F x := by
  rw [reflects,checked]
  unfold evalD
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t,ht,hv⟩
    obtain ⟨⟨p,l⟩,hin,rfl⟩ := List.mem_map.mp ht
    exact ⟨p,l,(flag_mem p l).mp hin,by
      simpa only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,pointIdx,lineIdx] using hv⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    refine ⟨[p.val,13+l.val],List.mem_map.mpr ⟨(p,l),(flag_mem p l).mpr hi,rfl⟩,?_⟩
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,pointIdx,lineIdx]
    exact ⟨hp,hl⟩
theorem within59 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x3 ≠ (1 : Fin (13 : ℕ)) ∧ (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool) (x4 : Fin ((27 : ℕ) + x2.size)) (x5 : List (Fin ((27 : ℕ) + x2.size))),   x5 ≠ [] ∧     (x4 :: x5).Nodup ∧       x2.size + x5.length ≤ (59 : ℕ) ∧         PEqualNP.TopForm.IsAO2 (27 : ℕ) x2 ∧           (∀ x6 ∈ x2.gates, x6.inputs.Nodup) ∧             ∀ (x6 : Fin (26 : ℕ) → Bool),               Minimal x1 x6 ∨ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x1 x7) x6 →                 have x8 : List Bool := x2.wires (List.ofFn x6 ++ [x6 (1 : Fin (26 : ℕ)) || x6 (2 : Fin (26 : ℕ))]);                 (if x3 = Bool.true then (x4 :: x5).any fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false else (x4 :: x5).all fun (x9 : Fin ((27 : ℕ) + x2.size)) => x8.getD (↑x9) Bool.false) = Bool.true ↔ x1 x6 := by
  dsimp only
  refine ⟨B,true,a,rest,by decide,by decide +kernel,by decide,by decide +kernel,by decide +kernel,?_⟩
  intro x _
  change (outputs.any fun i => (B.wires (hinput x)).getD i.val false)=true ↔ _
  rw [agrees]
  constructor
  · rintro ⟨p,l,⟨hn,he⟩,hp,hl⟩
    exact ⟨p,l,hn,he,hp,hl⟩
  · rintro ⟨p,l,hn,he,hp,hl⟩
    exact ⟨p,l,⟨hn,he⟩,hp,hl⟩
end Punctured9450

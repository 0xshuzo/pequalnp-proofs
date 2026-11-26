import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8123.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm
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


def C : Circuit := ⟨[⟨.or,[21,26]⟩,⟨.or,[42,28]⟩,⟨.or,[43,38]⟩,⟨.or,[44,41]⟩,⟨.and,[0,45]⟩,⟨.or,[21,22]⟩,⟨.or,[47,27]⟩,⟨.or,[48,29]⟩,⟨.or,[49,39]⟩,⟨.and,[1,50]⟩,⟨.or,[22,23]⟩,⟨.or,[52,28]⟩,⟨.or,[53,30]⟩,⟨.or,[54,40]⟩,⟨.and,[2,55]⟩,⟨.or,[23,24]⟩,⟨.or,[57,29]⟩,⟨.or,[58,31]⟩,⟨.or,[59,41]⟩,⟨.and,[3,60]⟩,⟨.or,[21,24]⟩,⟨.or,[62,25]⟩,⟨.or,[63,30]⟩,⟨.or,[64,32]⟩,⟨.and,[4,65]⟩,⟨.or,[22,25]⟩,⟨.or,[67,26]⟩,⟨.or,[68,31]⟩,⟨.or,[69,33]⟩,⟨.and,[5,70]⟩,⟨.or,[23,26]⟩,⟨.or,[72,27]⟩,⟨.or,[73,32]⟩,⟨.or,[74,34]⟩,⟨.and,[6,75]⟩,⟨.or,[24,27]⟩,⟨.or,[77,28]⟩,⟨.or,[78,33]⟩,⟨.or,[79,35]⟩,⟨.and,[7,80]⟩,⟨.or,[25,28]⟩,⟨.or,[82,29]⟩,⟨.or,[83,34]⟩,⟨.or,[84,36]⟩,⟨.and,[8,85]⟩,⟨.or,[26,29]⟩,⟨.or,[87,30]⟩,⟨.or,[88,35]⟩,⟨.or,[89,37]⟩,⟨.and,[9,90]⟩,⟨.or,[27,30]⟩,⟨.or,[92,31]⟩,⟨.or,[93,36]⟩,⟨.or,[94,38]⟩,⟨.and,[10,95]⟩,⟨.or,[28,31]⟩,⟨.or,[97,32]⟩,⟨.or,[98,37]⟩,⟨.or,[99,39]⟩,⟨.and,[11,100]⟩,⟨.or,[29,32]⟩,⟨.or,[102,33]⟩,⟨.or,[103,38]⟩,⟨.or,[104,40]⟩,⟨.and,[12,105]⟩,⟨.or,[30,33]⟩,⟨.or,[107,34]⟩,⟨.or,[108,39]⟩,⟨.or,[109,41]⟩,⟨.and,[13,110]⟩,⟨.or,[21,31]⟩,⟨.or,[112,34]⟩,⟨.or,[113,35]⟩,⟨.or,[114,40]⟩,⟨.and,[14,115]⟩,⟨.or,[22,32]⟩,⟨.or,[117,35]⟩,⟨.or,[118,36]⟩,⟨.or,[119,41]⟩,⟨.and,[15,120]⟩,⟨.or,[21,23]⟩,⟨.or,[122,33]⟩,⟨.or,[123,36]⟩,⟨.or,[124,37]⟩,⟨.and,[16,125]⟩,⟨.or,[22,24]⟩,⟨.or,[127,34]⟩,⟨.or,[128,37]⟩,⟨.or,[129,38]⟩,⟨.and,[17,130]⟩,⟨.or,[23,25]⟩,⟨.or,[132,35]⟩,⟨.or,[133,38]⟩,⟨.or,[134,39]⟩,⟨.and,[18,135]⟩,⟨.or,[24,26]⟩,⟨.or,[137,36]⟩,⟨.or,[138,39]⟩,⟨.or,[139,40]⟩,⟨.and,[19,140]⟩,⟨.or,[25,27]⟩,⟨.or,[142,37]⟩,⟨.or,[143,40]⟩,⟨.or,[144,41]⟩,⟨.and,[20,145]⟩,⟨.or,[46,51]⟩,⟨.or,[147,56]⟩,⟨.or,[148,61]⟩,⟨.or,[149,66]⟩,⟨.or,[150,71]⟩,⟨.or,[151,76]⟩,⟨.or,[152,81]⟩,⟨.or,[153,86]⟩,⟨.or,[154,91]⟩,⟨.or,[155,96]⟩,⟨.or,[156,101]⟩,⟨.or,[157,106]⟩,⟨.or,[158,111]⟩,⟨.or,[159,116]⟩,⟨.or,[160,121]⟩,⟨.or,[161,126]⟩,⟨.or,[162,131]⟩,⟨.or,[163,136]⟩,⟨.or,[164,141]⟩,⟨.or,[165,146]⟩],166⟩
def terms := (C.gates.foldl tstep T0).getD C.output []
def listTerms : List (List Nat) := [[0, 21], [0, 26], [0, 28], [0, 38], [0, 41], [1, 21], [1, 22], [1, 27], [1, 29], [1, 39], [2, 22], [2, 23], [2, 28], [2, 30], [2, 40], [3, 23], [3, 24], [3, 29], [3, 31], [3, 41], [4, 21], [4, 24], [4, 25], [4, 30], [4, 32], [5, 22], [5, 25], [5, 26], [5, 31], [5, 33], [6, 23], [6, 26], [6, 27], [6, 32], [6, 34], [7, 24], [7, 27], [7, 28], [7, 33], [7, 35], [8, 25], [8, 28], [8, 29], [8, 34], [8, 36], [9, 26], [9, 29], [9, 30], [9, 35], [9, 37], [10, 27], [10, 30], [10, 31], [10, 36], [10, 38], [11, 28], [11, 31], [11, 32], [11, 37], [11, 39], [12, 29], [12, 32], [12, 33], [12, 38], [12, 40], [13, 30], [13, 33], [13, 34], [13, 39], [13, 41], [14, 21], [14, 31], [14, 34], [14, 35], [14, 40], [15, 22], [15, 32], [15, 35], [15, 36], [15, 41], [16, 21], [16, 23], [16, 33], [16, 36], [16, 37], [17, 22], [17, 24], [17, 34], [17, 37], [17, 38], [18, 23], [18, 25], [18, 35], [18, 38], [18, 39], [19, 24], [19, 26], [19, 36], [19, 39], [19, 40], [20, 25], [20, 27], [20, 37], [20, 40], [20, 41]]

theorem checkedTerms : terms = listTerms := by decide +kernel

theorem goodOps : ∀ g ∈ C.gates, okb g=true := by decide +kernel

theorem reflection (x : Fin 42 → Bool) : C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 42 i)) terms := by
  exact (good_fold _ C.gates goodOps _ _ (good_init x)).2 C.output

theorem mono : Monotone2 C := fun g hg => okb_spec g (goodOps g hg)

def adjacent (p l : Fin 42) : Prop := p.val<21 ∧ 21≤l.val ∧ (l.val+21-p.val)%21∈([0,5,7,17,20]:List Nat)
instance (p l : Fin 42) : Decidable (adjacent p l) := by unfold adjacent; infer_instance
def hasEdge (x : Fin 42 → Bool) : Prop := ∃p l,adjacent p l ∧ x p=true ∧ x l=true
def rawEdge (p l : Nat) := p < 21 ∧ 21 ≤ l ∧ l < 42 ∧ (l+21-p)%21 ∈ ([0,5,7,17,20]:List Nat)
instance (p l : Nat) : Decidable (rawEdge p l) := by unfold rawEdge; infer_instance

theorem soundTerms : listTerms.all (fun c => c.any fun p => c.any fun l => decide (rawEdge p l))=true := by
  decide +kernel

theorem coverTerms : ∀ p l : Fin 42, adjacent p l →
    listTerms.any (fun c => c.all fun i => decide (i=p.val ∨ i=l.val))=true := by
  decide +kernel

theorem correct (x : Fin 42 → Bool) : C.eval (List.ofFn x)=true ↔ hasEdge x := by
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
    · simpa only [hp'] using List.all_eq_true.mp active p hp
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

def right (K : Circuit) := ∀ x : Fin 42 → Bool,K.eval (List.ofFn x)=true ↔ hasEdge x
def valid (K : Circuit) := IsAO2 42 K ∧ right K
def isOr (g : Gate) : Bool := GateOp.casesOn g.op false true false (fun _=>false) false
def cost (K : Circuit) := K.gates.countP isOr
def line (i : Nat) := decide (21≤i)
def edges : List (Nat × Nat) := (List.range 21).flatMap (fun p => ([0,5,7,17,20]:List Nat).map (fun k=>(p,21+(p+k)%21)))
def bad (K : Circuit) := doubleReread K 42 line edges
def best (K : Circuit) := ∀ D,valid D → cost K≤cost D
def Descent := ∀ K,valid K → best K → bad K≠[] → ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length

theorem baseline : valid C ∧ cost C=104 ∧ bad C=[] := by
  exact ⟨⟨by decide +kernel,correct⟩,by decide +kernel,by decide +kernel⟩

theorem clean_optimum_iff : Descent ↔ ∃K,valid K ∧ best K ∧ bad K=[] := by
  classical
  constructor
  · intro descent
    have existsCost : ∃s,∃K,valid K ∧ cost K=s := ⟨cost C,C,baseline.1,rfl⟩
    obtain ⟨A,va,ca⟩ := Nat.find_spec existsCost
    have least : best A := fun D vd => ca.le.trans (Nat.find_min' existsCost ⟨D,vd,rfl⟩)
    have sizes : ∃s,∃B,valid B ∧ best B ∧ (bad B).length=s := ⟨_,A,va,least,rfl⟩
    obtain ⟨B,vb,mb,bLen⟩ := Nat.find_spec sizes
    refine ⟨B,vb,mb,?_⟩
    by_contra nonempty
    obtain ⟨D,vd,cheap,short⟩ := descent B vb mb nonempty
    have md : best D := fun E ve => cheap.trans (mb E ve)
    have bound := Nat.find_min' sizes ⟨D,vd,md,rfl⟩
    omega
  · rintro ⟨D,vd,md,clean⟩ K vk _ nb
    refine ⟨D,vd,md K vk,?_⟩
    rw [clean]
    exact List.length_pos_iff.mpr nb

theorem any_104 (K : Circuit) (large : 104≤cost K) (nb : bad K≠[]) :
    ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length := by
  refine ⟨C,baseline.1,baseline.2.1.le.trans large,?_⟩
  rw [baseline.2.2]
  exact List.length_pos_iff.mpr nb

theorem low_cost_suffices (hard : ∀ K,valid K → best K → cost K≤103 → bad K≠[] →
      ∃D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length) : Descent := by
  intro K vk mini db
  rcases le_or_gt 104 (cost K) with big|small
  · exact any_104 K big db
  · exact hard K vk mini (by omega) db

end PEqualNP.Outside.L_meta_8123.Work
namespace PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.CircuitLowerBounds

-- evaluation toolkit (step, val, val_snoc, val_ge, val_lt) copied from the L_meta_2986 / L_meta_1406 files

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma val_ge {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : n + gs.length ≤ i) :
    val gs x i = false := by
  unfold val
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl


lemma val_lt {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = x ⟨i, hi⟩ := by
  induction gs using List.reverseRecOn with
  | nil =>
    rw [val_nil]
    simp [hi]
  | append_singleton gs g ih =>
    rw [val_snoc, if_neg (by omega)]
    exact ih

lemma val_in {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    val gs x i = val ([] : List Gate) x i := by
  rw [val_lt gs x i hi, val_lt [] x i hi]

/-- re-indexing of the wires: the first `a` inputs stay, everything else moves up by `n`. -/
def phi (a n : ℕ) (w : ℕ) : ℕ := if w < a then w else w + n

def rho (a n : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (phi a n)⟩

lemma phi_lt (a n : ℕ) (ha : a ≤ n) (i : ℕ) (hi : i < n) : phi a n i < n + n := by
  unfold phi
  split_ifs <;> omega

def zof (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) : Fin n → Bool :=
  fun i => x ⟨phi a n i.val, phi_lt a n ha i.val i.isLt⟩

lemma reidx (a n : ℕ) (ha : a ≤ n) (x : Fin (n + n) → Bool) (z : Fin n → Bool)
    (hz : ∀ (i : ℕ) (hi : i < n) (h2 : phi a n i < n + n), z ⟨i, hi⟩ = x ⟨phi a n i, h2⟩) :
    ∀ (gs : List Gate) (w : ℕ), val (gs.map (rho a n)) x (phi a n w) = val gs z w := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro w
    simp only [List.map_nil]
    rw [val_nil, val_nil]
    by_cases hw : w < n
    · have hp := phi_lt a n ha w hw
      rw [dif_pos hp, dif_pos hw]
      exact (hz w hw hp).symm
    · have hp : ¬ phi a n w < n + n := by
        unfold phi
        split_ifs <;> omega
      rw [dif_neg hp, dif_neg hw]
  | append_singleton gs g ih =>
    intro w
    rw [List.map_append, List.map_cons, List.map_nil, val_snoc, val_snoc, List.length_map]
    have key : phi a n w = n + n + gs.length ↔ w = n + gs.length := by
      unfold phi
      split_ifs <;> omega
    by_cases hw : w = n + gs.length
    · rw [if_pos (key.2 hw), if_pos hw]
      show g.op.eval (List.map (fun j => val (gs.map (rho a n)) x j) (g.inputs.map (phi a n))) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih j
    · rw [if_neg (fun h => hw (key.1 h)), if_neg hw]
      exact ih w

/-- well-formed gate lists: AND/OR, two inputs, each input earlier. -/
def WF (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < m + j

lemma wf_two (m : ℕ) (gs : List Gate) (a b c : ℕ) (hwf : WF m gs)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    WF m (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) := by
  intro j g hj
  rcases lt_or_ge j gs.length with h | h
  · rw [List.getElem?_append_left h] at hj
    exact hwf j g hj
  · rw [List.getElem?_append_right h] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = gs.length + k := ⟨j - gs.length, by omega⟩
    rw [Nat.add_sub_cancel_left] at hj
    match k, hj with
    | 0, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inl rfl, rfl, by intro i hi; simp at hi; omega⟩
    | 1, hj =>
      simp at hj
      subst hj
      exact ⟨Or.inr rfl, rfl, by intro i hi; simp at hi; omega⟩
    | k + 2, hj => simp at hj

lemma val_two_new {m : ℕ} (gs : List Gate) (a b c : ℕ) (x : Fin m → Bool)
    (ha : a < m + gs.length) (hb : b < m + gs.length) (hc : c < m + gs.length) :
    val (gs ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [c, m + gs.length]⟩]) x (m + gs.length + 1)
      = (val gs x c || (val gs x a && val gs x b)) := by
  have happ : gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [c, m + gs.length]⟩]
      = (gs ++ [⟨GateOp.and, [a, b]⟩]) ++ [⟨GateOp.or, [c, m + gs.length]⟩] := by simp
  have hl1 : (gs ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length = gs.length + 1 := by simp
  rw [happ, val_snoc, if_pos (by omega)]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
    Bool.or_false]
  rw [val_snoc, if_neg (by omega), val_snoc, if_pos rfl]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
    Bool.and_true]

lemma isAO2_of_wf (m : ℕ) (gs : List Gate) (out : ℕ) (hwf : WF m gs) :
    PEqualNP.TopForm.IsAO2 m (⟨gs, out⟩ : Circuit) := by
  unfold PEqualNP.TopForm.IsAO2
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).1
  · intro j hj i hi
    have hj' : j < gs.length := hj
    have hi' : i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs := hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact (hwf j _ (List.getElem?_eq_getElem hj')).2.2 i hi'
  · intro g hg
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
    exact (hwf j g hj).2.1

end PEqualNP.Outside.L_meta_3264_aux
namespace PEqualNP.Outside.L_meta_3568.Slice

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.ReadK

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl


end PEqualNP.Outside.L_meta_3568.Slice
namespace PEqualNP.Outside.L_meta_8123.Work
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.Outside.L_meta_3264_aux
open PEqualNP.Outside.L_meta_3568.Slice
set_option maxRecDepth 32768
set_option maxHeartbeats 0

def adjoin (K : Circuit) (e : Nat × Nat) : Circuit :=
  ⟨K.gates ++ [⟨.and,[e.1,e.2]⟩,⟨.or,[K.output,42+K.gates.length]⟩],42+K.gates.length+1⟩

theorem cost_adjoin (K : Circuit) (e : Nat × Nat) : cost (adjoin K e)=cost K+1 := by
  simp [cost,adjoin,isOr,List.countP_append]

theorem wfOf {n : Nat} {K : Circuit} (ao : IsAO2 n K) : WF n K.gates := by
  intro j g hg
  have hj : j<K.gates.length := by
    by_contra! far
    rw [List.getElem?_eq_none far] at hg
    contradiction
  have mem := List.mem_of_getElem? hg
  refine ⟨ao.1 _ mem,ao.2.2 _ mem,?_⟩
  intro v hv
  apply ao.2.1 j hj v
  change v∈(K.gates.getD j _).inputs
  simpa [List.getD_eq_getElem?_getD,hg] using hv

theorem bounds : ∀e∈edges,e.1<42 ∧ e.2<42 := by decide +kernel

theorem legal_adjoin {K : Circuit} (ao : IsAO2 42 K) (out : K.output<42+K.gates.length) {e}
    (he : e∈edges) : IsAO2 42 (adjoin K e) := by
  have h := bounds e he
  exact isAO2_of_wf _ _ _ (wf_two 42 K.gates e.1 e.2 K.output (wfOf ao) (by omega) (by omega) out)

theorem eval_adjoin (K : Circuit) (out : K.output<42+K.gates.length) {e} (he:e∈edges)
    (x : Fin 42 → Bool) : (adjoin K e).eval (List.ofFn x) =
      (K.eval (List.ofFn x) || (x ⟨e.1,(bounds e he).1⟩ && x ⟨e.2,(bounds e he).2⟩)) := by
  have h := bounds e he
  have eq := val_two_new K.gates e.1 e.2 K.output x (by omega) (by omega) out
  rw [val_lt _ _ _ h.1,val_lt _ _ _ h.2] at eq
  exact eq

def colour (b : Bool) : Nat→Bool := if b then line else (fun i=> !line i)
def init (b : Bool) (q : Nat × Nat) : List (Bool × Bool) :=
  (((List.range 42).map fun i => i==q.1 || i==q.2).zipIdx).map
    fun (x,i)=>if colour b i then (false,x) else (x,false)
private theorem init_len (b : Bool) (q) : (init b q).length=42 := by simp [init]
private theorem marked : ∀e∈edges,∀b : Bool,
    ((init b e).getD e.1 (false,false),(init b e).getD e.2 (false,false)) =
    (if b then ((true,false),(false,true)) else ((false,true),(true,false))) := by decide +kernel

def single (K : Circuit) (b : Bool) (q : Nat × Nat) := lineSingle K 42 (colour b) q.1 q.2
def dirty (K : Circuit) (q : Nat × Nat) := !(single K true q) && !(single K false q)
theorem bad_filter (K : Circuit) : bad K = edges.filter (dirty K) := rfl

private theorem finalGet {α : Type} (w : List α) (a d : α) (i : Nat) (eq:i=w.length) :
    (w++[a]).getD i d=a := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [show i-w.length=0 by omega]
  rfl

private theorem single_adjoin (K : Circuit) (out : K.output<42+K.gates.length) (e q : Nat × Nat)
    (b : Bool) :
    single (adjoin K e) b q =
      (single K b q || (linStep (scan linStep K.gates (init b q)) ⟨.and,[e.1,e.2]⟩).2) := by
  let w := scan linStep K.gates (init b q)
  let a := linStep w ⟨.and,[e.1,e.2]⟩
  have len : w.length=42+K.gates.length := by simp [w,scan_length,init_len]
  change ((scan linStep (K.gates ++ [⟨.and,[e.1,e.2]⟩,⟨.or,[K.output,42+K.gates.length]⟩]) (init b q)).getD
    (42+K.gates.length+1) (false,false)).2 = _
  rw [scan_append]
  change ((w ++ [a] ++ [linStep (w++[a]) ⟨.or,[K.output,42+K.gates.length]⟩]).getD
    (42+K.gates.length+1) (false,false)).2 = _
  rw [finalGet _ _ _ _ (by simp [len])]
  simp only [linStep,List.map_cons,List.map_nil,List.any_cons,List.any_nil,Bool.or_false]
  rw [List.getD_append _ _ _ _ (show K.output < w.length by omega),finalGet w a _ _ len.symm]
  rfl

theorem protects (K : Circuit) (out : K.output<42+K.gates.length) {e} (he:e∈edges) (b : Bool) :
    single (adjoin K e) b e=true := by
  rw [single_adjoin K out e e b]
  have bounds' := bounds e he
  have seen (v : Nat) (hv : v<42) :
      (scan linStep K.gates (init b e)).getD v (false,false)=(init b e).getD v (false,false) :=
    scan_prefix _ _ _ _ _ (by simpa [init_len] using hv)
  have pair := marked e he b
  have a := congrArg Prod.fst pair
  have c := congrArg Prod.snd pair
  simp only [linStep,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil,seen e.1 bounds'.1,seen e.2 bounds'.2]
  cases b <;> simp_all

theorem dirty_down (K : Circuit) (out : K.output<42+K.gates.length) (e q) :
    dirty (adjoin K e) q=true → dirty K q=true := by
  unfold dirty
  rw [single_adjoin K out e q true,single_adjoin K out e q false]
  simp <;> grind

private theorem count_mono {α : Type} (l : List α) (p q : α→Bool)
    (sub : ∀a∈l,q a=true → p a=true) : (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have rest := ih (fun b hb => sub b (List.mem_cons_of_mem _ hb))
    have head := sub a (List.mem_cons_self)
    cases h : p a <;> cases j : q a <;> simp_all [List.filter_cons]

private theorem count_lt {α : Type} (l : List α) (p q : α→Bool) (e : α) (he:e∈l)
    (yes:p e=true) (no:q e=false) (sub : ∀a∈l,q a=true → p a=true) :
    (l.filter q).length < (l.filter p).length := by
  induction l with
  | nil => simp at he
  | cons a t ih =>
    have shrink : ∀b∈t,q b=true → p b=true := fun b hb => sub b (List.mem_cons_of_mem _ hb)
    rcases List.mem_cons.mp he with rfl|inside
    · have bound := count_mono t p q shrink
      simp [List.filter_cons,yes,no] <;> omega
    · have strict := ih inside shrink
      have head := sub a (List.mem_cons_self)
      cases h : p a <;> cases j : q a <;> simp_all [List.filter_cons] <;> omega

theorem recovered {K A : Circuit} {e : Nat × Nat} (he : e∈edges) (badE : dirty K e=true)
    (ao : IsAO2 42 A) (out : A.output<42+A.gates.length) (price : cost A+1≤cost K)
    (semantic : ∀x : Fin 42→Bool, (A.eval (List.ofFn x) ||
      (x ⟨e.1,(bounds e he).1⟩ && x ⟨e.2,(bounds e he).2⟩))=true ↔ hasEdge x)
    (retain : ∀q∈edges,q≠e → dirty A q=true → dirty K q=true) :
    ∃ D,valid D ∧ cost D≤cost K ∧ (bad D).length<(bad K).length := by
  let D:=adjoin A e
  have clean : dirty D e=false := by simp [dirty,D,protects A out he true]
  refine ⟨D,⟨legal_adjoin ao out he,fun x => ?_⟩,by simpa [D,cost_adjoin] using price,?_⟩
  · rw [eval_adjoin A out he]
    exact semantic x
  · rw [bad_filter,bad_filter]
    apply count_lt _ _ _ e he badE clean
    intro q hq badD
    by_cases eq:q=e
    · subst q
      rw [clean] at badD
      contradiction
    exact retain q hq eq (dirty_down A out e q badD)

end PEqualNP.Outside.L_meta_8123.Work

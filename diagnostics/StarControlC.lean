import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_17948.Star
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


def body : Circuit := ⟨[⟨.or, [0,1]⟩,⟨.or, [26,3]⟩,⟨.or, [27,9]⟩,⟨.and, [13,28]⟩,⟨.or, [1,2]⟩,⟨.or, [30,4]⟩,⟨.or, [31,10]⟩,⟨.and, [14,32]⟩,⟨.or, [2,3]⟩,⟨.or, [34,5]⟩,⟨.or, [35,11]⟩,⟨.and, [15,36]⟩,⟨.or, [3,4]⟩,⟨.or, [38,6]⟩,⟨.or, [39,12]⟩,⟨.and, [16,40]⟩,⟨.or, [0,4]⟩,⟨.or, [42,5]⟩,⟨.or, [43,7]⟩,⟨.and, [17,44]⟩,⟨.or, [1,5]⟩,⟨.or, [46,6]⟩,⟨.or, [47,8]⟩,⟨.and, [18,48]⟩,⟨.or, [2,6]⟩,⟨.or, [50,7]⟩,⟨.or, [51,9]⟩,⟨.and, [19,52]⟩,⟨.or, [3,7]⟩,⟨.or, [54,8]⟩,⟨.or, [55,10]⟩,⟨.and, [20,56]⟩,⟨.or, [4,8]⟩,⟨.or, [58,9]⟩,⟨.or, [59,11]⟩,⟨.and, [21,60]⟩,⟨.or, [5,9]⟩,⟨.or, [62,10]⟩,⟨.or, [63,12]⟩,⟨.and, [22,64]⟩,⟨.or, [0,6]⟩,⟨.or, [66,10]⟩,⟨.or, [67,11]⟩,⟨.and, [23,68]⟩,⟨.or, [1,7]⟩,⟨.or, [70,11]⟩,⟨.or, [71,12]⟩,⟨.and, [24,72]⟩,⟨.or, [0,2]⟩,⟨.or, [74,8]⟩,⟨.or, [75,12]⟩,⟨.and, [25,76]⟩,⟨.or, [29,33]⟩,⟨.or, [78,37]⟩,⟨.or, [79,41]⟩,⟨.or, [80,45]⟩,⟨.or, [81,49]⟩,⟨.or, [82,53]⟩,⟨.or, [83,57]⟩,⟨.or, [84,61]⟩,⟨.or, [85,65]⟩,⟨.or, [86,69]⟩,⟨.or, [87,73]⟩,⟨.or, [88,77]⟩],89⟩
abbrev Q := Fin 13
def Inc (p l : Q) := p=l ∨ p=l+1 ∨ p=l+3 ∨ p=l+9
instance (p l : Q) : Decidable (Inc p l) := by unfold Inc; infer_instance
def flags : List (Q×Q) := [(0,0),(1,0),(3,0),(9,0),(1,1),(2,1),(4,1),(10,1),(2,2),(3,2),(5,2),(11,2),(3,3),(4,3),(6,3),(12,3),(0,4),(4,4),(5,4),(7,4),(1,5),(5,5),(6,5),(8,5),(2,6),(6,6),(7,6),(9,6),(3,7),(7,7),(8,7),(10,7),(4,8),(8,8),(9,8),(11,8),(5,9),(9,9),(10,9),(12,9),(0,10),(6,10),(10,10),(11,10),(1,11),(7,11),(11,11),(12,11),(0,12),(2,12),(8,12),(12,12)]
def listTerms := flags.map fun t => [t.1.val,13+t.2.val]
def combined := (body.gates.foldl tstep T0).getD 89 []
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
  have computed := (good_fold _ body.gates ok _ _ (good_init x)).2 89
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

abbrev Word := BitVec 79
def columns : List Word := [(34493956104 <<< 40) ||| 134217730,(2147483776 <<< 40) ||| 2415919108,(68719478784 <<< 40) ||| 38654705672,(32768 <<< 40) ||| 619012161552,(524305 <<< 40) ||| 8589934624,(8388896 <<< 40) ||| 137438953536,(268440066 <<< 40) ||| 128,(4295041088 <<< 40) ||| 256,(137440134144 <<< 40) ||| 512,(18890752 <<< 40) ||| 1073742848,(570687488 <<< 40) ||| 17179871232,(9667870720 <<< 40) ||| 274877911040,(292124884996 <<< 40) ||| 8192,(0 <<< 40) ||| 2013282304,(0 <<< 40) ||| 32212287488,(0 <<< 40) ||| 515396141056,(7 <<< 40) ||| 549755944960,(120 <<< 40) ||| 262144,(1920 <<< 40) ||| 524288,(30720 <<< 40) ||| 1048576,(491520 <<< 40) ||| 2097152,(7864320 <<< 40) ||| 4194304,(125829120 <<< 40) ||| 8388608,(2013265920 <<< 40) ||| 16777216,(32212254720 <<< 40) ||| 33554432,(515396075520 <<< 40) ||| 67108864]
def chart (v : Fin 26) (i : ℕ) : Word := if i%26=v.val then 0 else columns.getD (i%26) 0
def packTerm (A : ℕ → Word) : List ℕ → Word
  | [] => BitVec.allOnes 79
  | i::d => A i &&& packTerm A d
def packDNF (A : ℕ → Word) : List (List ℕ) → Word
  | [] => 0
  | d::D => packTerm A d ||| packDNF A D
def codes (v : Fin 26) := (body.gates.foldl tstep T0).map (packDNF (chart v))
def seen (v : Fin 26) : Finset ℕ :=
  let L := codes v
  (Finset.range 64).filter fun j => L.getD (26+j) 0 ∈ L.take (26+j)
theorem evalTerm (A : ℕ → Word) (k : Fin 79) (d : List ℕ) :
    (packTerm A d).getLsbD k = d.all (fun i => (A i).getLsbD k) := by
  induction d with
  | nil => simp only [packTerm,BitVec.getLsbD_allOnes,k.isLt,decide_true,List.all_nil]
  | cons i d ih => simp only [packTerm,BitVec.getLsbD_and,ih,List.all_cons]
theorem evalWord (A : ℕ → Word) (k : Fin 79) (D : List (List ℕ)) :
    (packDNF A D).getLsbD k = evalD (fun i => (A i).getLsbD k) D := by
  induction D with
  | nil => exact (by decide +kernel : ∀ i : Fin 79, (0 : Word).getLsbD i.val=false) k
  | cons d D ih =>
    simp only [packDNF,BitVec.getLsbD_or,evalTerm,ih,evalD,List.any_cons]
def input (v : Fin 26) (r : Fin 79) (i : Fin 26) := (chart v i.val).getLsbD r
theorem off (v : Fin 26) (r : Fin 79) : input v r v=false := by simp [input,chart]
set_option maxHeartbeats 2500000 in
theorem codeBit (v : Fin 26) (r : Fin 79) (w : ℕ) :
    ((codes v).getD w 0).getLsbD r = (body.wires (List.ofFn (input v r))).getD w false := by
  have ok : ∀g∈body.gates, okb g=true := by decide +kernel
  let T := body.gates.foldl tstep T0
  have spec := (good_fold _ body.gates ok _ _ (good_init (input v r))).2 w
  have get : (codes v).getD w 0=packDNF (chart v) (T.getD w []) := by
    change (T.map _).getD w _=_
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases h:T[w]? <;> rfl
  have fn : (fun i => (chart v i).getLsbD r) = (fun i => input v r (Fin.ofNat 26 i)) := by
    funext i
    change (chart v i).getLsbD r = (chart v (i%26)).getLsbD r
    simp [chart]
  calc
    _ = (packDNF (chart v) (T.getD w [])).getLsbD r := congrArg (fun a : Word => a.getLsbD r) get
    _ = evalD (fun i => (chart v i).getLsbD r) (T.getD w []) := evalWord _ _ _
    _ = evalD (fun i => input v r (Fin.ofNat 26 i)) (T.getD w []) := congrArg (fun f => evalD f (T.getD w [])) fn
    _ = _ := spec.symm
theorem length_codes (v : Fin 26) : (codes v).length=90 := by
  simp only [codes,List.length_map]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem atMostFour : ∀ v, (seen v).card≤4 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem noneHigh : ∀ v, ∀ j : Fin 64, ((codes v).getD (26+j.val) 0).getLsbD 0=false := by decide +kernel
theorem noFive (v : Fin 26) (J : Finset ℕ)
    (hs : ∀ j∈J, j<body.size ∧ ∃ a b : Bool, ∃ k<26+j, ∀ x : Fin 26→Bool, x v=false →
          (body.wires (List.ofFn x)).getD (26+j) false =
          (a && (body.wires (List.ofFn x)).getD k false || b)) : J.card≤4 := by
  apply (Finset.card_le_card ?_).trans (atMostFour v)
  intro j hj
  obtain ⟨ltj,a,b,k,hk,eq⟩ := hs j hj
  change j<64 at ltj
  have check (r : Fin 79) := eq (input v r) (off v r)
  simp only [←codeBit] at check
  have fromIndex (i : ℕ) (hi : i<26+j) : (codes v).getD i 0∈(codes v).take (26+j) := by
    have len := length_codes v
    have hlen : i<((codes v).take (26+j)).length := by simp; omega
    have val := List.getElem_mem (l:=(codes v).take (26+j)) hlen
    rw [List.getElem_take] at val
    rwa [List.getD_eq_getElem _ _ (by omega)]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ltj,?_⟩
  cases b with
  | true =>
    have low := noneHigh v ⟨j,ltj⟩
    have high := check 0
    simp at high
    exact False.elim (Bool.noConfusion (low.symm.trans high))
  | false =>
    cases a with
    | true =>
      have same : (codes v).getD (26+j) 0=(codes v).getD k 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        simpa using check ⟨r,hr⟩
      rw [same]
      exact fromIndex k hk
    | false =>
      have same : (codes v).getD (26+j) 0=(codes v).getD v.val 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro r hr
        have x := codeBit v ⟨r,hr⟩ v.val
        have C : (body.wires (List.ofFn (input v ⟨r,hr⟩))).getD v.val false = false := by
          change (body.gates.foldl wstep (List.ofFn (input v ⟨r,hr⟩))).getD v.val false=false
          have old (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i<xs.length) :
              (gs.foldl wstep xs).getD i false=xs.getD i false := by
            induction gs generalizing xs with
            | nil => rfl
            | cons a gs ih =>
              rw [List.foldl_cons,ih _ (by rw [wstep_len]; omega),wstep_lt _ _ _ hi]
          rw [old _ _ _ (by simpa using v.isLt),ofFn_getD _ _ v.isLt]
          exact off v _
        rw [x,C]
        simpa using check ⟨r,hr⟩
      rw [same]
      exact fromIndex v.val (by omega)

theorem fourReaders : ∀v : Fin 26, (body.gates.filter fun g => decide (v.val∈g.inputs)).length≤4 := by decide +kernel
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
local instance : Inhabited Gate := ⟨⟨.or,[]⟩⟩
theorem legal_at : ∀j : Fin 64, let g := body.gates[j.val]!
    (g.op=.and ∨ g.op=.or) ∧ ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a<26+j.val ∧ b<26+j.val := by
  intro j
  have f : ∀ j : Fin 64, let g := body.gates[j.val]!
      (g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2 ∧ g.inputs[0]!≠g.inputs[1]! ∧
      g.inputs[0]!<26+j.val ∧ g.inputs[1]!<26+j.val := by decide +kernel
  obtain ⟨op,len,ne,a,b⟩ := f j
  obtain ⟨u,w,pins⟩ := List.length_eq_two.mp len
  rw [pins] at ne a b
  exact ⟨op,u,w,pins,ne,a,b⟩

theorem cap64Fails : ¬(∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : (Fin (26 : ℕ) → Bool) → ℕ → Bool), (∀ (x3 : Fin (26 : ℕ)), (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (↑x3 ∈ x4.inputs)) x1.gates).length ≤ (4 : ℕ)) → x1.size ≤ (64 : ℕ) → (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (26 : ℕ) + x5 ∧ x9 < (26 : ℕ) + x5) → (∀ (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ), x2 x6 x7 = (x1.wires (List.ofFn x6)).getD x7 Bool.false) → (∀ (x7 : Fin (26 : ℕ) → Bool), x2 x7 x1.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), (x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ))) ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) → ∃ (x8 : Fin (26 : ℕ)) (x9 : Finset ℕ), (5 : ℕ) ≤ x9.card ∧ ∀ x10 ∈ x9, x10 < x1.size ∧ ∃ (x12 : Bool) (x13 : Bool), ∃ x14 < (26 : ℕ) + x10, ∀ (x15 : Fin (26 : ℕ) → Bool), x15 x8 = Bool.false → x2 x15 ((26 : ℕ) + x10) = (x12 && x2 x15 x14 || x13)) := by
  intro H
  have given := H body (fun x i => (body.wires (List.ofFn x)).getD i false) fourReaders (by decide +kernel)
  have legal : ∀ j (g : Gate), body.gates[j]?=some g → (g.op=.and ∨ g.op=.or) ∧
      ∃ a b, g.inputs=[a,b] ∧ a≠b ∧ a < 26+j ∧ b < 26+j := by
    intro j g hit
    obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hit
    let i : Fin 64 := ⟨j,hj⟩
    have gg : body.gates[j]! = g := by simpa [hj] using eq
    have ok := legal_at i
    change (body.gates[j]!.op=.and ∨ body.gates[j]!.op=.or) ∧
      ∃ a b, body.gates[j]!.inputs=[a,b] ∧ a≠b ∧ a < 26+j ∧ b < 26+j at ok
    rwa [gg] at ok
  obtain ⟨v,J,hJ,hs⟩ := given legal (fun _ _ => rfl) semantic
  have low := noFive v J hs
  omega
end PEqualNP.Outside.L_meta_17948.Star

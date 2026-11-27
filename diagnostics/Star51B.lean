import PEqualNP.Defs
namespace PlaneOrdered
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

theorem ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


theorem mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

theorem cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

theorem ordered (n : ℕ) (D : Circuit) (h : PEqualNP.TopForm.IsAO2 n D) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => (D.wires (List.ofFn x)).getD w false) := by
  let C : Circuit := ⟨D.gates,w⟩
  have hm : PEqualNP.MetaComplexity.Monotone2 C := by
    intro g hg
    exact ⟨h.1 g hg,by have eq := h.2.2 g hg; omega⟩
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  exact cmono C hm n x y hxy

end PlaneOrdered

namespace Promise19004
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 13
abbrev W := Fin 26
def Inc (p l : V) := (p.val+l.val)%13 ∈ ([0,1,3,9] : List Nat)
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def vec (X Y : Finset V) (i : W) : Bool :=
  if i.val<13 then decide (Fin.ofNat 13 i.val∈X) else decide (Fin.ofNat 13 i.val∈Y)
def off (X : Finset V) := Finset.univ.filter fun l => ∀p∈X,¬Inc p l
def read (C : Circuit) (o : List Nat) (x : W → Bool) :=
  GateOp.or.eval (o.map fun k => (C.wires (List.ofFn x)).getD k false)
def Tests (C : Circuit) (o : List Nat) : Prop :=
  (∀p l : V,Inc p l → read C o (vec {p} {l})=true) ∧
   ∀S : Finset V,S.card≤3 → read C o (vec S (off S))=false ∧ read C o (vec (off S) S)=false
def Hit (X Y : Finset V) := ∃p∈X,∃l∈Y,Inc p l
theorem four : ∀ S : Finset V, S.card=4 → (off S).card≤3 := by
  set_option maxRecDepth 20000 in
    set_option maxHeartbeats 0 in
      decide +kernel
theorem small (X Y : Finset V) (hn : ¬Hit X Y) : X.card≤3 ∨ Y.card≤3 := by
  by_cases hx : X.card≤3
  · exact Or.inl hx
  right
  obtain ⟨S,sub,hs⟩ := Finset.exists_subset_card_eq (show 4≤X.card by omega)
  have incl : Y ⊆ off S := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp h => hn ⟨p,sub hp,l,hl,h⟩⟩
  exact (Finset.card_le_card incl).trans (four S hs)

theorem read_mono (C : Circuit) (hm : Monotone2 C) (o : List Nat) {x y : W → Bool} (hxy : x≤y) :
    read C o x=true → read C o y=true := by
  simp only [read,GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id]
  rintro ⟨k,hk,h⟩
  let D : Circuit := ⟨C.gates,k⟩
  have mD : Monotone2 D := hm
  exact ⟨k,hk,PlaneOrdered.cmono D mD 26 x y hxy h⟩
theorem inclVec {A B X Y : Finset V} (ha : A⊆X) (hb : B⊆Y) : vec A B ≤ vec X Y := by
  intro i
  apply Bool.le_iff_imp.mpr
  unfold vec
  split <;> simp only [decide_eq_true_eq]
  · exact fun h => ha h
  · exact fun h => hb h
theorem decodes {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o)
    (X Y : Finset V) : read C o (vec X Y)=true ↔ Hit X Y := by
  constructor
  · intro f
    by_contra no
    rcases small X Y no with px|ly
    · have incl : Y ⊆ off X := fun l hl => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun p hp h => no ⟨p,hp,l,hl,h⟩⟩
      have lit := read_mono C hm o (inclVec (A:=X) subset_rfl incl) f
      rw [(ht.2 X px).1] at lit
      contradiction
    · have incl : X ⊆ off Y := by
        intro p hp
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl hi => no ⟨p,hp,l,hl,?_⟩⟩
        simpa only [Inc,Nat.add_comm] using hi
      have lit := read_mono C hm o (inclVec (B:=Y) incl subset_rfl) f
      rw [(ht.2 Y ly).2] at lit
      contradiction
  · rintro ⟨p,hp,l,hl,edge⟩
    exact read_mono C hm o (inclVec (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl)) (ht.1 p l edge)
def pts (x : W → Bool) := Finset.univ.filter fun p : V => x (Fin.castAdd 13 p)=true
def lns (x : W → Bool) := Finset.univ.filter fun l : V => x (Fin.natAdd 13 l)=true
theorem rebuild (x : W → Bool) : vec (pts x) (lns x)=x := by
  funext i
  unfold vec
  split <;> rename_i hi
  · have eq : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change i.val%13=i.val; omega)
    simp [pts]
    exact congrArg x eq
  · have eq : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := Fin.ext (by change 13+i.val%13=i.val; have := i.isLt; omega)
    simp only [lns,Finset.mem_filter,Finset.mem_univ,true_and,eq]
    cases x i <;> rfl
theorem exact_eval {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o) (x : W → Bool) :
    read C o x=true ↔ ∃p l : V,Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  have d := decodes hm ht (pts x) (lns x)
  rw [rebuild] at d
  rw [d]
  constructor
  · rintro ⟨p,hp,l,hl,ed⟩
    exact ⟨p,l,ed,(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hl).2⟩
  · rintro ⟨p,l,ed,hp,hl⟩
    exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,ed⟩

def finish (C : Circuit) (o : List Nat) : Circuit :=
  ⟨C.gates++[⟨GateOp.or,o⟩],26+C.size⟩
theorem finish_size (C : Circuit) (o : List Nat) : (finish C o).size=C.size+1 := by
  simp [finish,Circuit.size]
theorem finish_mono {C : Circuit} (hm : Monotone2 C) {o : List Nat} (small : o.length≤2) :
    Monotone2 (finish C o) := by
  intro g hg
  change g∈C.gates++[⟨GateOp.or,o⟩] at hg
  rcases List.mem_append.mp hg with old|new
  · exact hm g old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨Or.inr rfl,small⟩
theorem finish_eval (C : Circuit) (o : List Nat) (x : W → Bool) :
    (finish C o).eval (List.ofFn x)=read C o x := by
  let u := PlaneOrdered.wf C.gates (List.ofFn x)
  have sz : u.length=26+C.size := by simp [u,PlaneOrdered.wf_len,Circuit.size]
  change (PlaneOrdered.wf (C.gates++[⟨GateOp.or,o⟩]) (List.ofFn x)).getD (26+C.size) false=_
  unfold PlaneOrdered.wf
  rw [List.foldl_append]
  change (u++[GateOp.or.eval (o.map fun k => u.getD k false)]).getD (26+C.size) false=_
  rw [←sz,PlaneOrdered.getD_snoc_eq]
  rfl
end Promise19004
namespace Star19004
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


open Promise19004
def body : Circuit := ⟨[⟨.or,[13,14]⟩,⟨.or,[26,16]⟩,⟨.or,[27,22]⟩,⟨.and,[0,28]⟩,⟨.or,[13,15]⟩,⟨.or,[30,21]⟩,⟨.or,[31,25]⟩,⟨.and,[1,32]⟩,⟨.or,[14,20]⟩,⟨.or,[34,24]⟩,⟨.or,[35,25]⟩,⟨.and,[2,36]⟩,⟨.or,[13,19]⟩,⟨.or,[38,23]⟩,⟨.or,[39,24]⟩,⟨.and,[3,40]⟩,⟨.or,[18,22]⟩,⟨.or,[42,23]⟩,⟨.or,[43,25]⟩,⟨.and,[4,44]⟩,⟨.or,[17,21]⟩,⟨.or,[46,22]⟩,⟨.or,[47,24]⟩,⟨.and,[5,48]⟩,⟨.or,[16,20]⟩,⟨.or,[50,21]⟩,⟨.or,[51,23]⟩,⟨.and,[6,52]⟩,⟨.or,[15,19]⟩,⟨.or,[54,20]⟩,⟨.or,[55,22]⟩,⟨.and,[7,56]⟩,⟨.or,[14,18]⟩,⟨.or,[58,19]⟩,⟨.or,[59,21]⟩,⟨.and,[8,60]⟩,⟨.or,[13,17]⟩,⟨.or,[62,18]⟩,⟨.or,[63,20]⟩,⟨.and,[9,64]⟩,⟨.or,[16,17]⟩,⟨.or,[66,19]⟩,⟨.or,[67,25]⟩,⟨.and,[10,68]⟩,⟨.or,[15,16]⟩,⟨.or,[70,18]⟩,⟨.or,[71,24]⟩,⟨.and,[11,72]⟩,⟨.or,[14,15]⟩,⟨.or,[74,17]⟩,⟨.or,[75,23]⟩,⟨.and,[12,76]⟩,⟨.or,[29,33]⟩,⟨.or,[78,37]⟩,⟨.or,[79,41]⟩,⟨.or,[80,45]⟩,⟨.or,[81,49]⟩,⟨.or,[82,53]⟩,⟨.or,[83,57]⟩,⟨.or,[84,61]⟩,⟨.or,[85,65]⟩,⟨.or,[86,69]⟩,⟨.or,[87,73]⟩],0⟩
def outs : List Nat := [88,77]
def C := finish body outs
def terms := (C.gates.foldl tstep T0).getD C.output []
abbrev Q := Fin 13
def flags : List (Q×Q) := [(0, 0), (0, 1), (0, 3), (0, 9), (1, 0), (1, 2), (1, 8), (1, 12), (2, 1), (2, 7), (2, 11), (2, 12), (3, 0), (3, 6), (3, 10), (3, 11), (4, 5), (4, 9), (4, 10), (4, 12), (5, 4), (5, 8), (5, 9), (5, 11), (6, 3), (6, 7), (6, 8), (6, 10), (7, 2), (7, 6), (7, 7), (7, 9), (8, 1), (8, 5), (8, 6), (8, 8), (9, 0), (9, 4), (9, 5), (9, 7), (10, 3), (10, 4), (10, 6), (10, 12), (11, 2), (11, 3), (11, 5), (11, 11), (12, 1), (12, 2), (12, 4), (12, 10)]

def listTerms := flags.map fun t => [t.1.val,13+t.2.val]
theorem checkedTerms : terms = listTerms := by decide +kernel
theorem reflection (x : Fin 26 → Bool) : C.eval (List.ofFn x) = evalD (fun i => x (Fin.ofNat 26 i)) terms := by
  have ok : ∀ g∈C.gates, okb g=true := by decide +kernel
  exact (good_fold _ C.gates ok _ _ (good_init x)).2 C.output
theorem member : ∀p l:Q, (p,l)∈flags ↔ Inc p l := by decide +kernel
theorem identP : ∀p:Q,Fin.ofNat 26 p.val=Fin.castAdd 13 p := by decide +kernel
theorem identL : ∀l:Q,Fin.ofNat 26 (13+l.val)=Fin.natAdd 13 l := by decide +kernel
theorem semantic (x : Fin 26 → Bool) : read body outs x=true ↔
    ∃p l:Q, Inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true := by
  rw [←finish_eval]
  change C.eval (List.ofFn x)=true ↔ _
  rw [reflection,checkedTerms]
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
theorem vP (P L : Finset Q) (p : Q) : vec P L (Fin.castAdd 13 p)=decide (p∈P) := by
  have h : ∀p:Q, (Fin.castAdd 13 p).val<13 ∧ Fin.ofNat 13 (Fin.castAdd 13 p).val=p := by decide +kernel
  simp only [vec,(h p).1,ite_true,(h p).2]
theorem vL (P L : Finset Q) (l : Q) : vec P L (Fin.natAdd 13 l)=decide (l∈L) := by
  have h : ∀l:Q, ¬(Fin.natAdd 13 l).val<13 ∧ Fin.ofNat 13 (Fin.natAdd 13 l).val=l := by decide +kernel
  simp only [vec,(h l).1,ite_false,(h l).2]
theorem boundary : Tests body outs := by
  constructor
  · intro p l edge
    exact (semantic _).mpr ⟨p,l,edge,by rw [vP]; simp,by rw [vL]; simp⟩
  · intro X _
    constructor
    · by_contra wrong
      rw [Bool.not_eq_false] at wrong
      have fire := wrong
      obtain ⟨p,l,e,hp,hl⟩ := (semantic _).mp fire
      rw [vP,decide_eq_true_eq] at hp
      rw [vL,decide_eq_true_eq] at hl
      exact (Finset.mem_filter.mp hl).2 p hp e
    · by_contra wrong
      rw [Bool.not_eq_false] at wrong
      have fire := wrong
      obtain ⟨p,l,e,hp,hl⟩ := (semantic _).mp fire
      rw [vP,decide_eq_true_eq] at hp
      rw [vL,decide_eq_true_eq] at hl
      exact (Finset.mem_filter.mp hp).2 l hl (by simpa only [Inc,Nat.add_comm] using e)
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
theorem sharp : ∃(B : Circuit) (o : List Nat), Monotone2 B ∧ o.length≤2 ∧ Tests B o ∧
    (PEqualNP.MetaComplexity.NestedCover.gateAt B (B.size-1)).op=GateOp.or ∧ B.size=63 := by
  refine ⟨body,outs,?_,by decide,boundary,by rfl,by decide⟩
  exact (by decide +kernel : ∀g∈body.gates,(g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)


def countedOR (C : Circuit) : Finset Nat :=
  (Finset.range C.gates.length).filter fun i => (C.gates[i]?).any (fun g => decide (g.op=.or))
theorem ncardOR (D : Circuit) :
    {i : ℕ | ∃ g : Gate, D.gates[i]?=some g ∧ g.op=.or}.ncard = (countedOR D).card := by
  have e : {i : ℕ | ∃ g : Gate, D.gates[i]?=some g ∧ g.op=.or} = ↑(countedOR D) := by
    ext i
    by_cases h : i<D.gates.length
    · simp [countedOR,h,List.getElem?_eq_getElem h]
    · simp [countedOR,h,List.getElem?_eq_none (Nat.le_of_not_gt h)]
  rw [e,Set.ncard_coe_finset]

theorem exact51 : ∃ D : Circuit, Monotone2 D ∧ D.output+1=26+D.gates.length ∧
    (∃ pins : List Nat, D.gates.getLast?=some ⟨.or,pins⟩) ∧
    (∀ X Y : Finset Q, D.eval (List.ofFn (vec X Y))=true ↔ ∃ p∈X,∃ l∈Y,Inc p l) ∧
    {i : ℕ | ∃ g : Gate,D.gates[i]?=some g ∧ g.op=.or}.ncard=51 := by
  refine ⟨C,?_,rfl,⟨outs,rfl⟩,?_,?_⟩
  · exact (by decide +kernel : ∀g∈C.gates,(g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2)
  · intro X Y
    rw [show C=finish body outs by rfl,finish_eval,semantic]
    simp only [vP,vL,decide_eq_true_eq]
    constructor
    · rintro ⟨p,l,inc,hp,hl⟩; exact ⟨p,hp,l,hl,inc⟩
    · rintro ⟨p,hp,l,hl,inc⟩; exact ⟨p,l,inc,hp,hl⟩
  · rw [ncardOR]
    decide +kernel
end Star19004

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

end PlaneOrdered

namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := Fin 13
abbrev W := Fin 26
abbrev pt (p : V) : W := Fin.castAdd 13 p
abbrev ln (l : V) : W := Fin.natAdd 13 l
def offs : Finset V := {0,1,3,9}
def Inc (p l : V) : Prop := ∃ a ∈ offs, p = l+a
instance (p l : V) : Decidable (Inc p l) := by unfold Inc; infer_instance
def Avoid (S : Finset V) (l : V) := ∀ p ∈ S, ¬ Inc p l
instance (S : Finset V) (l : V) : Decidable (Avoid S l) := by unfold Avoid; infer_instance
def Closed (S : Finset V) := ∀ p ∉ S, ∃ l, Avoid S l ∧ Inc p l
def frame (S : Finset V) (i : W) : Bool :=
  decide ((∃ p ∈ S, i=pt p) ∨ ∃ l, i=ln l ∧ Avoid S l)
def pos (p l : V) (i : W) : Bool := decide (i=pt p ∨ i=ln l)
def Hit (x : W → Bool) := ∃ p l, Inc p l ∧ x (pt p)=true ∧ x (ln l)=true
def Tests (C : Circuit) : Prop :=
  (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) ∧
  ∀ S, Closed S → circuitFun 26 C (frame S)=false
def Exact (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ Hit x

theorem parts : ∀ i : W, (∃ p, i=pt p) ∨ ∃ l, i=ln l := by decide
theorem disj : ∀ p l : V, pt p ≠ ln l := by decide
theorem pp : ∀ p q : V, pt p=pt q → p=q := by decide
theorem ll : ∀ p q : V, ln p=ln q → p=q := by decide

theorem frame_pt (S : Finset V) (p : V) : frame S (pt p)=true ↔ p∈S := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨q,hq,e⟩|⟨l,e,_⟩)
    · exact (pp _ _ e) ▸ hq
    · exact (disj _ _ e).elim
  · exact fun h => Or.inl ⟨p,h,rfl⟩
theorem frame_ln (S : Finset V) (l : V) : frame S (ln l)=true ↔ Avoid S l := by
  simp only [frame,decide_eq_true_eq]
  constructor
  · rintro (⟨p,_,e⟩|⟨k,e,h⟩)
    · exact (disj _ _ e.symm).elim
    · exact (ll _ _ e) ▸ h
  · exact fun h => Or.inr ⟨l,rfl,h⟩
theorem complete {C : Circuit} (hm : Monotone2 C) : Tests C ↔ Exact C := by
  constructor
  · intro h x
    constructor
    · intro live
      by_contra empty
      let S := Finset.univ.filter fun p : V => ∀ l : V, x (ln l)=true → ¬ Inc p l
      have mem (p : V) : p∈S ↔ ∀ l, x (ln l)=true → ¬Inc p l := by simp [S]
      have avoid (l : V) (selected : x (ln l)=true) : Avoid S l :=
        fun p hp => (mem p).mp hp l selected
      have closed : Closed S := by
        intro p hp
        rw [mem] at hp
        push_neg at hp
        obtain ⟨l,hl,edge⟩ := hp
        exact ⟨l,avoid l hl,edge⟩
      have below : x≤frame S := by
        intro i
        apply Bool.le_iff_imp.mpr
        intro hi
        rcases parts i with ⟨p,rfl⟩|⟨l,rfl⟩
        · exact (frame_pt S p).mpr ((mem p).mpr (fun l hl edge => empty ⟨p,l,edge,hi,hl⟩))
        · exact (frame_ln S l).mpr (avoid l hi)
      have bad : circuitFun 26 C (frame S)=true := PlaneOrdered.cmono C hm 26 _ _ below live
      rw [h.2 S closed] at bad
      contradiction
    · rintro ⟨p,l,edge,hp,hl⟩
      apply PlaneOrdered.cmono C hm 26 (pos p l) x _ (h.1 p l edge)
      intro i
      apply Bool.le_iff_imp.mpr
      simp only [pos,decide_eq_true_eq]
      rintro (rfl|rfl)
      · exact hp
      · exact hl
  · intro h
    constructor
    · intro p l edge
      exact (h _).mpr ⟨p,l,edge,by simp [pos],by simp [pos]⟩
    · intro S _
      cases hv : circuitFun 26 C (frame S) with
      | false => rfl
      | true =>
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp hv
        exact ((frame_ln S l).mp hl p ((frame_pt S p).mp hp) edge).elim

theorem exact_lower_iff :
    (∀ C : Circuit, Monotone2 C → C.size≤63 →
      (∀ p l, Inc p l → circuitFun 26 C (pos p l)=true) →
      (∀ S, Closed S → circuitFun 26 C (frame S)=false) → False) ↔
    ∀ C : Circuit, Monotone2 C → Exact C → 64≤C.size := by
  constructor
  · intro h C hm exactC
    obtain ⟨hp,hn⟩ := (complete hm).mpr exactC
    by_contra! small
    exact h C hm (by omega) hp hn
  · intro h C hm small hp hn
    have := h C hm ((complete hm).mp ⟨hp,hn⟩)
    omega
end Full5741
namespace Promise17245
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

end Promise17245
namespace Rel5741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The renaming of wires: input wire `w < n` goes to `π w`, gate wire `w ≥ n` to
`w - n + m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

/-- A gate with its wires renamed. -/
def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

/-- A circuit with its wires renamed. -/
def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

/-- One gate evaluated on a wire list. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

/-- The invariant: the wire lists match along the renaming. -/
def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, PlaneOrdered.getD_snoc_eq, PlaneOrdered.getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end Rel5741
namespace Full5741
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def flip (i : W) : W :=
  if i.val<13 then i else ln (-(Fin.ofNat 13 i.val))
theorem flip_pt : ∀ p : V, flip (pt p)=pt p := by decide
theorem flip_ln : ∀ l : V, flip (ln l)=ln (-l) := by decide
theorem inc_plus : ∀ p l : V, Inc p l ↔ Promise17245.Inc p (-l) := by decide +kernel
theorem plus_inc : ∀ p l : V, Promise17245.Inc p l ↔ Inc p (-l) := by decide +kernel

def renamed (C : Circuit) := Rel5741.relabel 26 26 flip C
theorem rename_size (C : Circuit) : (renamed C).size=C.size := by
  simp [renamed,Rel5741.relabel,Circuit.size]
theorem rename_mono {C : Circuit} (hm : Monotone2 C) : Monotone2 (renamed C) := by
  intro g hg
  obtain ⟨old,mem,rfl⟩ := List.mem_map.mp hg
  exact ⟨(hm old mem).1,by simpa [Rel5741.relGate] using (hm old mem).2⟩
theorem rename_eval (C : Circuit) (x : W → Bool) :
    circuitFun 26 (renamed C) x = circuitFun 26 C (x ∘ flip) :=
  (Rel5741.rel_fold 26 26 flip C.gates _ _ (Rel5741.rel_init 26 26 flip x)).2.2 C.output
def PlusHit (x : W → Bool) :=
  ∃ p l : V, Promise17245.Inc p l ∧ x (pt p)=true ∧ x (ln l)=true
def PlusExact (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ PlusHit x

theorem forward {C : Circuit} (h : Exact C) : PlusExact (renamed C) := by
  intro x
  rw [rename_eval,h]
  constructor
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(inc_plus p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa [Function.comp,flip_ln] using hl⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(plus_inc p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa [Function.comp,flip_ln] using hl⟩
theorem backward {C : Circuit} (h : PlusExact C) : Exact (renamed C) := by
  intro x
  rw [rename_eval,h]
  constructor
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(plus_inc p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa [Function.comp,flip_ln] using hl⟩
  · rintro ⟨p,l,edge,hp,hl⟩
    exact ⟨p,-l,(inc_plus p l).mp edge,by simpa [Function.comp,flip_pt] using hp,
      by simpa [Function.comp,flip_ln] using hl⟩

open Promise17245 in
def Old (C : Circuit) :=
  (∀ p l : V, Promise17245.Inc p l → C.eval (List.ofFn (vec {p} {l}))=true) ∧
  ∀ S : Finset V, S.card≤3 →
    C.eval (List.ofFn (vec S (off S)))=false ∧ C.eval (List.ofFn (vec (off S) S))=false

theorem read_scalar (C : Circuit) (x : W → Bool) : Promise17245.read C [C.output] x=circuitFun 26 C x := by
  change GateOp.or.eval [((C.wires (List.ofFn x)).getD C.output false)] =
    ((C.wires (List.ofFn x)).getD C.output false)
  cases (C.wires (List.ofFn x)).getD C.output false <;> rfl

theorem vecpt (S T : Finset V) (p : V) : Promise17245.vec S T (pt p)=true ↔ p∈S := by
  have e : Fin.ofNat 13 (pt p).val=p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
  simp [Promise17245.vec,show (pt p).val<13 from p.isLt,e]
theorem vecln (S T : Finset V) (l : V) : Promise17245.vec S T (ln l)=true ↔ l∈T := by
  have e : Fin.ofNat 13 (ln l).val=l := Fin.ext (by change (13+l.val)%13=l.val; omega)
  have hi : ¬(ln l).val<13 := by change ¬13+l.val<13; omega
  simp [Promise17245.vec,hi,e]

open Promise17245 in
theorem old_iff {C : Circuit} (hm : Monotone2 C) : Old C ↔ PlusExact C := by
  constructor
  · intro h x
    have ht : Promise17245.Tests C [C.output] := by
      unfold Promise17245.Tests
      simp only [read_scalar]
      exact h
    simpa only [read_scalar] using exact_eval hm ht x
  · intro h
    constructor
    · intro p l edge
      exact (h _).mpr ⟨p,l,edge,(vecpt _ _ _).mpr (by simp),(vecln _ _ _).mpr (by simp)⟩
    · intro S _
      constructor
      · apply Bool.eq_false_iff.mpr
        intro y
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp y
        exact (Finset.mem_filter.mp ((vecln _ _ _).mp hl)).2 p ((vecpt _ _ _).mp hp) edge
      · apply Bool.eq_false_iff.mpr
        intro y
        obtain ⟨p,l,edge,hp,hl⟩ := (h _).mp y
        apply (Finset.mem_filter.mp ((vecpt _ _ _).mp hp)).2 l ((vecln _ _ _).mp hl)
        simpa only [Promise17245.Inc, Nat.add_comm l.val p.val] using edge

theorem equivalent_twins :
    (∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧ Tests C) ↔
    ∃ D : Circuit, Monotone2 D ∧ D.size≤63 ∧ Old D := by
  constructor
  · rintro ⟨C,hm,hs,ht⟩
    exact ⟨renamed C,rename_mono hm,by simpa [rename_size] using hs,
      (old_iff (rename_mono hm)).mpr (forward ((complete hm).mp ht))⟩
  · rintro ⟨D,hm,hs,ht⟩
    exact ⟨renamed D,rename_mono hm,by simpa [rename_size] using hs,
      (complete (rename_mono hm)).mpr (backward ((old_iff hm).mp ht))⟩
end Full5741

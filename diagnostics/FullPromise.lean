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

import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2880
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

end PEqualNP.Outside.L_meta_2880
namespace Research5962
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.CleanedNonEdge
abbrev V := Fin 14
abbrev X := V → Bool
def one (i : V) : X := fun j => decide (j=i)
def co (i : V) : X := fun j => decide (j≠i)
def simple (t : Fin 16) (x : X) := if h : t.val < 14 then x ⟨t.val,h⟩ else decide (t.val=15)
def obstructed (f g : X → Bool) :=
  ∀ t : Fin 16, ∃ x, f x = g x ∧ f x ≠ simple t x
def Fano (x : X) := ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧
  x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
instance (x : X) : Decidable (Fano x) := by unfold Fano; infer_instance
theorem boundary : (¬ Fano (fun _ => false)) ∧ Fano (fun _ => true) ∧
    (∀ i, ¬ Fano (one i)) ∧ (∀ i, Fano (co i)) := by decide +kernel

def signatures (f : X → Bool) := f (fun _ => false) = false ∧ f (fun _ => true) = true ∧
  ∀ i, f (one i) = false ∨ f (co i) = true

theorem extremes_iff (f g : X → Bool) (up : ∀ x y, x ≤ y → f x = true → f y = true)
    (out : ∀ x, g x = true ↔ Fano x) : obstructed f g ↔ signatures f := by
  constructor
  · intro h
    obtain ⟨a,_,ha⟩ := h 15
    obtain ⟨b,_,hb⟩ := h 14
    have fa : f a = false := by
      have hh : f a ≠ true := ha
      exact Bool.eq_false_iff.mpr hh
    have fb : f b = true := by
      have hh : f b ≠ false := hb
      exact Bool.eq_true_of_not_eq_false hh
    refine ⟨?_,up _ _ (fun _ => Bool.le_true _) fb,?_⟩
    · apply Bool.eq_false_iff.mpr
      intro yes
      have := up _ a (fun _ => Bool.false_le _) yes
      rw [fa] at this
      contradiction
    · intro i
      let t : Fin 16 := ⟨i.val,by omega⟩
      obtain ⟨x,_,hne⟩ := h t
      have ne : f x ≠ x i := by simpa [simple,t,i.isLt] using hne
      cases hx : x i with
      | true =>
        left
        apply Bool.eq_false_iff.mpr
        intro on
        have le : one i ≤ x := by
          intro j
          by_cases ij : j=i
          · subst j
            simp [one,hx]
          · simp [one,ij]
        exact ne ((up _ _ le on).trans hx.symm)
      | false =>
        right
        have on : f x = true := Bool.eq_true_of_not_eq_false (fun zero => ne (zero.trans hx.symm))
        apply up x _ _ on
        intro j
        by_cases ij : j=i
        · subst j
          simp [co,hx]
        · simp [co,ij]
  · rintro ⟨bot,top,gap⟩ t
    by_cases ht : t.val<14
    · let i : V := ⟨t.val,ht⟩
      rcases gap i with low | high
      · have no : g (one i) = false := Bool.eq_false_iff.mpr (fun e => boundary.2.2.1 i ((out _).mp e))
        refine ⟨one i,low.trans no.symm,?_⟩
        simp [simple,ht,i,one,low]
      · have yes : g (co i) = true := (out _).mpr (boundary.2.2.2 i)
        refine ⟨co i,high.trans yes.symm,?_⟩
        simp [simple,ht,i,co,high]
    · by_cases high : t.val=15
      · have no : g (fun _ => false) = false :=
          Bool.eq_false_iff.mpr fun e => boundary.1 ((out _).mp e)
        refine ⟨_,bot.trans no.symm,?_⟩
        simp [simple,ht,high,bot]
      · have yes : g (fun _ => true) = true := (out _).mpr boundary.2.1
        refine ⟨_,top.trans yes.symm,?_⟩
        simp [simple,ht,high,top]

theorem protected_wire (C : Circuit) (ao : Monotone2 C) (w : Nat)
    (correct : ∀ x : X, C.eval (List.ofFn x) = true ↔ Fano x) :
    obstructed (wireVal 14 C w) (fun x => C.eval (List.ofFn x)) ↔ signatures (wireVal 14 C w) :=
  extremes_iff _ _ (fun x y h => PEqualNP.Outside.L_meta_2880.cmono (⟨C.gates,w⟩ : Circuit) ao 14 x y h) correct

end Research5962

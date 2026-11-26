import PEqualNP.Defs

namespace Selector7832

def Adj (a b : Fin 13) : Prop := a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9

def opp (f : Fin 13 → Bool) (j : Fin 13) : Bool := !(f j || f (j + 1) || f (j + 3) || f (j + 9))

def acc (x : Fin 26 → Bool) : Prop :=
  ∃ a b : Fin 13, Adj a b ∧ x (Fin.castAdd 13 a) = true ∧ x (Fin.natAdd 13 b) = true

lemma opp_true_iff (f : Fin 13 → Bool) (j : Fin 13) :
    opp f j = true ↔ ∀ a, Adj a j → f a = false := by
  unfold opp Adj
  constructor
  · intro h a ha
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨h0, h1⟩, h3⟩, h9⟩ := h
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  · intro h
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff]
    exact ⟨⟨⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl))⟩, h _ (Or.inr (Or.inr (Or.inl rfl)))⟩,
      h _ (Or.inr (Or.inr (Or.inr rfl)))⟩

lemma le_of_true_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

lemma true_of_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst a
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) h)
  | true => rfl

lemma main (x : Fin 26 → Bool) (hmax : Maximal (fun z => ¬ acc z) x) :
    ∃ x6 : Fin 13 → Bool, x = Fin.append x6 (opp x6) ∧
      ∀ a, x6 a = false → ∃ b, Adj a b ∧ opp x6 b = true := by
  obtain ⟨x6, y, rfl⟩ : ∃ (x6 : Fin 13 → Bool) (y : Fin 13 → Bool), x = Fin.append x6 y := by
    refine ⟨fun a => x (Fin.castAdd 13 a), fun b => x (Fin.natAdd 13 b), ?_⟩
    funext i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro a; rw [Fin.append_left]
    · intro b; rw [Fin.append_right]
  obtain ⟨hna, hmx⟩ := hmax
  have hy : ∀ b, y b = true → opp x6 b = true := by
    intro b hb
    rw [opp_true_iff]
    intro a hab
    by_contra h
    apply hna
    refine ⟨a, b, hab, ?_, ?_⟩
    · simp only [Fin.append_left]; simpa using h
    · simp only [Fin.append_right]; exact hb
  have hz : ¬ acc (Fin.append x6 (opp x6)) := by
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [Fin.append_left, Fin.append_right] at ha hb
    rw [opp_true_iff] at hb
    rw [hb a hab] at ha
    exact Bool.false_ne_true ha
  have hle : Fin.append x6 y ≤ Fin.append x6 (opp x6) := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro a; simp only [Fin.append_left]; exact le_refl _
    · intro b; simp only [Fin.append_right]; exact le_of_true_imp (hy b)
  have hge := hmx hz hle
  have hyeq : y = opp x6 := by
    funext b
    apply le_antisymm (le_of_true_imp (hy b))
    have := hge (Fin.natAdd 13 b)
    simpa only [Fin.append_right] using this
  subst hyeq
  refine ⟨x6, rfl, ?_⟩
  intro a ha
  by_contra hno
  push_neg at hno
  have hacc : ¬ acc (Fin.append (Function.update x6 a true) (opp x6)) := by
    rintro ⟨u, b, hub, hu, hb⟩
    simp only [Fin.append_left, Fin.append_right] at hu hb
    by_cases hua : u = a
    · subst hua
      exact hno b hub hb
    · rw [Function.update_of_ne hua] at hu
      exact hz ⟨u, b, hub, by simpa only [Fin.append_left] using hu,
        by simpa only [Fin.append_right] using hb⟩
  have hle2 : Fin.append x6 (opp x6) ≤ Fin.append (Function.update x6 a true) (opp x6) := by
    intro i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro c
      simp only [Fin.append_left]
      by_cases hca : c = a
      · subst hca
        rw [Function.update_self]
        exact le_top
      · rw [Function.update_of_ne hca]
    · intro b; simp only [Fin.append_right]; exact le_refl _
  have h3 := hmx hacc hle2 (Fin.castAdd 13 a)
  simp only [Fin.append_left, Function.update_self] at h3
  rw [ha] at h3
  exact Bool.false_ne_true (true_of_le h3 rfl)


end Selector7832

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

namespace Selector7832
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

abbrev V := Fin 13
def probe (p l : V) (i : Fin 26) := decide (i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l)
def PSlot (p : V) := Fin.castAdd 13 p
def LSlot (l : V) := Fin.natAdd 13 l
def W (C : Circuit) (w : Nat) (x : Fin 26 → Bool) := PEqualNP.BlindGate.wireValue C 26 x w
def Positive (C : Circuit) (a b : Nat) := ∀ p l : V, Adj p l →
  W C a (probe p l)=true ∧ W C b (probe p l)=true
def Reject (C : Circuit) (a b : Nat) := ∀ x : V → Bool,
    (∀ p, x p=false → ∃ l, Adj p l ∧ opp x l=true) →
    W C (if opp x 0=true then a else b) (Fin.append x (opp x))=false

theorem app_le {x x' y y' : V → Bool} (p : x ≤ x') (l : y ≤ y') :
    Fin.append x y ≤ Fin.append x' y' := by
  intro i
  refine Fin.addCases (m:=13) (n:=13) ?_ ?_ i
  · intro j; simpa only [Fin.append_left] using p j
  · intro j; simpa only [Fin.append_right] using l j

theorem extend (x : Fin 26 → Bool) (no : ¬ acc x) :
    ∃ p : V → Bool, x ≤ Fin.append p (opp p) ∧ ∀ i, p i=false → ∃ j, Adj i j ∧ opp p j=true := by
  obtain ⟨m,hm,maxi⟩ := Finite.exists_le_maximal (p:=fun z => ¬ acc z) no
  obtain ⟨p,eq,hp⟩ := main m maxi
  exact ⟨p,eq ▸ hm,hp⟩

theorem neg_form {x y : V → Bool} : ¬acc (Fin.append x y) ↔
    ∀ p l : V, Adj p l → x p=true → y l=false := by
  constructor
  · intro no p l ad xp
    cases eq : y l with
    | false => rfl
    | true => exact False.elim (no ⟨p,l,ad,by simpa only [Fin.append_left] using xp,
        by simpa only [Fin.append_right] using eq⟩)
  · rintro safe ⟨p,l,ad,hp,hl⟩
    simp only [Fin.append_left] at hp
    simp only [Fin.append_right] at hl
    exact Bool.false_ne_true ((safe p l ad hp).symm.trans hl)

theorem monoOff (C : Circuit) (hf : IsAO2 26 C) (w : Nat) {x y : Fin 26 → Bool}
    (sub : x ≤ y) (off : W C w y=false) : W C w x=false := by
  apply Bool.eq_false_iff.mpr
  intro v
  have yes := true_of_le (PlaneOrdered.ordered 26 C hf w sub) v
  exact Bool.false_ne_true (off.symm.trans yes)

/-- On nonincident assignments with no point of the distinguished line, the first
operand is forced to be false, even when the assignment is far below a maximal one. -/
theorem first_off (C : Circuit) (hf : IsAO2 26 C) (a b : Nat) (neg : Reject C a b)
    (x y : V → Bool) (ind : ¬acc (Fin.append x y))
    (cold : ∀ p, Adj p 0 → x p=false) : W C a (Fin.append x y)=false := by
  let y' : V → Bool := fun l => decide (l=0) || y l
  have safe : ¬acc (Fin.append x y') := by
    apply neg_form.mpr
    intro p l edge xp
    by_cases z : l=0
    · subst l
      exact False.elim (Bool.false_ne_true ((cold p edge).symm.trans xp))
    · simpa [y',z] using neg_form.mp ind p l edge xp
  obtain ⟨p,sub,maxi⟩ := extend _ safe
  have l0 : opp p 0=true := by
    have := true_of_le (sub (LSlot 0)) (by change Fin.append x y' (Fin.natAdd 13 (0 : V))=true; rw [Fin.append_right]; simp [y'])
    simpa only [LSlot,Fin.append_right] using this
  have off := neg p maxi
  rw [if_pos l0] at off
  apply monoOff C hf a (le_trans (app_le le_rfl (show y ≤ y' from ?_)) sub) off
  intro l
  apply le_of_true_imp
  intro yes
  simp [y',yes]

/-- The second operand can only leak onto an independent input when the
distinguished line is present or every one of its four points meets a selected line. -/
theorem second_off (C : Circuit) (hf : IsAO2 26 C) (a b : Nat) (neg : Reject C a b)
    (x y : V → Bool) (ind : ¬acc (Fin.append x y)) (c : V) (central : Adj c 0)
    (empty : ∀ l, Adj c l → y l=false) : W C b (Fin.append x y)=false := by
  let x' : V → Bool := fun i => decide (i=c) || x i
  have safe : ¬acc (Fin.append x' y) := by
    apply neg_form.mpr
    intro p l edge xp
    by_cases e : p=c
    · subst p; exact empty l edge
    · exact neg_form.mp ind p l edge (by simpa [x',e] using xp)
  obtain ⟨p,sub,maxi⟩ := extend _ safe
  have cp : p c=true := by
    have := true_of_le (sub (PSlot c)) (by change Fin.append x' y (Fin.castAdd 13 c)=true; simp [Fin.append_left,x'])
    simpa only [PSlot,Fin.append_left] using this
  have l0 : ¬opp p 0=true := fun h => Bool.false_ne_true (((opp_true_iff p 0).mp h c central).symm.trans cp)
  have off := neg p maxi
  rw [if_neg l0] at off
  apply monoOff C hf b (le_trans (app_le (show x ≤ x' from ?_) le_rfl) sub) off
  intro i
  apply le_of_true_imp
  intro yes
  simp [x',yes]

theorem both_on (C : Circuit) (hf : IsAO2 26 C) (a b : Nat) (pos : Positive C a b)
    (z : Fin 26 → Bool) (on : acc z) : W C a z=true ∧ W C b z=true := by
  obtain ⟨p,l,edge,hp,hl⟩ := on
  have sub : probe p l ≤ z := by
    intro i
    apply le_of_true_imp
    intro hi
    have eq : i=Fin.castAdd 13 p ∨ i=Fin.natAdd 13 l := by simpa only [probe,decide_eq_true_eq] using hi
    rcases eq with rfl|rfl <;> assumption
  obtain ⟨wa,wb⟩ := pos p l edge
  exact ⟨true_of_le (PlaneOrdered.ordered 26 C hf a sub) wa,true_of_le (PlaneOrdered.ordered 26 C hf b sub) wb⟩

theorem both_compute_affine_restriction (C : Circuit) (hf : IsAO2 26 C) (a b : Nat)
    (pos : Positive C a b) (neg : Reject C a b) (x y : V → Bool)
    (centerOff : ∀ p, Adj p 0 → x p=false)
    (c : V) (c0 : Adj c 0) (directionOff : ∀ l, Adj c l → y l=false) :
    (W C a (Fin.append x y)=true ↔ acc (Fin.append x y)) ∧
    (W C b (Fin.append x y)=true ↔ acc (Fin.append x y)) := by
  by_cases h : acc (Fin.append x y)
  · obtain ⟨ha,hb⟩ := both_on C hf a b pos _ h
    exact ⟨⟨fun _ => h,fun _ => ha⟩,⟨fun _ => h,fun _ => hb⟩⟩
  · have ha := first_off C hf a b neg x y h centerOff
    have hb := second_off C hf a b neg x y h c c0 directionOff
    simp [h,ha,hb]

end Selector7832

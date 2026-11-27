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

namespace P19004.Count
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


theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

/-- The value of wire `w` on input `x`. -/
def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem two_list (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l = [a, b] ∨ l = [b, a] := by
  match l, hl with
  | [], _ => simp at ha
  | [u], _ =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [u, v], _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab

end P19004.Count
namespace P19004
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev V := Fin 13
abbrev W := Fin 26
def inc (p l : V) := (p.val+l.val)%13 ∈ ([0,1,3,9]:List Nat)
instance (p l : V) : Decidable (inc p l) := by unfold inc;infer_instance
def vec (X Y : Finset V) (i : W) : Bool :=
  if i.val<13 then decide (Fin.ofNat 13 i.val∈X) else decide (Fin.ofNat 13 i.val∈Y)
def spec (C : Circuit) := ∀ X Y : Finset V,C.eval (List.ofFn (vec X Y))=true ↔ ∃ p∈X,∃ l∈Y,inc p l
def P (x : W → Bool) := Finset.univ.filter fun p : V => x (Fin.castAdd 13 p)=true
def L (x : W → Bool) := Finset.univ.filter fun l : V => x (Fin.natAdd 13 l)=true
lemma recover (x : W→Bool) : vec (P x) (L x)=x := by
  funext i
  refine Fin.addCases (m:=13) (n:=13) (motive:=fun i => vec (P x) (L x) i=x i) ?_ ?_ i
  · intro p
    have f : ∀ t : V,(Fin.castAdd 13 t).val<13 ∧ Fin.ofNat 13 (Fin.castAdd 13 t).val=t := by decide +kernel
    simp [vec,(f p).1,(f p).2,P]
  · intro l
    have f : ∀ t : V,¬(Fin.natAdd 13 t).val<13 ∧ Fin.ofNat 13 (Fin.natAdd 13 t).val=t := by decide +kernel
    simp only [vec,if_neg (f l).1,(f l).2,L,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
    simp
def fire (x : W→Bool) := ∃p:V,∃l:V,inc p l ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
instance (x : W→Bool) : Decidable (fire x) := by unfold fire; infer_instance
theorem specAll {C : Circuit} (h : spec C) (x : W→Bool) : C.eval (List.ofFn x)=true ↔ fire x := by
  have z := h (P x) (L x)
  rw [recover] at z
  simp only [P,L,Finset.mem_filter,Finset.mem_univ,true_and] at z
  constructor
  · intro v; obtain ⟨p,hp,l,hl,hi⟩ := z.mp v; exact ⟨p,l,hi,hp,hl⟩
  · rintro ⟨p,l,hi,hp,hl⟩; exact z.mpr ⟨p,hp,l,hl,hi⟩

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
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

def allOR (C : Circuit) := (Finset.univ : Finset (Fin C.gates.length)).filter (fun g => (C.gates.get g).op=.or)
theorem allOR_card (C : Circuit) : (allOR C).card=(countedOR C).card := by
  have e : (allOR C).image Fin.val=countedOR C := by
    ext i
    simp only [Finset.mem_image,allOR,countedOR,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_range]
    constructor
    · rintro ⟨g,op,rfl⟩
      exact ⟨g.isLt,by simpa [List.getElem?_eq_getElem g.isLt] using op⟩
    · rintro ⟨hi,op⟩
      exact ⟨⟨i,hi⟩,by simpa [List.getElem?_eq_getElem hi] using op,rfl⟩
  rw [←e, Finset.card_image_of_injective _ Fin.val_injective]


open P19004.Count
def gateOr (C : Circuit) (i : Fin C.gates.length) (x : W→Bool) :=
  ∀ a∈(C.gates.get i).inputs, a<26+i.val ∧ val C.gates a x=true
def risen (C : Circuit) (x y : W→Bool) (i : Fin C.gates.length) : Prop :=
  (C.gates.get i).op=.or ∧ ¬gateOr C i x ∧ gateOr C i y
lemma valMono {C : Circuit} (hm : Monotone2 C) (w : Nat) {x y : W→Bool} (le : x≤y) :
    val C.gates w x=true → val C.gates w y=true :=
  PlaneOrdered.cmono (⟨C.gates,w⟩ : Circuit) (by intro g h;exact hm g h) 26 x y le
lemma riseMono {C : Circuit} (hm : Monotone2 C) {x y : W→Bool} (le : x≤y) (i : Fin C.gates.length) :
    gateOr C i x → gateOr C i y := by
  intro h a ha; exact ⟨(h a ha).1,valMono hm a le (h a ha).2⟩
lemma fresh {C : Circuit} (hm : Monotone2 C) (X B M U : W→Bool)
    (xU : X≤U) (bU : B≤U) (meet : ∀p:W,X p=true → B p=true → M p=true) :
    ∀ w, val C.gates w X=true → val C.gates w B=true → val C.gates w M=false →
    ∃ i : Fin C.gates.length, risen C B U i := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro x b m
    by_cases input : w<26
    · rw [val_input C.gates X w input] at x
      rw [val_input C.gates B w input] at b
      rw [val_input C.gates M w input] at m
      exact (Bool.false_ne_true (m.symm.trans (meet _ x b))).elim
    by_cases bounded : w<26+C.gates.length
    · let k := w-26
      have eq : w=26+k := by dsimp [k];omega
      have hk : k<C.gates.length := by omega
      have leg := hm C.gates[k] (List.getElem_mem hk)
      rcases (show C.gates[k].op=.and ∨ C.gates[k].op=.or by simpa using leg.1) with op|op
      · rw [eq,val_and C.gates _ k hk op] at x b
        have no : ¬∀ i∈C.gates[k].inputs,i<26+k ∧ val C.gates i M=true := by
          intro h; exact Bool.false_ne_true (m.symm.trans (by rw [eq]; exact (val_and C.gates _ k hk op).mpr h))
        push_neg at no
        obtain ⟨a,ha,bad⟩ := no
        obtain ⟨lt,xa⟩ := x a ha
        exact ih a (by omega) xa (b a ha).2 (by simpa using bad lt)
      · rw [eq,val_or C.gates _ k hk op] at x b
        obtain ⟨a,ha,la,xa⟩ := x
        obtain ⟨c,hc,lc,bc⟩ := b
        have off (t) (hmemb:t∈C.gates[k].inputs) (lt:t<26+k) : val C.gates t M=false := by
          apply Bool.eq_false_iff.mpr; intro oo
          exact Bool.false_ne_true (m.symm.trans (by rw [eq]; exact (val_or C.gates _ k hk op).mpr ⟨t,hmemb,lt,oo⟩))
        by_cases ab : val C.gates a B=true
        · exact ih a (by omega) xa ab (off a ha la)
        have ne : a≠c := by intro ac;subst c;exact ab bc
        have inputs : C.gates[k].inputs=[a,c] ∨ C.gates[k].inputs=[c,a] :=
          two_list _ leg.2 a c ha hc ne
        refine ⟨⟨k,hk⟩,op,fun z => ab (z a ha).2,?_⟩
        intro i hi
        change i∈C.gates[k].inputs at hi
        rcases inputs with s|s <;> rw [s] at hi <;>
          simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
        · rcases hi with rfl|rfl
          · exact ⟨la,valMono hm _ xU xa⟩
          · exact ⟨lc,valMono hm _ bU bc⟩
        · rcases hi with rfl|rfl
          · exact ⟨lc,valMono hm _ bU bc⟩
          · exact ⟨la,valMono hm _ xU xa⟩
    · have zero : val C.gates w X=false := by
        unfold val;rw [List.getD_eq_default _ _ (by rw [wf_len,List.length_ofFn];omega)]
      exact (Bool.false_ne_true (zero.symm.trans x)).elim

abbrev Step := Fin 20
def oldMasks : List Nat := [33579015, 33579023, 33579039, 33579295, 33579807, 33580831, 33584927, 33617695, 33617823, 33619871, 33685407, 33685471, 33816543, 33816575, 34078719, 34603007, 35651583, 37748735, 41943039, 50331647]
def newMasks : List Nat := [33579023, 33579039, 33579295, 33579807, 33580831, 33584927, 33617695, 33617823, 33619871, 33685407, 33685471, 33816543, 33816575, 34078719, 34603007, 35651583, 37748735, 41943039, 50331647, 67108863]
def flags : List Nat := [8200, 33554448, 16640, 8704, 33555456, 20480, 32770, 32896, 34816, 65537, 65600, 131584, 131104, 262160, 524296, 1048580, 2097154, 4194305, 8388616, 16777220]
def coreMask : Nat := 33579015
def bits (m:Nat) (i:W) := m.testBit i.val
def old (j:Step) := bits (oldMasks.getD j.val 0)
def new (j:Step) := bits (newMasks.getD j.val 0)
def edge (j:Step) := bits (flags.getD j.val 0)
def meetRow (j:Step) (p:W) := edge j p && old j p
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem witnessRows :
    (∀j:Step,fire (old j) ∧ fire (edge j) ∧ ¬fire (meetRow j) ∧
       (∀v:W,edge j v≤new j v) ∧ (∀v:W,old j v≤new j v)) ∧
    (∀ i j:Step, i<j → ∀v:W,new i v≤old j v) := by decide +kernel

noncomputable def present (C : Circuit) : Finset (Fin C.gates.length) := by
  classical; exact (allOR C).filter (fun i => gateOr C i (bits coreMask))
theorem coreLe : ∀ j:Step,∀v:W,bits coreMask v≤old j v := by decide +kernel

theorem corePlus20 (C : Circuit) (hm : Monotone2 C) (hg : spec C) :
    20+(present C).card≤{i : ℕ | ∃ g : Gate,C.gates[i]?=some g ∧ g.op=.or}.ncard := by
  classical
  have pick (s : Step) : ∃i:Fin C.gates.length,risen C (old s) (new s) i := by
    obtain ⟨ho,he,off,eu,ou⟩ := witnessRows.1 s
    exact fresh hm (edge s) (old s) (meetRow s) (new s) eu ou
      (by intro p ex ox; simp [meetRow,ex,ox]) C.output
      ((specAll hg _).mpr he) ((specAll hg _).mpr ho)
      (Bool.eq_false_iff.mpr (fun h => off ((specAll hg _).mp h)))
  choose idx hi' using pick
  have apart (a b : Step) (lt:a<b) : idx a ≠idx b := by
    intro eq
    have active := riseMono hm (witnessRows.2 a b lt) (idx a) (hi' a).2.2
    rw [eq] at active
    exact (hi' b).2.1 active
  have inj : Function.Injective idx := by
    intro a b eq
    rcases lt_trichotomy a b with h|h|h
    · exact (apart a b h eq).elim
    · exact h
    · exact (apart b a h eq.symm).elim
  have sub : Finset.univ.image idx ⊆ allOR C := by
    intro i h
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hi' s).1⟩
  have dis : Disjoint (Finset.univ.image idx) (present C) := by
    apply Finset.disjoint_left.mpr
    intro i hi hp
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hi
    exact (hi' s).2.1 (riseMono hm (coreLe s) _ (Finset.mem_filter.mp hp).2)
  have sub' : Finset.univ.image idx ∪ present C ⊆ allOR C :=
    Finset.union_subset sub (Finset.filter_subset _ _)
  have h := Finset.card_le_card sub'
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_fin] at h
  simpa only [ncardOR,←allOR_card] using h
end P19004

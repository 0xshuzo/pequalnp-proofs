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
    simp [lns]
    exact congrArg x eq
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
end Promise17245

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
end Promise17245


namespace PEqualNP.Outside.L_meta_6369

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK

private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  unfold Circuit.wires
  rw [foldl_append_length, List.length_ofFn]

private lemma wireVal_input {n : ℕ} (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wireVal n C i.val x = x i := by
  unfold wireVal Circuit.wires
  have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
  rw [foldl_append_getD_lt _ C.gates (List.ofFn x) false i.val hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

private lemma wireVal_ge {n : ℕ} (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w)
    (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [wires_length]; exact hw

private lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal n C w x) := by
  unfold wireVal Circuit.wires
  have hgate := foldl_append_getD_gate
    (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
    C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
  rw [List.length_ofFn] at hgate
  rw [hgate]
  change (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
    (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < (List.ofFn x).length + j := by
    rw [List.length_ofFn]
    exact hAO.2.1 j hj i hi
  exact foldl_append_take_getD _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt

private lemma wireVal_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma wireVal_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x =
      (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO hj, hop, inputs_eq_pair hAO hj]
  simp [GateOp.eval]

private lemma circuitFun_eq_wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = wireVal n C C.output x := rfl

private lemma orSets_length (n : ℕ) (C : Circuit) :
    (orSets n C).length = C.gates.length := by
  unfold orSets orStep
  rw [foldl_append_length]
  simp

private lemma orSets_getD_ge (n : ℕ) (C : Circuit) {j : ℕ} (hj : C.gates.length ≤ j) :
    (orSets n C).getD j [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [orSets_length]; exact hj

private lemma orSets_getD_lt_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = _
  rw [hprelen, ite_eq_left_of_eq_true _ _ (eq_true hop)]
  congr 1
  apply List.flatMap_congr
  intro w hw
  rw [List.mem_filter, decide_eq_true_eq] at hw
  have hlt : w - n < ([] : List (List ℕ)).length + j := by simp; omega
  exact foldl_append_take_getD _ C.gates [] [] j (w - n) (Nat.le_of_lt hj) hlt

private lemma orSets_getD_lt_not_or (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  let _ : DecidableEq GateOp := gateOpDecEq
  unfold orSets orStep
  have h := foldl_append_getD_gate
    (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else []))
    C.gates [] [] j hj ⟨GateOp.or, []⟩
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h]
  set pre := (C.gates.take j).foldl
    (fun cs (g : Gate) => cs ++ [cs.length :: (if g.op = GateOp.or then
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => cs.getD (w - n) [])
      else [])]) []
  have hprelen : pre.length = j := by
    rw [foldl_append_length, List.length_nil, Nat.zero_add, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt hj)]
  change pre.length :: (if (gateAt C j).op = GateOp.or then
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + pre.length))).flatMap
        (fun w => pre.getD (w - n) [])
      else []) = [j]
  rw [hprelen, ite_eq_right_of_eq_false _ _ (eq_false hop)]

private lemma orReaches_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (w g : ℕ) :
    OrReaches n C w g ↔
      ∃ j < C.gates.length, w = n + j ∧
        (g = j ∨ ((gateAt C j).op = GateOp.or ∧ ∃ b : Fin 2, OrReaches n C (opnd C j b) g)) := by
  constructor
  · rintro ⟨hnw, hmem⟩
    have hlt : w - n < C.gates.length := by
      by_contra hge
      push Not at hge
      rw [orSets_getD_ge n C hge] at hmem
      simp at hmem
    refine ⟨w - n, hlt, by omega, ?_⟩
    by_cases hop : (gateAt C (w - n)).op = GateOp.or
    · rw [orSets_getD_lt_or n C hlt hop, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Or.inl rfl
      · right
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨u, hu, hgu⟩
        rw [List.mem_filter, decide_eq_true_eq] at hu
        rw [inputs_eq_pair hAO hlt] at hu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu.1 with rfl | rfl
        · exact ⟨hop, 0, hu.2.1, hgu⟩
        · exact ⟨hop, 1, hu.2.1, hgu⟩
    · rw [orSets_getD_lt_not_or n C hlt hop, List.mem_singleton] at hmem
      exact Or.inl hmem
  · rintro ⟨j, hj, rfl, hcase⟩
    refine ⟨Nat.le_add_right n j, ?_⟩
    rw [Nat.add_sub_cancel_left]
    rcases hcase with rfl | ⟨hop, b, hnu, hgu⟩
    · by_cases hop : (gateAt C g).op = GateOp.or
      · rw [orSets_getD_lt_or n C hj hop]; exact List.mem_cons_self
      · rw [orSets_getD_lt_not_or n C hj hop]; exact List.mem_singleton_self g
    · rw [orSets_getD_lt_or n C hj hop, List.mem_cons]
      right
      rw [List.mem_flatMap]
      refine ⟨opnd C j b, ?_, hgu⟩
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨opnd_mem_inputs hAO hj b, hnu, opnd_lt hAO hj b⟩

private lemma orReaches_self {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_iff hAO (n + j) j).mpr ⟨j, hj, rfl, Or.inl rfl⟩

private lemma orReaches_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g → n + g ≤ w ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨_, b, hb⟩⟩
    · exact ⟨le_rfl, hj⟩
    · have hlt : opnd C j b < n + j := opnd_lt hAO hj b
      have hrec := ih _ hlt g hb
      exact ⟨by omega, hrec.2⟩

private lemma orReaches_trans {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g h : ℕ, OrReaches n C w g → OrReaches n C (n + g) h → OrReaches n C w h := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g h hwg hgh
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hgh
    · have hrec := ih _ (opnd_lt hAO hj b) g h hb hgh
      exact (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hrec⟩⟩

private lemma orReaches_parent {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      w = n + g ∨
        ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧ OrReaches n C w h ∧
          ∃ b : Fin 2, opnd C h b = n + g := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact Or.inl rfl
    · right
      rcases ih _ (opnd_lt hAO hj b) g hb with hEq | ⟨h, hh, hhop, hreach, b', hb'⟩
      · exact ⟨j, hj, hop, orReaches_self hAO hj, b, hEq⟩
      · exact ⟨h, hh, hhop, (orReaches_iff hAO (n + j) h).mpr ⟨j, hj, rfl, Or.inr ⟨hop, b, hreach⟩⟩, b', hb'⟩

private lemma wireVal_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w g : ℕ, OrReaches n C w g →
      ∀ x : Fin n → Bool, wireVal n C (n + g) x = true → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro g hwg x hxg
    rw [orReaches_iff hAO] at hwg
    rcases hwg with ⟨j, hj, rfl, rfl | ⟨hop, b, hb⟩⟩
    · exact hxg
    · have hsub := ih _ (opnd_lt hAO hj b) g hb x hxg
      rw [wireVal_or hAO hj hop, Bool.or_eq_true]
      fin_cases b
      · exact Or.inl hsub
      · exact Or.inr hsub

private lemma orIn_input {n : ℕ} {C : Circuit} (i : Fin n) :
    orIn n C i.val = {i} := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (hu | ⟨k, _, ⟨hni, _⟩, _, _⟩)
    · exact Fin.ext hu
    · omega
  · rintro rfl
    exact Or.inl rfl

private lemma orIn_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {w : ℕ}
    (hw : n + C.gates.length ≤ w) :
    orIn n C w = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hwk, _, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hwk
    rcases hwk with ⟨j, hj, rfl, _⟩
    omega

private lemma orIn_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext u
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro (hu | ⟨k, _, hjk, hkop, _⟩)
  · omega
  · rw [orReaches_iff hAO] at hjk
    rcases hjk with ⟨j', _, heq, hcase⟩
    have hjj' : j' = j := by omega
    subst hjj'
    rcases hcase with rfl | ⟨hor, _⟩
    · rw [hop] at hkop; cases hkop
    · rw [hop] at hor; cases hor

private lemma orIn_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  unfold orIn
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hjk, hkop, huk⟩)
    · omega
    · rw [orReaches_iff hAO] at hjk
      rcases hjk with ⟨j', _, heq, hcase⟩
      have hjj' : j' = j := by omega
      subst hjj'
      rcases hcase with rfl | ⟨_, b, hb⟩
      · rw [inputs_eq_pair hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · fin_cases b
        · exact Or.inl (Or.inr ⟨k, hk, hb, hkop, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hb, hkop, huk⟩)
  · rintro ((h0 | ⟨k, hk, h0k, hkop, huk⟩) | (h1 | ⟨k, hk, h1k, hkop, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h0]
      exact opnd_mem_inputs hAO hj 0
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, h0k⟩⟩
    · right
      refine ⟨j, hj, orReaches_self hAO hj, hop, ?_⟩
      rw [h1]
      exact opnd_mem_inputs hAO hj 1
    · right
      refine ⟨k, hk, ?_, hkop, huk⟩
      exact (orReaches_iff hAO (n + j) k).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, h1k⟩⟩

private lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w g : ℕ} (hwg : OrReaches n C w g) :
    orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hEq | ⟨k, hk, hgk, hkop, huk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans hAO w g k hwg hgk, hkop, huk⟩

private lemma wireVal_true_of_mem_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i : Fin n} {x : Fin n → Bool} (hxi : x i = true) :
    ∀ w : ℕ, i ∈ orIn n C w → wireVal n C w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hi
    by_cases hlt : w < n
    · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
      rw [heq, Finset.mem_singleton] at hi
      subst hi
      exact (wireVal_input C ⟨w, hlt⟩ x).trans hxi
    · by_cases hge : n + C.gates.length ≤ w
      · rw [orIn_ge hAO hge] at hi
        simp at hi
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hi ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [orIn_and hAO hj hop] at hi
          simp at hi
        · rw [orIn_or hAO hj hop, Finset.mem_union] at hi
          rw [wireVal_or hAO hj hop, Bool.or_eq_true]
          rcases hi with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

open Classical in
private noncomputable def bigOrReach (n : ℕ) (C : Circuit) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun g =>
    (gateAt C g).op = GateOp.or ∧ 2 ≤ (orIn n C (n + g)).card ∧ ∃ w ∈ W, OrReaches n C w g

private lemma leaf_count_bound {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ k : ℕ, ∀ W : Finset ℕ, (bigOrReach n C W).card = k →
      (W.biUnion (orIn n C)).card ≤ W.card + k := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro W hk
    by_cases hne : (bigOrReach n C W).Nonempty
    · set M := bigOrReach n C W
      set m := M.max' hne
      have hmM : m ∈ M := Finset.max'_mem M hne
      have hm_props : m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
          2 ≤ (orIn n C (n + m)).card ∧ ∃ w ∈ W, OrReaches n C w m := by
        simpa [M, bigOrReach, Finset.mem_filter, Finset.mem_range] using hmM
      have hmax_unique : ∀ w ∈ W, OrReaches n C w m → w = n + m := by
        intro w hw hwm
        have hle := orReaches_le hAO w m hwm
        rw [orReaches_iff hAO] at hwm
        rcases hwm with ⟨j, hj, rfl, hcase⟩
        by_contra hne_w
        have hmj : m ≠ j := fun h => hne_w (by omega)
        rcases hcase with hEq | ⟨hjop, b, hb⟩
        · exact hmj hEq
        · have hjM : j ∈ M := by
            simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
            refine ⟨hj, hjop, ?_, n + j, hw, orReaches_self hAO hj⟩
            have hsub : orIn n C (n + m) ⊆ orIn n C (n + j) :=
              orIn_subset_of_orReaches hAO
                ((orReaches_iff hAO (n + j) m).mpr ⟨j, hj, rfl, Or.inr ⟨hjop, b, hb⟩⟩)
            exact le_trans hm_props.2.2.1 (Finset.card_le_card hsub)
          have hjle : j ≤ m := Finset.le_max' M j hjM
          omega
      have hnmW : n + m ∈ W := by
        rcases hm_props.2.2.2 with ⟨w, hw, hwm⟩
        rwa [hmax_unique w hw hwm] at hw
      set W' : Finset ℕ := insert (opnd C m 0) (insert (opnd C m 1) (W.erase (n + m)))
      have hbi : W.biUnion (orIn n C) ⊆ W'.biUnion (orIn n C) := by
        intro u hu
        rw [Finset.mem_biUnion] at hu ⊢
        rcases hu with ⟨w, hw, huw⟩
        by_cases hwm : w = n + m
        · subst hwm
          rw [orIn_or hAO hm_props.1 hm_props.2.1, Finset.mem_union] at huw
          rcases huw with h0 | h1
          · exact ⟨opnd C m 0, by simp [W'], h0⟩
          · exact ⟨opnd C m 1, by simp [W'], h1⟩
        · exact ⟨w, by simp [W', hw, hwm], huw⟩
      have hW'card : W'.card ≤ W.card + 1 := by
        have h1 : W'.card ≤ (insert (opnd C m 1) (W.erase (n + m))).card + 1 :=
          Finset.card_insert_le _ _
        have h2 : (insert (opnd C m 1) (W.erase (n + m))).card ≤ (W.erase (n + m)).card + 1 :=
          Finset.card_insert_le _ _
        have h3 : (W.erase (n + m)).card + 1 = W.card := Finset.card_erase_add_one hnmW
        omega
      have hM'sub : bigOrReach n C W' ⊆ M.erase m := by
        intro g hg
        simp only [bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
        rcases hg with ⟨hglt, hgop, hgcard, w', hw', hw'g⟩
        rw [Finset.mem_erase]
        have hgM : g ∈ M := by
          simp only [M, bigOrReach, Finset.mem_filter, Finset.mem_range]
          refine ⟨hglt, hgop, hgcard, ?_⟩
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
          rcases hw' with rfl | rfl | ⟨_, hw'W⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 0, hw'g⟩⟩⟩
          · exact ⟨n + m, hnmW,
              (orReaches_iff hAO (n + m) g).mpr ⟨m, hm_props.1, rfl, Or.inr ⟨hm_props.2.1, 1, hw'g⟩⟩⟩
          · exact ⟨w', hw'W, hw'g⟩
        refine ⟨?_, hgM⟩
        intro hgm
        subst hgm
        simp only [W', Finset.mem_insert, Finset.mem_erase] at hw'
        rcases hw' with rfl | rfl | ⟨hne', hw'W⟩
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 0
          omega
        · have hle := (orReaches_le hAO _ _ hw'g).1
          have hlt := opnd_lt hAO hm_props.1 1
          omega
        · exact hne' (hmax_unique w' hw'W hw'g)
      have hM'card_le : (bigOrReach n C W').card ≤ (M.erase m).card :=
        Finset.card_le_card hM'sub
      have hMerase : (M.erase m).card + 1 = k := by
        rw [Finset.card_erase_add_one hmM, hk]
      have hM'lt : (bigOrReach n C W').card < k := by omega
      have hrec := ih _ hM'lt W' rfl
      have hbi_card : (W.biUnion (orIn n C)).card ≤ (W'.biUnion (orIn n C)).card :=
        Finset.card_le_card hbi
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hle1 : ∀ w ∈ W, (orIn n C w).card ≤ 1 := by
        intro w hw
        by_contra hgt
        push Not at hgt
        have hge2 : 2 ≤ (orIn n C w).card := hgt
        by_cases hlt : w < n
        · have heq : orIn n C w = {⟨w, hlt⟩} := orIn_input ⟨w, hlt⟩
          rw [heq, Finset.card_singleton] at hge2
          omega
        · by_cases hge : n + C.gates.length ≤ w
          · rw [orIn_ge hAO hge, Finset.card_empty] at hge2
            omega
          · set j := w - n
            have hwEq : w = n + j := by omega
            have hj : j < C.gates.length := by omega
            have hmem : gateAt C j ∈ C.gates := by
              unfold gateAt
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
              exact List.getElem_mem hj
            rw [hwEq] at hge2 hw
            rcases hAO.1 _ hmem with hop | hop
            · rw [orIn_and hAO hj hop, Finset.card_empty] at hge2
              omega
            · have hjM : j ∈ bigOrReach n C W := by
                simp only [bigOrReach, Finset.mem_filter, Finset.mem_range]
                exact ⟨hj, hop, hge2, n + j, hw, orReaches_self hAO hj⟩
              rw [hne] at hjM
              simp at hjM
      have hbi : (W.biUnion (orIn n C)).card ≤ ∑ w ∈ W, (orIn n C w).card :=
        Finset.card_biUnion_le
      have hsum : ∑ w ∈ W, (orIn n C w).card ≤ ∑ _w ∈ W, 1 :=
        Finset.sum_le_sum hle1
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
      omega

private lemma mem_insertNew {A : List (List ℕ)} {u v : List ℕ} :
    v ∈ insertNew A u ↔ v ∈ A ∨ v = u := by
  unfold insertNew
  split_ifs with h
  · constructor
    · intro hv; exact Or.inl hv
    · rintro (hv | rfl)
      · exact hv
      · exact h
  · simp

private lemma mem_foldl_insertNew {l acc : List (List ℕ)} {v : List ℕ} :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insertNew]
    tauto

private lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩

private lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  unfold readVectors
  rw [foldl_append_length, List.length_map, List.length_range]

private lemma readVectors_getD_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : n + C.gates.length ≤ w) :
    (readVectors C n S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [readVectors_length]; exact hw

private lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : w < n) :
    (readVectors C n S k).getD w [] = leafVectors S k w := by
  unfold readVectors
  have hlt : w < ((List.range n).map (leafVectors S k)).length := by
    rw [List.length_map, List.length_range]; exact hw
  rw [foldl_append_getD_lt _ C.gates ((List.range n).map (leafVectors S k)) [] w hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  simp

private lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]

private lemma mem_readVectors_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      v ∈ (readVectors C n S k).getD (opnd C j 0) [] ∨
      v ∈ (readVectors C n S k).getD (opnd C j 1) [] := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

private lemma mem_readVectors_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      ∃ u0 ∈ (readVectors C n S k).getD (opnd C j 0) [],
      ∃ u1 ∈ (readVectors C n S k).getD (opnd C j 1) [],
        v = capAdd k (capAdd k (S.map fun _ => 0) u0) u1 := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨t, ht, u1, hu1, rfl⟩
    rw [mem_andStep] at ht
    rcases ht with ⟨z, hz, u0, hu0, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u0, hu0, u1, hu1, rfl⟩
  · rintro ⟨u0, hu0, u1, hu1, rfl⟩
    refine ⟨capAdd k (S.map fun _ => 0) u0, ?_, u1, hu1, rfl⟩
    rw [mem_andStep]
    exact ⟨S.map fun _ => 0, List.mem_singleton_self _, u0, hu0, rfl⟩

private lemma readVectors_pair_inv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, ∀ v ∈ (readVectors C n [p.val, q.val] 1).getD w [],
      ∃ a b : ℕ, v = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp only [ite_true, hne, ite_false] at hv
          exact ⟨1, 0, hv, by omega, by omega, by omega⟩
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp only [hne, ite_false, ite_true] at hv
          exact ⟨0, 1, hv, by omega, by omega, by omega⟩
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, rfl⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 0) u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 1) u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          refine ⟨min (min (0 + a0) 2 + a1) 2, min (min (0 + b0) 2 + b1) 2, ?_,
            Nat.min_le_right _ _, Nat.min_le_right _ _, by omega⟩
          simp [capAdd]
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · exact ih _ (hw ▸ opnd_lt hAO hj 0) v h0
          · exact ih _ (hw ▸ opnd_lt hAO hj 1) v h1

private lemma readVectors_unit_left {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [1, 0] ∈ (readVectors C n [p.val, q.val] 1).getD w [] → p ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · rw [orIn_input p]; exact Finset.mem_singleton_self p
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp [hne] at hv
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          omega
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hv with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_unit_right {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [0, 1] ∈ (readVectors C n [p.val, q.val] 1).getD w [] → q ∈ orIn n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp [hne] at hv
        · rw [orIn_input q]; exact Finset.mem_singleton_self q
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          omega
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rw [orIn_or hAO hj hop, Finset.mem_union]
          rcases hv with h0 | h1
          · exact Or.inl (ih _ (hw ▸ opnd_lt hAO hj 0) h0)
          · exact Or.inr (ih _ (hw ▸ opnd_lt hAO hj 1) h1)

private lemma readVectors_pair_extract {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, [1, 1] ∈ (readVectors C n [p.val, q.val] 1).getD w [] →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C w a ∧
        ((p ∈ side C a 0 ∧ q ∈ side C a 1) ∨ (q ∈ side C a 0 ∧ p ∈ side C a 1)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp [hne] at hv
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp [hne] at hv
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv ⊢
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, heq⟩
          rcases readVectors_pair_inv hAO hpq _ u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases readVectors_pair_inv hAO hpq _ u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
            List.zipWith_nil_right, List.cons.injEq, and_true] at heq
          refine ⟨j, hj, hop, orReaches_self hAO hj, ?_⟩
          have hcases : (a0 = 1 ∧ b0 = 0 ∧ a1 = 0 ∧ b1 = 1) ∨
              (a0 = 0 ∧ b0 = 1 ∧ a1 = 1 ∧ b1 = 0) := by omega
          rcases hcases with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
          · exact Or.inl ⟨readVectors_unit_left hAO hpq _ hu0, readVectors_unit_right hAO hpq _ hu1⟩
          · exact Or.inr ⟨readVectors_unit_right hAO hpq _ hu0, readVectors_unit_left hAO hpq _ hu1⟩
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · rcases ih _ (hw ▸ opnd_lt hAO hj 0) h0 with ⟨a, ha, haop, hreach, hside⟩
            exact ⟨a, ha, haop,
              (orReaches_iff hAO (n + j) a).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 0, hreach⟩⟩, hside⟩
          · rcases ih _ (hw ▸ opnd_lt hAO hj 1) h1 with ⟨a, ha, haop, hreach, hside⟩
            exact ⟨a, ha, haop,
              (orReaches_iff hAO (n + j) a).mpr ⟨j, hj, rfl, Or.inr ⟨hop, 1, hreach⟩⟩, hside⟩

private lemma pairwise_lt_pair_eq {n : ℕ} {p q : Fin n} (hpq : p < q)
    {l : List (Fin n)} (hpw : l.Pairwise (· < ·))
    (hmem : ∀ x : Fin n, x ∈ l ↔ x = p ∨ x = q) :
    l = [p, q] := by
  cases l with
  | nil =>
    have hp := (hmem p).mpr (Or.inl rfl)
    simp at hp
  | cons a t =>
    rw [List.pairwise_cons] at hpw
    have ha : a = p ∨ a = q := (hmem a).mp List.mem_cons_self
    have hap : a = p := by
      rcases ha with h1 | h2
      · exact h1
      · have hp : p ∈ a :: t := (hmem p).mpr (Or.inl rfl)
        rw [List.mem_cons] at hp
        rcases hp with hEq | hpt
        · exact absurd (hEq.trans h2) (ne_of_lt hpq)
        · have hlt : a < p := hpw.1 p hpt
          rw [h2] at hlt
          exact absurd hlt (not_lt_of_gt hpq)
    subst a
    cases t with
    | nil =>
      have hq : q ∈ [p] := (hmem q).mpr (Or.inr rfl)
      rw [List.mem_singleton] at hq
      exact absurd hq (ne_of_gt hpq)
    | cons b t' =>
      rw [List.pairwise_cons] at hpw
      have hb : b = p ∨ b = q := (hmem b).mp (List.mem_cons_of_mem p List.mem_cons_self)
      have hpb : p < b := hpw.1 b List.mem_cons_self
      have hbq : b = q := by
        rcases hb with h1 | h2
        · rw [h1] at hpb
          exact absurd hpb (lt_irrefl p)
        · exact h2
      subst b
      cases t' with
      | nil => rfl
      | cons c t'' =>
        have hqc : q < c := hpw.2.1 c List.mem_cons_self
        have hc : c = p ∨ c = q :=
          (hmem c).mp (List.mem_cons_of_mem p (List.mem_cons_of_mem q List.mem_cons_self))
        rcases hc with h1 | h2
        · rw [h1] at hqc
          exact absurd (lt_trans hpq hqc) (lt_irrefl p)
        · rw [h2] at hqc
          exact absurd hqc (lt_irrefl q)

private lemma setList_pair {n : ℕ} {p q : Fin n} (hpq : p < q) :
    setList ({p, q} : Finset (Fin n)) = [p.val, q.val] := by
  unfold setList
  have hpw : ((List.finRange n).filter fun i => decide (i ∈ ({p, q} : Finset (Fin n)))).Pairwise (· < ·) := by
    apply List.Pairwise.filter
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp [hij]
  have hmem : ∀ x : Fin n,
      x ∈ (List.finRange n).filter (fun i => decide (i ∈ ({p, q} : Finset (Fin n)))) ↔
        x = p ∨ x = q := by
    intro x
    simp
  rw [pairwise_lt_pair_eq hpq hpw hmem]
  simp

private lemma isPrimeImplicant_edge {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit}
    (hcomp : ∀ x : Fin n → Bool, circuitFun n C x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    {p q : Fin n} (hadj : G.Adj p q) :
    IsPrimeImplicant n C {p, q} := by
  have hpq : p ≠ q := G.ne_of_adj hadj
  refine ⟨?_, ?_⟩
  · rw [hcomp, decide_eq_true_eq]
    exact ⟨p, q, hadj, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    rw [Finset.mem_ssubsets] at hT
    rw [hcomp, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [setInput, decide_eq_true_eq] at hu hv
    have huv_ne : u ≠ v := G.ne_of_adj huv
    have hu_mem : u ∈ ({p, q} : Finset (Fin n)) := hT.1 hu
    have hv_mem : v ∈ ({p, q} : Finset (Fin n)) := hT.1 hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu_mem hv_mem
    have hsub : ({p, q} : Finset (Fin n)) ⊆ T := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hu_mem with rfl | rfl <;> rcases hv_mem with rfl | rfl
      · exact absurd rfl huv_ne
      · rcases hx with rfl | rfl <;> assumption
      · rcases hx with rfl | rfl <;> assumption
      · exact absurd rfl huv_ne
    exact hT.2 hsub

private lemma edge_has_and_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ∀ x : Fin n → Bool, circuitFun n C x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hR1 : IsReadK n C 1) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      ((u ∈ side C a 0 ∧ v ∈ side C a 1) ∨ (v ∈ side C a 0 ∧ u ∈ side C a 1)) := by
  suffices hord : ∀ p q : Fin n, G.Adj p q → p < q →
      ∃ a < C.gates.length, (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
        ((p ∈ side C a 0 ∧ q ∈ side C a 1) ∨ (q ∈ side C a 0 ∧ p ∈ side C a 1)) by
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
    · exact hord u v hadj hlt
    · rcases hord v u hadj.symm hgt with ⟨a, ha, hop, hreach, hside⟩
      exact ⟨a, ha, hop, hreach, hside.symm⟩
  intro p q hpq_adj hpq_lt
  have hpq : p ≠ q := ne_of_lt hpq_lt
  have hpi : IsPrimeImplicant n C {p, q} := isPrimeImplicant_edge hcomp hpq_adj
  have hrm : readsAtMost C n (setList ({p, q} : Finset (Fin n))) 1 = true := hR1 {p, q} hpi
  rw [setList_pair hpq_lt] at hrm
  unfold readsAtMost at hrm
  rw [List.any_eq_true] at hrm
  rcases hrm with ⟨vec, hvec_mem, hvec_all⟩
  rcases readVectors_pair_inv hAO hpq C.output vec hvec_mem with ⟨a, b, rfl, ha2, hb2, hab1⟩
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hvec_all
  have hcases : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 1) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hp_in : p ∈ orIn n C C.output := readVectors_unit_left hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = p)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hp_in
    have hcf : circuitFun n C (fun i => decide (i = p)) = true := hval
    rw [hcomp, decide_eq_true_eq] at hcf
    rcases hcf with ⟨x, y, hxy, hx, hy⟩
    simp only [decide_eq_true_eq] at hx hy
    subst hx; subst hy
    exact absurd rfl (G.ne_of_adj hxy)
  · have hq_in : q ∈ orIn n C C.output := readVectors_unit_right hAO hpq C.output hvec_mem
    have hval : wireVal n C C.output (fun i => decide (i = q)) = true :=
      wireVal_true_of_mem_orIn hAO (by simp) C.output hq_in
    have hcf : circuitFun n C (fun i => decide (i = q)) = true := hval
    rw [hcomp, decide_eq_true_eq] at hcf
    rcases hcf with ⟨x, y, hxy, hx, hy⟩
    simp only [decide_eq_true_eq] at hx hy
    subst hx; subst hy
    exact absurd rfl (G.ne_of_adj hxy)
  · exact readVectors_pair_extract hAO hpq C.output hvec_mem

private def BelowG (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit) (g : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wireVal n C (n + g) x = true →
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

private lemma belowG_of_orReaches {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ∀ x : Fin n → Bool, circuitFun n C x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    {g : ℕ} (hreach : OrReaches n C C.output g) :
    BelowG n G C g := by
  intro x hxg
  have hout : wireVal n C C.output x = true := wireVal_of_orReaches hAO C.output g hreach x hxg
  have hcf : circuitFun n C x = true := hout
  rw [hcomp, decide_eq_true_eq] at hcf
  exact hcf

private lemma adj_of_and_orReaches {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C)
    (hcomp : ∀ x : Fin n → Bool, circuitFun n C x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    {a : ℕ} (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hreach : OrReaches n C C.output a) {u v : Fin n}
    (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
    G.Adj u v := by
  have h0 : wireVal n C (opnd C a 0) (pairInput u v) = true :=
    wireVal_true_of_mem_orIn hAO (by simp [pairInput]) _ hu
  have h1 : wireVal n C (opnd C a 1) (pairInput u v) = true :=
    wireVal_true_of_mem_orIn hAO (by simp [pairInput]) _ hv
  have ha_val : wireVal n C (n + a) (pairInput u v) = true := by
    rw [wireVal_and hAO ha hop, Bool.and_eq_true]
    exact ⟨h0, h1⟩
  rcases belowG_of_orReaches hAO hcomp hreach (pairInput u v) ha_val with ⟨p, q, hpq, hp, hq⟩
  simp only [pairInput, decide_eq_true_eq] at hp hq
  have hne : p ≠ q := G.ne_of_adj hpq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hne
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl hne

private lemma main_theorem (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hNoC4 : NoFourCycle G) (hAO : IsAO2 n C)
    (hcomp : ∀ x : Fin n → Bool, circuitFun n C x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hR1 : IsReadK n C 1) :
    ∃ S : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
      G.edgeFinset.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hempty : G.edgeFinset = ∅
  · refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [hempty] at hmem
      simp at hmem
    · rw [hempty]
      simp
  · have hne_edges : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hne_edges with ⟨e0, he0⟩
    have hn_pos : 0 < n := by
      rcases e0 with ⟨u0, v0⟩
      exact Fin.pos u0
    let v0 : Fin n := ⟨0, hn_pos⟩
    let A_used : Finset ℕ := (Finset.range C.gates.length).filter fun a =>
      (gateAt C a).op = GateOp.and ∧ OrReaches n C C.output a ∧
      (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty
    let OrTop : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ OrReaches n C C.output g
    let OrBot : Finset ℕ := (Finset.range C.gates.length).filter fun g =>
      (gateAt C g).op = GateOp.or ∧ ¬ BelowG n G C g
    have hA_star : ∀ a ∈ A_used, (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
      intro a ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at ha
      rcases ha with ⟨halt, haop, hreach, hne0, hne1⟩
      by_contra hboth
      push Not at hboth
      have hpos0 : 0 < (side (n := n) C a 0).card := Finset.Nonempty.card_pos hne0
      have hpos1 : 0 < (side (n := n) C a 1).card := Finset.Nonempty.card_pos hne1
      have hgt0 : 1 < (side (n := n) C a 0).card := by omega
      have hgt1 : 1 < (side (n := n) C a 1).card := by omega
      rcases Finset.one_lt_card.mp hgt0 with ⟨u1, hu1, u2, hu2, hune⟩
      rcases Finset.one_lt_card.mp hgt1 with ⟨w1, hw1, w2, hw2, hwne⟩
      exact no_four_cycle hNoC4 hune hwne
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu1 hw2)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw1)
        (adj_of_and_orReaches hAO hcomp halt haop hreach hu2 hw2)
    let ctrSide : ℕ → Fin 2 := fun a => if (side (n := n) C a 0).card = 1 then 0 else 1
    let leafSide : ℕ → Fin 2 := fun a => 1 - ctrSide a
    let ctr : ℕ → Fin n := fun a =>
      if h : (side (n := n) C a (ctrSide a)).Nonempty then h.choose else v0
    have hctr_eq : ∀ a ∈ A_used, side (n := n) C a (ctrSide a) = {ctr a} := by
      intro a ha
      have hcard1 : (side (n := n) C a (ctrSide a)).card = 1 := by
        simp only [ctrSide]
        split_ifs with h0
        · exact h0
        · exact (hA_star a ha).resolve_left h0
      have hne_c : (side (n := n) C a (ctrSide a)).Nonempty :=
        Finset.card_pos.mp (by omega)
      have hmem_c : ctr a ∈ side (n := n) C a (ctrSide a) := by
        simp only [ctr, hne_c, ↓reduceDIte]
        exact hne_c.choose_spec
      rcases Finset.card_eq_one.mp hcard1 with ⟨c, hc⟩
      rw [hc, Finset.mem_singleton] at hmem_c
      rw [hc, hmem_c]
    have hctr_adj : ∀ a ∈ A_used, ∀ u ∈ side (n := n) C a (leafSide a), G.Adj (ctr a) u := by
      intro a ha u hu
      have hA_mem := ha
      simp only [A_used, Finset.mem_filter, Finset.mem_range] at hA_mem
      rcases hA_mem with ⟨halt, haop, hreach, _, _⟩
      have hc_mem : ctr a ∈ side (n := n) C a (ctrSide a) := by
        rw [hctr_eq a ha]; exact Finset.mem_singleton_self _
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      rcases hcs with h0 | h1
      · have hl : leafSide a = 1 := by simp [leafSide, h0]
        rw [h0] at hc_mem
        rw [hl] at hu
        exact adj_of_and_orReaches hAO hcomp halt haop hreach hc_mem hu
      · have hl : leafSide a = 0 := by simp [leafSide, h1]
        rw [h1] at hc_mem
        rw [hl] at hu
        exact (adj_of_and_orReaches hAO hcomp halt haop hreach hu hc_mem).symm
    let S : Finset (Fin n) := A_used.image ctr
    have hS_le : S.card ≤ A_used.card := Finset.card_image_le
    have hS_cover : ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S := by
      intro u v huv
      rcases edge_has_and_gate hAO hcomp hR1 huv with ⟨a, ha, hop, hreach, hside⟩
      have haA : a ∈ A_used := by
        simp only [A_used, Finset.mem_filter, Finset.mem_range]
        rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
        · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
        · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
      have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
      have hceq := hctr_eq a haA
      rcases hcs with h0 | h1
      · rw [h0] at hceq
        rcases hside with ⟨hu0, _⟩ | ⟨hv0, _⟩
        · rw [hceq, Finset.mem_singleton] at hu0
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu0.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hv0
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv0.symm⟩)
      · rw [h1] at hceq
        rcases hside with ⟨_, hv1⟩ | ⟨_, hu1⟩
        · rw [hceq, Finset.mem_singleton] at hv1
          exact Or.inr (Finset.mem_image.mpr ⟨a, haA, hv1.symm⟩)
        · rw [hceq, Finset.mem_singleton] at hu1
          exact Or.inl (Finset.mem_image.mpr ⟨a, haA, hu1.symm⟩)
    have hdisj_A_OrTop : Disjoint A_used OrTop := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrTop, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_A_OrBot : Disjoint A_used OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [A_used, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rw [hg1.2.1] at hg2
      cases hg2.2.1
    have hdisj_OrTop_OrBot : Disjoint OrTop OrBot := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [OrTop, OrBot, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      exact hg2.2.2 (belowG_of_orReaches hAO hcomp hg1.2.2)
    have hsum_gates : A_used.card + OrTop.card + OrBot.card ≤ C.gates.length := by
      have hdisj1 : Disjoint (A_used ∪ OrTop) OrBot :=
        Finset.disjoint_union_left.mpr ⟨hdisj_A_OrBot, hdisj_OrTop_OrBot⟩
      have hcard_u : (A_used ∪ OrTop ∪ OrBot).card = A_used.card + OrTop.card + OrBot.card := by
        rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj_A_OrTop]
      rw [← hcard_u]
      calc (A_used ∪ OrTop ∪ OrBot).card
          ≤ (Finset.range C.gates.length).card := by
            apply Finset.card_le_card
            intro g hg
            simp only [A_used, OrTop, OrBot, Finset.mem_union, Finset.mem_filter,
              Finset.mem_range] at hg ⊢
            omega
        _ = C.gates.length := Finset.card_range _
    have hA_le_OrTop : A_used.card ≤ OrTop.card + 1 := by
      let U : Finset ℕ := A_used ∪ OrTop
      let V : Finset ℕ := U.image fun g => n + g
      have hV_card : V.card = A_used.card + OrTop.card := by
        have hinj : Function.Injective (fun g : ℕ => n + g) := add_right_injective n
        rw [Finset.card_image_of_injective U hinj, Finset.card_union_of_disjoint hdisj_A_OrTop]
      have hV_sub : V ⊆ insert C.output
          ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2) := by
        intro w hw
        simp only [V, Finset.mem_image] at hw
        rcases hw with ⟨g, hgU, rfl⟩
        have hreach : OrReaches n C C.output g := by
          simp only [U, A_used, OrTop, Finset.mem_union, Finset.mem_filter, Finset.mem_range] at hgU
          rcases hgU with hgA | hgO
          · exact hgA.2.2.1
          · exact hgO.2.2
        rw [Finset.mem_insert]
        rcases orReaches_parent hAO C.output g hreach with hEq | ⟨h, hh, hhop, hhreach, b, hb⟩
        · exact Or.inl hEq.symm
        · right
          rw [Finset.mem_image]
          refine ⟨(h, b), ?_, hb⟩
          rw [Finset.mem_product]
          refine ⟨?_, Finset.mem_univ b⟩
          simp only [OrTop, Finset.mem_filter, Finset.mem_range]
          exact ⟨hh, hhop, hhreach⟩
      have hcard_le : V.card ≤ OrTop.card * 2 + 1 := by
        calc V.card
            ≤ (insert C.output
                ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2)).card :=
              Finset.card_le_card hV_sub
          _ ≤ ((OrTop ×ˢ (Finset.univ : Finset (Fin 2))).image fun p => opnd C p.1 p.2).card + 1 :=
              Finset.card_insert_le _ _
          _ ≤ (OrTop ×ˢ (Finset.univ : Finset (Fin 2))).card + 1 :=
              Nat.add_le_add_right Finset.card_image_le 1
          _ = OrTop.card * 2 + 1 := by simp [Finset.card_product]
      omega
    let Kc : Fin n → Finset ℕ := fun c => A_used.filter fun a => ctr a = c
    let Wc : Fin n → Finset ℕ := fun c => (Kc c).image fun a => opnd C a (leafSide a)
    let Lc : Fin n → Finset (Fin n) := fun c => (Wc c).biUnion (orIn n C)
    let Mc : Fin n → Finset ℕ := fun c => bigOrReach n C (Wc c)
    have hE_sub : G.edgeFinset ⊆ S.biUnion fun c => (Lc c).image fun u => s(c, u) := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
        rcases edge_has_and_gate hAO hcomp hR1 huv with ⟨a, ha, hop, hreach, hside⟩
        have haA : a ∈ A_used := by
          simp only [A_used, Finset.mem_filter, Finset.mem_range]
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · exact ⟨ha, hop, hreach, ⟨u, hu0⟩, ⟨v, hv1⟩⟩
          · exact ⟨ha, hop, hreach, ⟨v, hv0⟩, ⟨u, hu1⟩⟩
        have hcS : ctr a ∈ S := Finset.mem_image.mpr ⟨a, haA, rfl⟩
        have haK : a ∈ Kc (ctr a) := by
          simp [Kc, haA]
        have hwW : opnd C a (leafSide a) ∈ Wc (ctr a) :=
          Finset.mem_image.mpr ⟨a, haK, rfl⟩
        rw [Finset.mem_biUnion]
        refine ⟨ctr a, hcS, ?_⟩
        rw [Finset.mem_image]
        have hcs : ctrSide a = 0 ∨ ctrSide a = 1 := by simp only [ctrSide]; split_ifs <;> simp
        have hceq := hctr_eq a haA
        rcases hcs with h0 | h1
        · have hl : leafSide a = 1 := by simp [leafSide, h0]
          rw [h0] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hu0
            refine ⟨v, ?_, by rw [hu0]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv1⟩
          · rw [hceq, Finset.mem_singleton] at hv0
            refine ⟨u, ?_, by rw [hv0, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu1⟩
        · have hl : leafSide a = 0 := by simp [leafSide, h1]
          rw [h1] at hceq
          rcases hside with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
          · rw [hceq, Finset.mem_singleton] at hv1
            refine ⟨u, ?_, by rw [hv1, Sym2.eq_swap]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hu0⟩
          · rw [hceq, Finset.mem_singleton] at hu1
            refine ⟨v, ?_, by rw [hu1]⟩
            rw [Finset.mem_biUnion]
            exact ⟨opnd C a (leafSide a), hwW, by rw [hl]; exact hv0⟩
    have hE_le : G.edgeFinset.card ≤ ∑ c ∈ S, (Lc c).card := by
      calc G.edgeFinset.card
          ≤ (S.biUnion fun c => (Lc c).image fun u => s(c, u)).card := Finset.card_le_card hE_sub
        _ ≤ ∑ c ∈ S, ((Lc c).image fun u => s(c, u)).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ S, (Lc c).card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hLc_le : ∀ c ∈ S, (Lc c).card ≤ (Kc c).card + (Mc c).card := by
      intro c _
      have h1 := leaf_count_bound hAO (Mc c).card (Wc c) rfl
      have h2 : (Wc c).card ≤ (Kc c).card := Finset.card_image_le
      exact le_trans h1 (Nat.add_le_add_right h2 _)
    have hK_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Kc := by
      intro c1 _ c2 _ hne
      change Disjoint (Kc c1) (Kc c2)
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      exact hne (ha1.2.symm.trans ha2.2)
    have hsum_K : ∑ c ∈ S, (Kc c).card ≤ A_used.card := by
      rw [← Finset.card_biUnion hK_disj]
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_biUnion] at ha
      rcases ha with ⟨c, _, hac⟩
      exact (Finset.mem_filter.mp hac).1
    have hM_sub : ∀ c ∈ S, Mc c ⊆ OrBot := by
      intro c _ g hg
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg
      rcases hg with ⟨hglt, hgop, hgcard, _, _, _⟩
      simp only [OrBot, Finset.mem_filter, Finset.mem_range]
      refine ⟨hglt, hgop, ?_⟩
      intro hbelow
      have hne_g : (orIn n C (n + g)).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne_g with ⟨u, hu⟩
      have hval : wireVal n C (n + g) (fun i => decide (i = u)) = true :=
        wireVal_true_of_mem_orIn hAO (by simp) (n + g) hu
      rcases hbelow (fun i => decide (i = u)) hval with ⟨p, q, hpq, hp, hq⟩
      simp only [decide_eq_true_eq] at hp hq
      subst hp; subst hq
      exact absurd rfl (G.ne_of_adj hpq)
    have hM_disj : Set.PairwiseDisjoint (S : Set (Fin n)) Mc := by
      intro c1 _ c2 _ hne
      change Disjoint (Mc c1) (Mc c2)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      simp only [Mc, bigOrReach, Finset.mem_filter, Finset.mem_range] at hg1 hg2
      rcases hg1 with ⟨_, _, hgcard, w1, hw1, hw1g⟩
      rcases hg2 with ⟨_, _, _, w2, hw2, hw2g⟩
      simp only [Wc, Finset.mem_image] at hw1 hw2
      rcases hw1 with ⟨a1, ha1, rfl⟩
      rcases hw2 with ⟨a2, ha2, rfl⟩
      simp only [Kc, Finset.mem_filter] at ha1 ha2
      have hgt1 : 1 < (orIn n C (n + g)).card := by omega
      rcases Finset.one_lt_card.mp hgt1 with ⟨u1, hu1, u2, hu2, hune⟩
      have hsub1 : orIn n C (n + g) ⊆ side C a1 (leafSide a1) := orIn_subset_of_orReaches hAO hw1g
      have hsub2 : orIn n C (n + g) ⊆ side C a2 (leafSide a2) := orIn_subset_of_orReaches hAO hw2g
      have h1u1 : G.Adj c1 u1 := ha1.2 ▸ hctr_adj a1 ha1.1 u1 (hsub1 hu1)
      have h1u2 : G.Adj c1 u2 := ha1.2 ▸ hctr_adj a1 ha1.1 u2 (hsub1 hu2)
      have h2u1 : G.Adj c2 u1 := ha2.2 ▸ hctr_adj a2 ha2.1 u1 (hsub2 hu1)
      have h2u2 : G.Adj c2 u2 := ha2.2 ▸ hctr_adj a2 ha2.1 u2 (hsub2 hu2)
      exact no_four_cycle hNoC4 hne hune h1u1 h1u2 h2u1 h2u2
    have hsum_M : ∑ c ∈ S, (Mc c).card ≤ OrBot.card := by
      rw [← Finset.card_biUnion hM_disj]
      apply Finset.card_le_card
      intro g hg
      rw [Finset.mem_biUnion] at hg
      rcases hg with ⟨c, hcS, hgc⟩
      exact hM_sub c hcS hgc
    have hE_bound : G.edgeFinset.card ≤ A_used.card + OrBot.card := by
      calc G.edgeFinset.card
          ≤ ∑ c ∈ S, (Lc c).card := hE_le
        _ ≤ ∑ c ∈ S, ((Kc c).card + (Mc c).card) := Finset.sum_le_sum hLc_le
        _ = (∑ c ∈ S, (Kc c).card) + ∑ c ∈ S, (Mc c).card := Finset.sum_add_distrib
        _ ≤ A_used.card + OrBot.card := Nat.add_le_add hsum_K hsum_M
    refine ⟨S, hS_cover, ?_⟩
    change G.edgeFinset.card + S.card ≤ C.gates.length + 1
    omega

end PEqualNP.Outside.L_meta_6369

theorem PEqualNP.Outside.L_meta_6369 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsAO2 x1 x4 → (∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) → PEqualNP.ReadK.IsReadK x1 x4 (1 : ℕ) → ∃ (x9 : Finset (Fin x1)), (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ x2.edgeFinset.card + x9.card ≤ x4.size + (1 : ℕ) :=
  fun x1 x2 _ x4 hNoC4 hAO hcomp hR1 =>
    PEqualNP.Outside.L_meta_6369.main_theorem x1 x2 x4 hNoC4 hAO hcomp hR1


namespace PEqualNP.Outside.L_meta_1527

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

end PEqualNP.Outside.L_meta_1527

theorem PEqualNP.Outside.L_meta_1527 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size :=
  PEqualNP.Outside.L_meta_1527.main_aux

namespace PEqualNP.Outside.L_meta_8567_aux

namespace A1527

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

end A1527

namespace A1501

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

end A1501
namespace Glue

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem exists_least (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C' : Circuit)
    (h1 : PEqualNP.TopForm.IsAO2 n C') (h2 : circuitFun n C' = graphFun G ∅) :
    ∃ C : Circuit, PEqualNP.TopForm.IsLeastAO G C ∧ C.size ≤ C'.size := by
  classical
  have hex : ∃ k : ℕ, ∃ C : Circuit, PEqualNP.TopForm.IsAO2 n C ∧ circuitFun n C = graphFun G ∅ ∧
      C.size = k := ⟨_, C', h1, h2, rfl⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := Nat.find_spec hex
  refine ⟨C, ⟨hC1, hC2, ?_⟩, ?_⟩
  · intro D hD1 hD2
    rw [hC3]
    exact Nat.find_min' hex ⟨D, hD1, hD2, rfl⟩
  · rw [hC3]
    exact Nat.find_min' hex ⟨C', h1, h2, rfl⟩

end Glue


theorem base4181 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x8 ∧ PEqualNP.TopForm.TopForm x2 x8 ∧ x8.size ≤ x4.size := by
  classical
  intro x1 x2 x3 x4 hne hm hf
  have hf' : ∀ x : Fin x1 → Bool,
      x4.eval (List.ofFn x) = true ↔ ∃ u v : Fin x1, x2.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    have h : x4.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ x :=
      congrFun hf x
    have hg : PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ x =
        Decidable.decide (∃ u v : Fin x1, x2.Adj u v ∧ x u = true ∧ x v = true) := by
      simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
    rw [h, hg, decide_eq_true_iff]
  obtain ⟨C1, hA, hF, hS⟩ :=
    PEqualNP.Outside.L_meta_8567_aux.A1527.main_aux x1 x2 x3 x4 hm hf'
  obtain ⟨C2, hL2, hS2⟩ := PEqualNP.Outside.L_meta_8567_aux.Glue.exists_least x1 x2 C1 hA hF
  obtain ⟨C3, hL3, hS3, -, hT3⟩ :=
    PEqualNP.Outside.L_meta_8567_aux.A1501.main_ind x1 x2 hne _ C2 hL2 rfl
  exact ⟨C3, hL3, hT3, by omega⟩

end PEqualNP.Outside.L_meta_8567_aux


theorem PEqualNP.Outside.L_meta_8567 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x2 x8 ∧ PEqualNP.TopForm.TopForm x2 x8 ∧ x8.size ≤ x4.size := by
  intro n G _ C hE hC hf
  refine PEqualNP.Outside.L_meta_8567_aux.base4181 n G C hE ?_ hf
  intro g hg
  refine ⟨?_, ?_⟩
  · rcases hC.1 g hg with h | h <;> simp [h]
  · rw [hC.2.2 g hg]

namespace PEqualNP.Outside.L_meta_8933

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

def reachable (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (n + k = C.output ∨ InCone n C k (C.output - n))

lemma reachable_child {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k j : ℕ} (hk : reachable n C k) (hj : n + j ∈ (gateAt C k).inputs) :
    reachable n C j := by
  have hlt := rb k hk.1 (n + j) hj
  have hbound := hk.1
  refine ⟨by omega, Or.inr ?_⟩
  have hcone : InCone n C j k := (inCone_iff n C j k).2
    ⟨hk.1, j, by omega, hj, Or.inl rfl⟩
  rcases hk.2 with h | h
  · rwa [show C.output - n = k by omega]
  · exact inCone_trans n C j k hcone _ h

lemma cone_reader {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) :
    ∃ k, k < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧
      n + i ∈ (gateAt C k).inputs := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨hj, k, hkj, hin, rfl | hc⟩ := (inCone_iff n C i j).1 h
    · exact ⟨j, hj, Or.inl rfl, hin⟩
    · obtain ⟨l, hl, rfl | hlc, hread⟩ := ih k hkj hc
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, l, hkj, hin, Or.inl rfl⟩), hread⟩
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, k, hkj, hin, Or.inr hlc⟩), hread⟩

lemma reachable_reader {n : ℕ} {C : Circuit} {i : ℕ}
    (hi : reachable n C i) (hne : i ≠ C.output - n) :
    ∃ k, reachable n C k ∧ n + i ∈ (gateAt C k).inputs := by
  rcases hi.2 with he | hc
  · omega
  · obtain ⟨k, hk, hr | hr, hin⟩ := cone_reader hc
    · have hn : n ≤ C.output := by
        by_contra h
        obtain ⟨_, j, hj, _, _⟩ := (inCone_iff n C i (C.output - n)).1 hc
        omega
      exact ⟨k, ⟨hk, Or.inl (by omega)⟩, hin⟩
    · exact ⟨k, ⟨hk, Or.inr hr⟩, hin⟩

def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (pairInput u u)) w = true

lemma mem_support {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ singletonSupport n C w ↔ val C (List.ofFn (pairInput u u)) w = true := by
  simp [singletonSupport]

lemma support_input {n : ℕ} {C : Circuit} (u : Fin n) :
    singletonSupport n C u.val = {u} := by
  ext v
  rw [mem_support, val_ofFn]
  simp [pairInput, eq_comm]

lemma support_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ singletonSupport n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_or (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun ⟨w, hw, _, ht⟩ => ⟨w, hw, ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, rb k hk w hw, ht⟩⟩

lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1

lemma input_card {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs.toFinset.card ≤ 2 :=
  (List.toFinset_card_le _).trans (hm _ (gateAt_mem hk)).2

noncomputable def births (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty

lemma mem_births {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ births n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty := by
  classical
  simp only [births, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty

lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]

noncomputable def merges (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card

lemma mem_merges {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ merges n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card := by
  classical
  simp only [merges, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

-- Each reachable wire with empty singleton support other than the output
-- is read by some reachable gate. Counting these reads pays for connecting
-- the edge-producing AND gates, even when the circuit shares subcircuits.
lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    2 * (births n C).card + (merges n C).card ≤ C.size + 1 := by
  classical
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let Z := R.filter fun k => singletonSupport n C (n + k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w - n
  have hR (k) : k ∈ R ↔ reachable n C k := by
    simp only [R, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n + k) = ∅ := Finset.mem_filter
  have hread : Z.erase (C.output - n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hj
    obtain ⟨k, hk, hin⟩ := reachable_reader ((hR j).1 ((hZ j).1 hz).1) hne
    refine Finset.mem_biUnion.2 ⟨k, (hR k).2 hk, Finset.mem_image.2 ⟨n + j, ?_, by omega⟩⟩
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hin, by omega, ((hZ j).1 hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output - n)).card + 1 := by
        by_cases h : C.output - n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread) _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + 2 * (if k ∈ births n C then 1 else 0) +
      (if k ∈ merges n C then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hr := (hR k).1 hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.1 hd).2.2
      simpa [he] using (mem_positiveInputs.1 hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm hr.1)
    by_cases hb : k ∈ births n C
    · obtain ⟨_, hop, a, b, hab, ha, hb'⟩ := mem_births.1 hb
      have hz := (hZ k).2 ⟨hk, hclean k hr hop⟩
      have hl : k ∉ merges n C := by
        intro h
        have hh := (mem_merges.1 h).2.1
        rw [hop] at hh
        cases hh
      have hd : D k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have hh : w = a ∨ w = b := by simpa [hab] using hw'.1
        rcases hh with rfl | rfl
        · simp [hw'.2.2] at ha
        · simp [hw'.2.2] at hb'
      simp [hb, hz, hl, hd]
    · by_cases hl : k ∈ merges n C
      · have hpos := (mem_merges.1 hl).2.2.2
        simp only [hb, hl, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
        split_ifs <;> omega
      · by_cases hz : k ∈ Z
        · simp only [hb, hl, hz, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
          omega
        · have hs : (singletonSupport n C (n + k)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 fun h => hz ((hZ k).2 ⟨hk, h⟩)
          have hop : (gateAt C k).op = GateOp.or :=
            (gate_op hm hr.1).resolve_left fun h => hs.ne_empty (hclean k hr h)
          obtain ⟨u, hu⟩ := hs
          obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
          have hpos := Finset.card_pos.2 ⟨w, mem_positiveInputs.2 ⟨hw, u, huw⟩⟩
          simp only [hb, hl, hz, ite_false, Nat.mul_zero, Nat.add_zero]
          omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hT h, h⟩⟩
  have hB : births n C ⊆ R := fun _ h => (hR _).2 (mem_births.1 h).1
  have hL : merges n C ⊆ R := fun _ h => (hR _).2 (mem_merges.1 h).1
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    count _ hB, count _ hL, Finset.sum_add_distrib,
    count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  have hRc : R.card ≤ C.size := by
    change R.card ≤ C.gates.length
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega

noncomputable def mergePool {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n))
    (c : Fin n) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => k ∈ merges n C ∧
    ∀ v ∈ singletonSupport n C (n + k), G.Adj c v

lemma mem_mergePool {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    {m k : ℕ} : k ∈ mergePool C G c m ↔ k < m ∧ k ∈ merges n C ∧
      ∀ v ∈ singletonSupport n C (n + k), G.Adj c v := by
  classical
  simp [mergePool]

-- Expand the largest root with wide singleton support into its positive inputs.
-- A two-input expansion can add one root and is charged to that OR gate.
lemma leaf_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n ∨ reachable n C (w - n))
    (hadj : ∀ w ∈ roots, ∀ v ∈ singletonSupport n C w, G.Adj c v)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (mergePool C G c m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (singletonSupport n C w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      simp [hs] at hb
    calc
      _ ≤ ∑ w ∈ roots, (singletonSupport n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [mergePool]
  | succ m ih =>
    have hpool : mergePool C G c m ⊆ mergePool C G c (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_mergePool.1 hk
      exact mem_mergePool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hr : reachable n C m := by
        rcases hvalid _ hmem with h | h
        · omega
        · simpa using h
      have hor : (gateAt C m).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
        simp [hclean m hr h] at hlarge
      let P := positiveInputs n C m
      let T := roots.erase (n + m) ∪ P
      have hback : ∀ w ∈ P, w < n + m :=
        fun w hw => rb m hr.1 w (mem_positiveInputs.1 hw).1
      have hup : ∀ w ∈ P, singletonSupport n C w ⊆ singletonSupport n C (n + m) := by
        intro w hw u hu
        exact (support_or rb hr.1 hor u).2 ⟨w, (mem_positiveInputs.1 hw).1, hu⟩
      have hTvalid : ∀ w ∈ T, w < n ∨ reachable n C (w - n) := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hvalid _ (Finset.mem_of_mem_erase hw)
        · by_cases hn : w < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child rb hr (by
              rw [show n + (w - n) = w by omega]
              exact (mem_positiveInputs.1 hw).1))
      have hTadj : ∀ w ∈ T, ∀ v ∈ singletonSupport n C w, G.Adj c v := by
        intro w hw v hv
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hadj _ (Finset.mem_of_mem_erase hw) v hv
        · exact hadj _ hmem v (hup _ hw hv)
      have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hcard
        rcases Finset.mem_union.1 hw with hw | hw
        · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
          have hne := (Finset.mem_erase.1 hw).1
          omega
        · exact hback w hw
      have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
        intro u hu
        obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
        by_cases he : w = n + m
        · subst w
          obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).1 huw
          exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
            (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
        · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
      have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTadj hTbound)
      have hTcard := Finset.card_union_le (roots.erase (n + m)) P
      have herase := Finset.card_erase_add_one hmem
      have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hr.1)
      by_cases hp : 1 < P.card
      · have hnew : m ∈ mergePool C G c (m + 1) := mem_mergePool.2
          ⟨by omega, mem_merges.2 ⟨hr, hor, hlarge, hp⟩, hadj _ hmem⟩
        have hn : m ∉ mergePool C G c m := fun h => (Nat.lt_irrefl m) (mem_mergePool.1 h).1
        have hsubpool : insert m (mergePool C G c m) ⊆ mergePool C G c (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
      · have hinc := Finset.card_le_card hpool
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hadj hnew
      have hinc := Finset.card_le_card hpool
      omega

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩

lemma crossing {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    {k a b : ℕ} (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and)
    (hab : (gateAt C k).inputs = [a,b]) :
    ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v := by
  intro u hu v hv
  apply hsafe k hk hop u v
  rw [gateVal_eq_val]
  apply (val_and (by simp) hk.1 hop).2
  intro w hw
  refine ⟨rb k hk.1 w hw, ?_⟩
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inl) _ (mem_support.1 hu)
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inr) _ (mem_support.1 hv)

lemma birth_route {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (u v : Fin n) :
    ∀ w, (w < n ∨ reachable n C (w - n)) → val C (List.ofFn (pairInput u v)) w = true →
      (∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) ∨
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hi : w < n
    · let t : Fin n := ⟨w, hi⟩
      change val C (List.ofFn (pairInput u v)) t.val = true at ht
      change _ ∨ u ∈ singletonSupport n C t.val ∨ v ∈ singletonSupport n C t.val
      rw [val_ofFn] at ht
      rw [support_input]
      have he : t = u ∨ t = v := of_decide_eq_true ht
      exact Or.inr (he.imp (fun h => Finset.mem_singleton.2 h.symm) (fun h => Finset.mem_singleton.2 h.symm))
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : reachable n C k := by simpa using hw.resolve_left hi
      have sub (a) (ha : a ∈ (gateAt C k).inputs)
          (ht' : val C (List.ofFn (pairInput u v)) a = true) := by
        apply ih a (rb k hk.1 a ha) _ ht'
        by_cases hn : a < n
        · exact Or.inl hn
        · exact Or.inr (reachable_child rb hk (by rwa [show n + (a - n) = a by omega]))
      rcases gate_op hm hk.1 with hop | hop
      · by_cases hborn : ∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
            u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a
        · exact Or.inl hborn
        · have hone : ∀ a ∈ (gateAt C k).inputs,
              u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a :=
            fun a ha => (sub a ha ((val_and (by simp) hk.1 hop).1 ht a ha).2).resolve_left hborn
          have hno (t : Fin n) : ¬ ∀ a ∈ (gateAt C k).inputs, t ∈ singletonSupport n C a := by
            intro h
            have hh := (val_and (by simp) hk.1 hop).2 (fun a ha => ⟨rb k hk.1 a ha,
              mem_support.1 (h a ha)⟩ : ∀ a ∈ (gateAt C k).inputs,
                a < n + k ∧ val C (List.ofFn (pairInput t t)) a = true)
            have hs := mem_support.2 hh
            simp [hclean k hk hop] at hs
          have hlen := (hm _ (gateAt_mem hk.1)).2
          generalize he : (gateAt C k).inputs = l at hlen
          cases l with
          | nil =>
            have hz := hempty k hk hop
            rw [gateVal_eq_val, (show val C (List.ofFn (fun _ : Fin n => false)) (n + k) = true from
              (val_and (by simp) hk.1 hop).2 (by simp [he]))] at hz
            cases hz
          | cons a as =>
            cases as with
            | nil =>
              rcases hone a (by simp [he]) with ha | ha
              · exact (hno u (by simpa [he] using ha)).elim
              · exact (hno v (by simpa [he] using ha)).elim
            | cons b bs =>
              have hb0 : bs = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
              subst bs
              have nonemp (a) (ha : a ∈ (gateAt C k).inputs) :
                  (singletonSupport n C a).Nonempty := by
                rcases hone a ha with hu | hv
                · exact ⟨u, hu⟩
                · exact ⟨v, hv⟩
              exact Or.inl ⟨k, mem_births.2 ⟨hk, hop, a, b, he,
                nonemp a (by simp [he]), nonemp b (by simp [he])⟩, hone⟩
      · obtain ⟨a, ha, _, ht'⟩ := (val_or (by simp) hk.1 hop).1 ht
        rcases sub a ha ht' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((support_or rb hk.1 hop u).2 ⟨a, ha, h⟩))
        · exact Or.inr (Or.inr ((support_or rb hk.1 hop v).2 ⟨a, ha, h⟩))

lemma birth_star {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    {k : ℕ} (hk : k ∈ births n C) :
    ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
  obtain ⟨hr, hop, a, b, hab, ha, hb⟩ := mem_births.1 hk
  have hex := crossing hm rb hsafe hr hop hab
  have hsmall : (singletonSupport n C a).card ≤ 1 ∨ (singletonSupport n C b).card ≤ 1 := by
    by_contra! h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h.2
    exact hcommon u v x y huv hxy (hex u hu x hx) (hex u hu y hy) (hex v hv x hx) (hex v hv y hy)
  have star (s w : ℕ) (hs : (singletonSupport n C s).Nonempty)
      (hcard : (singletonSupport n C s).card ≤ 1)
      (hsin : s ∈ (gateAt C k).inputs) (hwin : w ∈ (gateAt C k).inputs)
      (hcross : ∀ u ∈ singletonSupport n C s, ∀ v ∈ singletonSupport n C w, G.Adj u v) :
      ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
        (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
        ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
          u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
          (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
    obtain ⟨c, hc⟩ := hs
    have heq : ∀ t ∈ singletonSupport n C s, t = c :=
      fun t ht => Finset.card_le_one.1 hcard t ht c hc
    refine ⟨c, w, hwin, hcross c hc, ?_⟩
    intro u v h
    rcases h s hsin with hu | hv
    · left
      refine ⟨heq u hu, (h w hwin).resolve_left fun hw => ?_⟩
      exact G.irrefl (hcross u hu u hw)
    · right
      refine ⟨heq v hv, (h w hwin).resolve_right fun hw => ?_⟩
      exact G.irrefl (hcross v hv v hw)
  rcases hsmall with h | h
  · exact star a b ha h (by simp [hab]) (by simp [hab]) hex
  · exact star b a hb h (by simp [hab]) (by simp [hab]) (fun u hu v hv => (hex v hv u hu).symm)

def edgeKey {n : ℕ} (c v : Fin n) : Fin n × Fin n := (min c v, max c v)

lemma edgeKey_comm {n : ℕ} (c v : Fin n) : edgeKey c v = edgeKey v c := by
  simp only [edgeKey, min_comm c v, max_comm c v]

lemma graph_budget {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n)) (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (hout : singletonSupport n C C.output = ∅)
    (hpair : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card ≤ C.size + 1 := by
  classical
  have hclean (k) (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and) :
      singletonSupport n C (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    exact G.irrefl (hsafe k hk hop u u (mem_support.1 hu))
  let B := births n C
  let star (k : ℕ) (hk : k ∈ B) := birth_star hm rb hsafe hcommon hk
  let c (k : ℕ) := if hk : k ∈ B then (star k hk).choose else seed
  let w (k : ℕ) := if hk : k ∈ B then (star k hk).choose_spec.choose else 0
  have choose_spec (k) (hk : k ∈ B) :
    w k ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C (w k), G.Adj (c k) v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨ (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    simpa only [c, w, dite_eq_left hk] using (star k hk).choose_spec.choose_spec
  have cover (u v) (huv : G.Adj u v) :
      ∃ k ∈ B, (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
        (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    have hv := hpair u v huv
    rw [eval_eq_val] at hv
    have hl : C.output < n + C.gates.length := by
      by_contra! hh
      rw [val_ge (by simp : (List.ofFn (pairInput u v)).length = n) hh] at hv
      cases hv
    have hn : n ≤ C.output := by
      by_contra! hh
      have he := support_input (C := C) (⟨C.output, hh⟩ : Fin n)
      rw [hout] at he
      exact (Finset.singleton_nonempty _).ne_empty he.symm
    have hr : reachable n C (C.output - n) := ⟨by omega, Or.inl (by omega)⟩
    rcases birth_route hm rb hclean hempty u v C.output (Or.inr hr) hv with h | h
    · obtain ⟨k, hk, ha⟩ := h
      exact ⟨k, hk, (choose_spec k hk).2.2 u v ha⟩
    · simp [hout] at h
  let T := B.image c
  let fiber (u : Fin n) := B.filter fun k => c k = u
  let roots (u : Fin n) := (fiber u).image w
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
  have hcov : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    obtain ⟨k, hk, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := cover u v huv
    · exact Or.inl (Finset.mem_image_of_mem c hk)
    · exact Or.inr (Finset.mem_image_of_mem c hk)
  have hEsub : E ⊆ T.biUnion (fun t => (leaves t).image (edgeKey t)) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨huv, huv'⟩ := hE _ hp
    obtain ⟨k, hk, h⟩ := cover u v huv
    have hroot : w k ∈ roots (c k) := Finset.mem_image_of_mem w (Finset.mem_filter.2 ⟨hk, rfl⟩)
    refine Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, ?_⟩
    have hkey : edgeKey u v = (u, v) := by simp [edgeKey, min_eq_left huv', max_eq_right huv']
    rcases h with ⟨he, h⟩ | ⟨he, h⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
      intro a ha
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      by_cases hn : w k < n
      · exact Or.inl hn
      · apply Or.inr
        exact reachable_child rb (mem_births.1 hk).1 (by
          rw [show n + (w k - n) = w k by omega]
          exact (choose_spec k hk).1)) (by
      intro a ha v hv
      obtain ⟨k, hk, rfl, rfl⟩ := hr a ha
      exact (choose_spec k hk).2.1 v hv) (by
      intro a ha _
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      have hk' := (mem_births.1 hk).1.1
      have := rb k hk' (w k) (choose_spec k hk).1
      omega)
    exact h.trans (Nat.add_le_add_right Finset.card_image_le _)
  have hdisjFib : (T : Set (Fin n)).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    exact hab ((Finset.mem_filter.1 hka).2.symm.trans (Finset.mem_filter.1 hkb).2)
  have hsumB : (∑ t ∈ T, (fiber t).card) = B.card := by
    rw [← Finset.card_biUnion hdisjFib]
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨_, _, hf⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hf).1
    · intro hk
      exact Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

private lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]

private lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp

private lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]

private lemma inputs_eq_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hmem : gateAt C j ∈ C.gates := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ hmem
  unfold opnd
  rcases h : (gateAt C j).inputs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

private lemma opnd_mem_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [inputs_eq_pair hAO hj]
  fin_cases b <;> simp

private lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem_inputs hAO hj b)

private lemma mem_insertNew {A : List (List ℕ)} {u v : List ℕ} :
    v ∈ insertNew A u ↔ v ∈ A ∨ v = u := by
  unfold insertNew
  split_ifs with h
  · constructor
    · intro hv; exact Or.inl hv
    · rintro (hv | rfl)
      · exact hv
      · exact h
  · simp

private lemma mem_foldl_insertNew {l acc : List (List ℕ)} {v : List ℕ} :
    v ∈ l.foldl insertNew acc ↔ v ∈ acc ∨ v ∈ l := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih, mem_insertNew]
    tauto

private lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} :
    v ∈ andStep k A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd k u w := by
  unfold andStep
  rw [mem_foldl_insertNew]
  simp only [List.not_mem_nil, false_or, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩
  · rintro ⟨u, hu, w, hw, rfl⟩
    exact ⟨u, hu, w, hw, rfl⟩

private lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  unfold readVectors
  rw [foldl_append_length, List.length_map, List.length_range]

private lemma readVectors_getD_ge (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : n + C.gates.length ≤ w) :
    (readVectors C n S k).getD w [] = [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [readVectors_length]; exact hw

private lemma readVectors_getD_lt (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    {w : ℕ} (hw : w < n) :
    (readVectors C n S k).getD w [] = leafVectors S k w := by
  unfold readVectors
  have hlt : w < ((List.range n).map (leafVectors S k)).length := by
    rw [List.length_map, List.length_range]; exact hw
  rw [foldl_append_getD_lt _ C.gates ((List.range n).map (leafVectors S k)) [] w hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  simp

private lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]

private lemma mem_readVectors_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      v ∈ (readVectors C n S k).getD (opnd C j 0) [] ∨
      v ∈ (readVectors C n S k).getD (opnd C j 1) [] := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_foldl_insertNew, mem_foldl_insertNew]
  simp

private lemma mem_readVectors_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) (v : List ℕ) :
    v ∈ (readVectors C n S k).getD (n + j) [] ↔
      ∃ u0 ∈ (readVectors C n S k).getD (opnd C j 0) [],
      ∃ u1 ∈ (readVectors C n S k).getD (opnd C j 1) [],
        v = capAdd k (capAdd k (S.map fun _ => 0) u0) u1 := by
  rw [readVectors_getD_gate hAO S k hj, hop, inputs_eq_pair hAO hj]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  rw [mem_andStep]
  constructor
  · rintro ⟨t, ht, u1, hu1, rfl⟩
    rw [mem_andStep] at ht
    rcases ht with ⟨z, hz, u0, hu0, rfl⟩
    rw [List.mem_singleton] at hz
    subst hz
    exact ⟨u0, hu0, u1, hu1, rfl⟩
  · rintro ⟨u0, hu0, u1, hu1, rfl⟩
    refine ⟨capAdd k (S.map fun _ => 0) u0, ?_, u1, hu1, rfl⟩
    rw [mem_andStep]
    exact ⟨S.map fun _ => 0, List.mem_singleton_self _, u0, hu0, rfl⟩

private lemma readVectors_pair_inv {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p q : Fin n} (hpq : p ≠ q) :
    ∀ w : ℕ, ∀ v ∈ (readVectors C n [p.val, q.val] 1).getD w [],
      ∃ a b : ℕ, v = [a, b] ∧ a ≤ 2 ∧ b ≤ 2 ∧ 1 ≤ a + b := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    by_cases hlt : w < n
    · rw [readVectors_getD_lt C n [p.val, q.val] 1 hlt] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        simp only [List.mem_singleton, List.map_cons, List.map_nil] at hv
        rcases hmem with rfl | rfl
        · have hne : q.val ≠ p.val := fun h => hpq (Fin.ext h.symm)
          simp only [ite_true, hne, ite_false] at hv
          exact ⟨1, 0, hv, by omega, by omega, by omega⟩
        · have hne : p.val ≠ q.val := fun h => hpq (Fin.ext h)
          simp only [hne, ite_false, ite_true] at hv
          exact ⟨0, 1, hv, by omega, by omega, by omega⟩
      · simp at hv
    · by_cases hge : n + C.gates.length ≤ w
      · rw [readVectors_getD_ge C n [p.val, q.val] 1 hge] at hv
        simp at hv
      · set j := w - n
        have hw : w = n + j := by omega
        have hj : j < C.gates.length := by omega
        have hmem : gateAt C j ∈ C.gates := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        rw [hw] at hv
        rcases hAO.1 _ hmem with hop | hop
        · rw [mem_readVectors_and hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with ⟨u0, hu0, u1, hu1, rfl⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 0) u0 hu0 with ⟨a0, b0, rfl, ha0, hb0, hs0⟩
          rcases ih _ (hw ▸ opnd_lt hAO hj 1) u1 hu1 with ⟨a1, b1, rfl, ha1, hb1, hs1⟩
          refine ⟨min (min (0 + a0) 2 + a1) 2, min (min (0 + b0) 2 + b1) 2, ?_,
            Nat.min_le_right _ _, Nat.min_le_right _ _, by omega⟩
          simp [capAdd]
        · rw [mem_readVectors_or hAO [p.val, q.val] 1 hj hop] at hv
          rcases hv with h0 | h1
          · exact ih _ (hw ▸ opnd_lt hAO hj 0) v h0
          · exact ih _ (hw ▸ opnd_lt hAO hj 1) v h1

private def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

private lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
    edgeTrue G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

private def dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j

private def badHit {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (p : Fin n × Fin n) : Prop :=
  G.Adj p.1 p.2 ∧ readsAtMost C n [p.1.val, p.2.val] 1 = false ∧
    gateVal n C j (pairInput p.1 p.2) = true

private noncomputable def selectEdge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (fallback : Fin n × Fin n) (j : ℕ) : Fin n × Fin n := by
  classical
  exact if h : ∃ p, badHit G C j p then h.choose else fallback

private lemma select_hit {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {fallback : Fin n × Fin n} {j : ℕ} {p : Fin n × Fin n}
    (h : badHit G C j p) : badHit G C j (selectEdge G C fallback j) := by
  classical
  have hex : ∃ p, badHit G C j p := ⟨p, h⟩
  simpa only [selectEdge, dite_eq_left hex] using hex.choose_spec

private lemma select_adj {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    {fallback : Fin n × Fin n} (hf : G.Adj fallback.1 fallback.2) (j : ℕ) :
    G.Adj (selectEdge G C fallback j).1 (selectEdge G C fallback j).2 := by
  classical
  by_cases h : ∃ p, badHit G C j p
  · exact (select_hit (fallback := fallback) h.choose_spec).1
  · simpa only [selectEdge, dite_eq_right h] using hf

-- Keep each gate index and replace a dirty AND by a test for its selected edge.
private noncomputable def repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) : Circuit := by
  classical
  exact ⟨(List.range C.gates.length).map fun j =>
    if dirty G C j then ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ else gateAt C j,
    C.output⟩

private lemma repair_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) :
    (repair G C pick).gates.length = C.gates.length := by
  simp [repair]

private lemma repair_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (repair G C pick) j =
      @ite Gate (dirty G C j) (Classical.propDecidable _)
        ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ (gateAt C j) := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  rw [gateAt_eq hj']
  simp [repair]

private lemma repair_ao {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n) :
    IsAO2 n (repair G C pick) := by
  classical
  have hgate (j : ℕ) (hj : j < (repair G C pick).gates.length) :
      ((gateAt (repair G C pick) j).op = GateOp.and ∨
        (gateAt (repair G C pick) j).op = GateOp.or) ∧
      (gateAt (repair G C pick) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (repair G C pick) j).inputs, w < n + j := by
    rw [repair_len] at hj
    rw [repair_gate pick hj]
    split_ifs
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := (pick j).1.isLt
        omega
      · have := (pick j).2.isLt
        omega
    · exact ⟨hC.1 _ (gateAt_mem hj), hC.2.2 _ (gateAt_mem hj), hC.2.1 j hj⟩
  refine ⟨?_, fun j hj => (hgate j hj).2.2, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).2.1

private lemma repair_kept {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (h : ¬ dirty G C j) : gateAt (repair G C pick) j = gateAt C j := by
  classical
  rw [repair_gate pick hj, ite_eq_right h]

private lemma repair_replaced_val {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (hd : dirty G C j) (x : Fin n → Bool) :
    val (repair G C pick) (List.ofFn x) (n + j) = true ↔
      x (pick j).1 = true ∧ x (pick j).2 = true := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  have hg := (repair_gate (G := G) pick hj).trans (ite_eq_left hd)
  rw [val_and (by simp) hj' (congrArg Gate.op hg), hg]
  have h₁ : (pick j).1.val < n + j := by have := (pick j).1.isLt; omega
  have h₂ : (pick j).2.val < n + j := by have := (pick j).2.isLt; omega
  simp [h₁, h₂, val_ofFn]

private lemma repair_compare {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    (x : Fin n → Bool) (forward : Bool)
    (hreplaced : ∀ j < C.gates.length, dirty G C j →
      if forward then
        val C (List.ofFn x) (n + j) = true → val (repair G C pick) (List.ofFn x) (n + j) = true
      else
        val (repair G C pick) (List.ofFn x) (n + j) = true → val C (List.ofFn x) (n + j) = true) :
    ∀ w : ℕ, if forward then
      val C (List.ofFn x) w = true → val (repair G C pick) (List.ofFn x) w = true
    else
      val (repair G C pick) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  let D := repair G C pick
  let xs := List.ofFn x
  have hl : D.gates.length = C.gates.length := repair_len G C pick
  have hx : xs.length = n := List.length_ofFn
  have transfer (A B : Circuit) (heq : A.gates.length = C.gates.length)
      (heq' : B.gates.length = C.gates.length)
      (hkeep : ∀ j < C.gates.length, ¬ dirty G C j →
        gateAt A j = gateAt C j ∧ gateAt B j = gateAt C j)
      (hchange : ∀ j < C.gates.length, dirty G C j →
        val A xs (n + j) = true → val B xs (n + j) = true) :
      ∀ w, val A xs w = true → val B xs w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hi : w < n
      · rwa [val_input hx hi, ← val_input (C := A) hx hi]
      by_cases hj : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
        have hj' : j < C.gates.length := by omega
        by_cases hd : dirty G C j
        · exact hchange j hj' hd ht
        obtain ⟨ha, hb⟩ := hkeep j hj' hd
        have hjA : j < A.gates.length := by rwa [heq]
        have hjB : j < B.gates.length := by rwa [heq']
        rcases hC.1 _ (gateAt_mem hj') with op | op
        · rw [val_and hx hjA (by rwa [ha]), ha] at ht
          rw [val_and hx hjB (by rwa [hb]), hb]
          exact fun i hi => ⟨(ht i hi).1, ih i (ht i hi).1 (ht i hi).2⟩
        · rw [val_or hx hjA (by rwa [ha]), ha] at ht
          rw [val_or hx hjB (by rwa [hb]), hb]
          obtain ⟨i, hi, hlt, hv⟩ := ht
          exact ⟨i, hi, hlt, ih i hlt hv⟩
      · rw [val_ge hx (by omega)] at ht
        cases ht
  cases forward
  · exact transfer D C hl rfl (fun j hj hn => ⟨repair_kept pick hj hn, rfl⟩) hreplaced
  · exact transfer C D rfl hl (fun j hj hn => ⟨rfl, repair_kept pick hj hn⟩) hreplaced

-- With at most two leaves, an AND can occur only at a wire below the graph function.
-- At that AND, each operand has a one-leaf witness.
private lemma repair_read_vector {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    {u v : Fin n} (hne : u ≠ v) :
    ∀ w a b : ℕ, a ≤ 1 → b ≤ 1 →
      [a, b] ∈ (readVectors C n [u.val, v.val] 1).getD w [] →
      (a + b ≤ 1 ∨ ∀ x : Fin n → Bool, val C (List.ofFn x) w = true → graphFun G ∅ x = true) →
      val (repair G C pick) (List.ofFn (pairInput u v)) w = true := by
  let D := repair G C pick
  let xs := List.ofFn (pairInput u v)
  have hx : xs.length = n := List.length_ofFn
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro a b ha hb hv hsafe
    by_cases hi : w < n
    · rw [readVectors_getD_lt C n _ 1 hi] at hv
      unfold leafVectors at hv
      split_ifs at hv with he
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp [val_ofFn, pairInput]
      · simp at hv
    by_cases hj : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      have hj' : j < C.gates.length := by omega
      have hjD : j < D.gates.length := by rwa [repair_len]
      rcases hC.1 _ (gateAt_mem hj') with hop | hop
      · rw [mem_readVectors_and hC _ _ hj' hop] at hv
        obtain ⟨x, hxv, y, hyv, hsum⟩ := hv
        have h0 := opnd_lt hC hj' 0
        have h1 := opnd_lt hC hj' 1
        obtain ⟨a₀, b₀, rfl, ha₀, hb₀, hn₀⟩ := readVectors_pair_inv hC hne _ _ hxv
        obtain ⟨a₁, b₁, rfl, ha₁, hb₁, hn₁⟩ := readVectors_pair_inv hC hne _ _ hyv
        simp only [capAdd, List.map_cons, List.map_nil, List.zipWith_cons_cons,
          List.zipWith_nil_right, List.cons.injEq, and_true] at hsum
        have htotal : a = a₀ + a₁ ∧ b = b₀ + b₁ := by omega
        have hbelow : BelowF G C j := by
          intro z hz
          exact (hsafe.resolve_left (by omega)) z hz
        have hg : gateAt D j = gateAt C j :=
          repair_kept pick hj' (fun hd => hd.2 hbelow)
        change val D xs (n + j) = true
        rw [val_and hx hjD (by rwa [hg]), hg, inputs_eq_pair hC hj']
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact ⟨h0, ih _ h0 a₀ b₀ (by omega) (by omega) hxv (Or.inl (by omega))⟩
        · exact ⟨h1, ih _ h1 a₁ b₁ (by omega) (by omega) hyv (Or.inl (by omega))⟩
      · rw [mem_readVectors_or hC _ _ hj' hop] at hv
        have hg : gateAt D j = gateAt C j :=
          repair_kept pick hj' (fun hd => by cases hop.symm.trans hd.1)
        change val D xs (n + j) = true
        rw [val_or hx hjD (by rwa [hg]), hg]
        have step (k : Fin 2) (hk : [a, b] ∈
            (readVectors C n [u.val, v.val] 1).getD (opnd C j k) []) :
            ∃ i ∈ (gateAt C j).inputs, i < n + j ∧ val D xs i = true := by
          have hm := opnd_mem_inputs hC hj' k
          have lt := opnd_lt hC hj' k
          refine ⟨_, hm, lt, ih _ lt a b ha hb hk (hsafe.imp_right ?_)⟩
          intro h x hval
          exact h x ((val_or (by simp) hj' hop).2 ⟨_, hm, lt, hval⟩)
        exact hv.elim (step 0) (step 1)
    · rw [readVectors_getD_ge C n _ 1 (by omega)] at hv
      simp at hv

private lemma repair_read_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    (hc : circuitFun n C = graphFun G ∅) {u v : Fin n} (hne : u ≠ v)
    (hread : readsAtMost C n [u.val, v.val] 1 = true) :
    circuitFun n (repair G C pick) (pairInput u v) = true := by
  obtain ⟨l, hl, hle⟩ := List.any_eq_true.1 hread
  obtain ⟨a, b, rfl, _, _, _⟩ := readVectors_pair_inv hC hne _ _ hl
  have hbound : a ≤ 1 ∧ b ≤ 1 := by simpa using hle
  exact repair_read_vector hC pick hne _ _ _ hbound.1 hbound.2 hl (Or.inr (by
    intro x hx
    rw [← hc]
    exact hx))

-- On a graph-false input every replaced gate is false. On a bad edge, uniqueness
-- preserves each dirty gate that was true. The read-vector argument handles the other edges.
private lemma repaired_graph {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (fallback : Fin n × Fin n) (hf : G.Adj fallback.1 fallback.2)
    (hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2)) :
    let pick := selectEdge G C fallback
    let D := repair G C pick
    (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
    (∀ u v, G.Adj u v → circuitFun n D (pairInput u v) = true) ∧
    (∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true) := by
  intro pick D
  have hp : ∀ j, G.Adj (pick j).1 (pick j).2 := select_adj hf
  have hreflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val D (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hval
      have hpv := (repair_replaced_val pick hj hd x).1 hval
      exact (hn (graph_true.2 ⟨_, _, hp j, hpv.1, hpv.2⟩)).elim) w
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have h := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨_, _, hp j, h.1, h.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by
        rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (hreflect x hn (n + j) hv))
  · intro u v huv
    cases hread : readsAtMost C n [u.val, v.val] 1
    · have htrue : circuitFun n C (pairInput u v) = true := by
        rw [hc]
        exact graph_true.2 (edge_true_pair.2 huv)
      exact repair_compare hC pick (pairInput u v) true (by
        intro j hj hd hv
        have hhit : badHit G C j (u, v) := ⟨huv, hread, hv⟩
        have hs : s((pick j).1, (pick j).2) = s(u, v) :=
          hu j hj hd _ _ (select_hit (fallback := fallback) hhit) hhit
        apply (repair_replaced_val pick hj hd _).2
        rcases Sym2.eq_iff.1 hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
      ) C.output htrue
    · exact repair_read_one hC pick hc (G.ne_of_adj huv) hread
  · intro x hx
    by_contra hn
    have h := hreflect x hn C.output hx
    change circuitFun n C x = true at h
    rw [hc] at h
    exact hn h

private lemma sorted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ E : Finset (Fin n × Fin n), E.card = G.edgeFinset.card ∧
      ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2 := by
  let E := Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 ≤ p.2
  refine ⟨E, ?_, fun p hp => (Finset.mem_filter.1 hp).2⟩
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · exact fun p hp => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 hp).2.1
  · intro a ha b hb hab
    rcases Sym2.eq_iff.1 hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · have hle₁ := (Finset.mem_filter.1 ha).2.2
      have hle₂ := (Finset.mem_filter.1 hb).2.2
      have he : b.1 = b.2 := le_antisymm hle₂ (by rwa [h₁, h₂] at hle₁)
      exact Prod.ext (h₁.trans he.symm) (h₂.trans he)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h := SimpleGraph.mem_edgeFinset.1 he
      rcases le_total u v with huv | hvu
      · exact ⟨(u, v), Finset.mem_filter.2 ⟨Finset.mem_univ _, h, huv⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.2 ⟨Finset.mem_univ _, h.symm, hvu⟩, Sym2.eq_swap⟩

private lemma main_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (hu : ∀ j < C.gates.length, dirty G C j →
      ∀ p q, badHit G C j p → badHit G C j q → s(p.1, p.2) = s(q.1, q.2)) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ u v =>
    have hadj := SimpleGraph.mem_edgeFinset.1 he
    let pick := selectEdge G C (u, v)
    let D := repair G C pick
    have hD : IsAO2 n D := repair_ao hC pick
    obtain ⟨hclean, hpair, hfun⟩ := repaired_graph hC hc (u, v) hadj hu
    have hm : Monotone2 D := by
      intro g hg
      exact ⟨by simpa using hD.1 g hg, (hD.2.2 g hg).le⟩
    obtain ⟨E, hcard, hE⟩ := sorted_edges G
    obtain ⟨T, hcover, hT, hbound⟩ := graph_budget (C := D) G u hm hD.2.1
      (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
      (by
        intro j hj hop
        cases h : gateVal n D j (fun _ => false)
        · rfl
        · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
          cases ha)
      (fun _ _ _ _ => no_four_cycle hfour)
      (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hh : circuitFun n D (pairInput a a) = true := mem_support.1 ha
        exact G.irrefl (edge_true_pair.1 (graph_true.1 (hfun _ hh))))
      hpair E hE
    refine ⟨T, ?_, ?_⟩
    · exact hcover
    · have hlen : D.size = C.size := repair_len G C pick
      omega

end PEqualNP.Outside.L_meta_8933

theorem PEqualNP.Outside.L_meta_8933 :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → (¬∃ x9 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x9 ∧ ∃ (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1), x2.Adj x10 x11 ∧ x2.Adj x12 x13 ∧ s(x10, x11) ≠ s(x12, x13) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x10, ↑x11] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x12, ↑x13] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x9 (PEqualNP.EdgeOwnership.pairInput x10 x11) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x9 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → ∃ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 ∧ x2.edgeFinset.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n G _ C hfour hne hC hc hbad
  apply PEqualNP.Outside.L_meta_8933.main_bound G C hfour hne hC hc
  intro j hj hd p q hp hq
  by_contra h
  exact hbad ⟨j, hj, hd.1, hd.2, p.1, p.2, q.1, q.2,
    hp.1, hq.1, h, hp.2.1, hq.2.1, hp.2.2, hq.2.2⟩
namespace PEqualNP.Outside.PlaneRead17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
set_option maxRecDepth 32768
set_option maxHeartbeats 0
abbrev V := Fin 26
def edges : List (Nat × Nat) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
def rel (a b : V) := (a.val,b.val) ∈ edges ∨ (b.val,a.val) ∈ edges
instance (a b : V) : Decidable (rel a b) := by unfold rel; infer_instance
def G : SimpleGraph V where
  Adj := rel
  symm := ⟨fun a b h => Or.symm h⟩
  loopless := by
    have h : ∀ a : V, ¬rel a a := by decide +kernel
    exact ⟨h⟩
instance : DecidableRel G.Adj := fun a b => inferInstanceAs (Decidable (rel a b))
theorem c4 : NoFourCycle G := by decide +kernel
theorem edgeCount : G.edgeFinset.card = 52 := by decide +kernel
def leftPoint (i : Fin 13) : V :=
  ([0, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] : List V).getD i.val 0

def rightLine (i : Fin 13) : V := ⟨13+i.val,by omega⟩

private theorem matched : ∀ i : Fin 13, G.Adj (leftPoint i) (rightLine i) := by decide +kernel

private theorem apart : ∀ i j : Fin 13, i ≠ j →
    leftPoint i ≠ leftPoint j ∧ leftPoint i ≠ rightLine j ∧
    rightLine i ≠ leftPoint j ∧ rightLine i ≠ rightLine j := by decide +kernel

theorem coverCount (S : Finset V) (covers : ∀ a b : V, G.Adj a b → a ∈ S ∨ b ∈ S) :
    13 ≤ S.card := by
  let pick (i : Fin 13) : V := if leftPoint i ∈ S then leftPoint i else rightLine i
  have chosen (i : Fin 13) : pick i ∈ S := by
    by_cases h : leftPoint i ∈ S
    · simpa [pick,h] using h
    · simpa [pick,h] using (covers _ _ (matched i)).resolve_left h
  have injective : Function.Injective pick := by
    intro i j eq
    by_contra ne
    obtain ⟨hll,hlr,hrl,hrr⟩ := apart i j ne
    by_cases hi : leftPoint i ∈ S <;> by_cases hj : leftPoint j ∈ S <;>
      simp only [pick,hi,hj,ite_true,ite_false] at eq
    · exact hll eq
    · exact hlr eq
    · exact hrl eq
    · exact hrr eq
  let f (i : Fin 13) : {v // v ∈ S} := ⟨pick i,chosen i⟩
  have bound := Fintype.card_le_of_injective f (fun i j eq =>
    injective (congrArg Subtype.val eq))
  simpa using bound

theorem lower (C : Circuit) (ao : IsAO2 26 C) (r : IsReadK 26 C 1)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) : 64 ≤ C.size := by
  have h (x : V → Bool) : circuitFun 26 C x = decide (∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true) := by
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x)=true ↔ _
    rw [decide_eq_true_eq,ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ab,ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩
  obtain ⟨S,hS,hcost⟩ := PEqualNP.Outside.L_meta_6369 26 G C c4 ao h r
  have hs := coverCount S hS
  rw [edgeCount] at hcost
  omega


theorem listed {p l : Fin 13} (e : Promise17245.Inc p l) :
    ((Fin.castAdd 13 p).val,(Fin.natAdd 13 l).val)∈edges := by
  exact (by decide +kernel : ∀p l:Fin 13,Promise17245.Inc p l → ((Fin.castAdd 13 p).val,(Fin.natAdd 13 l).val)∈edges) p l e
theorem unlisted : ∀a b : V,(a.val,b.val)∈edges → ∃p l:Fin 13,
    a=Fin.castAdd 13 p ∧ b=Fin.natAdd 13 l ∧ Promise17245.Inc p l := by decide +kernel
open Promise17245
theorem agrees {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o) (x : V → Bool) :
    (finish C o).eval (List.ofFn x) = true ↔ ∃a b:V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true := by
  rw [finish_eval,exact_eval hm ht]
  constructor
  · rintro ⟨p,l,e,hp,hl⟩
    exact ⟨_,_,listed e,hp,hl⟩
  · rintro ⟨a,b,e,ha,hb⟩
    obtain ⟨p,l,rfl,rfl,hpl⟩ := unlisted a b e
    exact ⟨p,l,hpl,ha,hb⟩
theorem readOne {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o)
    (ao : IsAO2 26 (finish C o)) (r : IsReadK 26 (finish C o) 1) : 63≤C.size := by
  have h := lower (finish C o) ao r (agrees hm ht)
  rw [finish_size] at h
  omega
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def repeatedPair (C : Circuit) : Prop :=
  ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j ∧
    ∃ a b c d : V, G.Adj a b ∧ G.Adj c d ∧ s(a,b) ≠ s(c,d) ∧
      readsAtMost C 26 [a.val,b.val] 1 = false ∧
      readsAtMost C 26 [c.val,d.val] 1 = false ∧
      gateVal 26 C j (pairInput a b) = true ∧ gateVal 26 C j (pairInput c d) = true

theorem normalizeCounterexample (C : Circuit) (m : Monotone2 C) (small : C.size ≤ 63)
    (ok : ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔
      ∃ a b : V,(a.val,b.val)∈edges ∧ x a=true ∧ x b=true) :
    ∃ T : Circuit, IsLeastAO G T ∧ TopForm G T ∧ T.size ≤ 63 ∧
      repeatedPair T := by
  have computed (x : V → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ a b : V, G.Adj a b ∧ x a=true ∧ x b=true := by
    rw [ok]
    constructor
    · rintro ⟨a,b,ab,ha,hb⟩
      exact ⟨a,b,Or.inl ab,ha,hb⟩
    · rintro ⟨a,b,ab,ha,hb⟩
      rcases ab with ab | ba
      · exact ⟨a,b,ab,ha,hb⟩
      · exact ⟨b,a,ba,hb,ha⟩
  have nonempty : G.edgeFinset.Nonempty := Finset.card_pos.mp (by rw [edgeCount]; decide)
  obtain ⟨D,ao,agree,sz⟩ := PEqualNP.Outside.L_meta_1527 26 G inferInstance C m computed
  obtain ⟨T,least,top,szT⟩ := PEqualNP.Outside.L_meta_8567 26 G D nonempty ao agree
  have sz' : T.size ≤ 63 := by omega
  have pair : repeatedPair T := by
    by_contra none
    obtain ⟨S,covers,hcost⟩ := PEqualNP.Outside.L_meta_8933 26 G T c4 nonempty
      least.1 least.2.1 none
    have atLeast := coverCount S covers
    rw [edgeCount] at hcost
    omega

  exact ⟨T,least,top,sz',pair⟩

theorem repeatedIfSmall {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o)
    (out : o.length≤2) (small : C.size≤62) :
    ∃T : Circuit, IsLeastAO G T ∧ TopForm G T ∧ T.size ≤ 63 ∧ repeatedPair T := by
  apply normalizeCounterexample (finish C o) (finish_mono hm out) _ (agrees hm ht)
  rw [finish_size]
  omega
end PEqualNP.Outside.PlaneRead17245

namespace PEqualNP.Outside.PlaneRead17245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open Promise17245
set_option maxHeartbeats 0
set_option maxRecDepth 32768
abbrev F := Fin 52
abbrev A := Fin 95
def rowBits : Array Nat := #[0x416000,0x220a000,0x3104000,0x1882000,0x2c40000,0x1620000,0xb10000,0x588000,0x2c4000,0x162000,0x20b0000,0x1058000,0x82c000,0x20b,0x1105,0x1882,0xc41,0x1620,0xb10,0x588,0x2c4,0x162,0xb1,0x1058,0x82c,0x416]
def words : Array Nat := #[0x338bdab49ca307b9ac5a928398a418820,0x33595b0f9de30a35c9329833aca440440,0x3378c2927ceadc59c5185075a4ca61040,0x3377b7128d670a59c7329054ac6161040,0x1d89d6d4bca2f865aa5b12431ca818801,0x2d77d2128ceb86e5c11950a4acc761002,0x2d78e1b27d674865ca31d015a46561002,0x1b59e2cf95e34865ca3258459ca340402,0x1d695710bce2fa37293b14332ca820041,0x2d09d2ed8beb893b285942c48cc750082,0x2cdae2f07c67493b2849d4c5986508082,0x1b6be2b094e347bb2c3a548598a320022,0x30eb56748464fbe5a462d2a31d0500861,0x256862b76be349e5ca3a581198ab01102,0x2566d277845f8ae5c12ad8a30ce901102,0x2adb626f846f4965c44998a59c6500502,0x2d183af59b5f49632b49c234198051482,0x1d3837128daefa57263b0854ac6052041,0x2d56ba517c274be32331d4b6250009482,0x1b383ab78da547e32b3a4856190050c22,0x2f08bad59bdb89532958c274140c51882,0x2b6939b1bce147e32b399436240821422,0x316bb5d194e0fa57263ad484b00321441,0x2ed7bad3ac6149632b4994541c0c08c82,0x31183dd69caeda572648c883818b51441,0x2f3852cd8d5ee9632b43025480e650c82,0x2b1851b69de4e7e32b620833812651422,0x2f56e2d07ce2e9532943147580a309882,0x2b19b9f684af46e3234988b01d8851422,0x2f57ba506c678b532728d4902d0c09882,0x2f38ba4d83eb4b63253982b0250c50c82,0x3119b69685e4f7572862c8601d2351441,0x3138d5d785a4fa37293ac803310550c41,0x2538d2d5835f8bbb2c1ac20314e952082,0x2557e2d36c234bbb2c3254019cab0a082,0x2b38e1b285af47bb2c398805a46552022,0x3148d6ee95a0f9e5aa3ac04430c548861,0x2577e2768c1b4ae5c13240a29c6b61102,0x2578d2b67b6189e5ca1ac01394c961102,0x2afbd26d8c2d8965c45940a48ce660502,0x1d38be9285ecdc5725180865a4ec52041,0x2d19d25583daebe3236002b3212751482,0x2d57d2f16ce0e9632b401434b0c709482,0x1b7952b3b460e7e32b601453a0c920c22,0x2b6bd1f19426e6e3230214b4b0e621422,0x31693e91bc26d7572800d46624eb21441,0x2f09e2558b5eeb5327030292a16351882,0x2edad2537c22eb63250314b3a12608c82,0x317b56939460f7372062d4941cc520c41,0x2b3851f28ded86bb201948c4ace652022,0x253862f58bdb4b3b203a42c2986b52082,0x2556d2f37c618b3b202ad4c38cc90a082,0x3379c2b2c468e7d9a7609255a0ca19020,0x332a3ab78e2707d9a75a8656190249020,0x18b525073148310419c5ed5a4e5183dcd,0x334959f88de70ab9a83286c2ace448820,0x1f48bb3395f10ad9a532c644284c49c20,0x3348c2b894ef67b9ac39068594ca48820,0x47205862a963424129e211addf9b51cd,0x16c42547110a330415be2d9a4e3273e0d,0x319adaf47c6509b9a852d2c3988508860,0x3197c274aca36bb9ac2152831d4b08860,0x26fcc314ac64ebd9a4621253096a09c60,0x337c39f29d230ad9a53292742d8219020,0x1853850a22cc312414c5e12cceafb45cd,0x453a58b2194140c13ae61793e34b61cd,0x2b89bb31bca907d9a7599246284819420,0x1872a44b228c3404159de1996291b3dcd,0x10b30584514e312414c4ed1cddf5849cd,0x2b493b378cf167c1ab3946a6104849820,0x10438d8b2a8c112414cd611c3ef3b49cd,0x2b7c5b349c64e7c1ab6212a3888519820,0x18b30c47510a940415946d99d31783dcd,0x2b1a433895e6e7d9a7620645894649420,0x2b1939f8a4ef0cd9a45186712d8849420,0x2b79b9f4c4a36cc1aa2152b11d8819820,0x1042844b3994362411bce147e335b49cd,0x105225863ad4310419c4e0fa5e32b55cd,0x2b3bc332c52367b9ac39522591461a020,0x2b28db33a62f07b9ac598623a8854a020,0x18520c4a3996142412abe149e717b45cd,0x16728d4c2090930415a49d9bc678b3e0d,0x3148da79955f0bb9ac32c28228e548860,0x314942f98beb69b9a83942c510cb48860,0x27493b0f8d730bd9a43282562c4849c60,0x18a30d05590e112414cbed2c5677845cd,0x3328c1f7a4f0ead9a5408673316a49020,0x4b50585310e940c13952d7ac5f9861cd,0x18720d0b2994910419a4615c4a77b3dcd,0x10b50c4431ca1624117d6d4be713849cd,0x2b8bc1f19d24ecd9a4121275316619420,0x2b48d9f79626ecc1aa1206b230e549820,0x1065a445510e36040fbced98e292855cd,0x2b3c59f2bc690cb9a25192c22ce51a020,0x2b2a41f38df16cb9a22146c51d664a020]
def first : Array Nat := #[0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,0x30,0x31,0x32,0x33]
def second : Array Nat := #[0x0,0x0,0x34,0x35,0x36,0x0,0x37,0x38,0x36,0x0,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,0x40,0x35,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x36,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,0x50,0x51,0x52,0x53,0x54,0x55,0x34,0x56,0x57,0x58,0x59,0x5a,0x5b,0x5c,0x55,0x5d,0x5e]
def flagP : Array Nat := #[0x0,0x0,0x0,0x0,0x1,0x1,0x1,0x1,0x2,0x2,0x2,0x2,0x3,0x3,0x3,0x3,0x4,0x4,0x4,0x4,0x5,0x5,0x5,0x5,0x6,0x6,0x6,0x6,0x7,0x7,0x7,0x7,0x8,0x8,0x8,0x8,0x9,0x9,0x9,0x9,0xa,0xa,0xa,0xa,0xb,0xb,0xb,0xb,0xc,0xc,0xc,0xc]
def flagL : Array Nat := #[0xd,0xe,0x10,0x16,0xd,0xf,0x15,0x19,0xe,0x14,0x18,0x19,0xd,0x13,0x17,0x18,0x12,0x16,0x17,0x19,0x11,0x15,0x16,0x18,0x10,0x14,0x15,0x17,0xf,0x13,0x14,0x16,0xe,0x12,0x13,0x15,0xd,0x11,0x12,0x14,0x10,0x11,0x13,0x19,0xf,0x10,0x12,0x18,0xe,0xf,0x11,0x17]

def fast (u v : V) : Bool := ((rowBits[u.val]?).getD 0).testBit v.val
theorem adjFast : ∀u v:V, G.Adj u v ↔ fast u v = true := by decide +kernel
def motion (k : A) (v : V) : V := Fin.ofNat 26 ((((words[k.val]?).getD 0) >>> (5*v.val)) % 32)
def Valid (k : A) := (∀u v:V,motion k u=motion k v → u=v) ∧ ∀u v:V,fast (motion k u) (motion k v)=fast u v
instance (k : A) : Decidable (Valid k) := by unfold Valid; infer_instance
theorem ok0 : Valid 0 := by decide +kernel
theorem ok1 : Valid 1 := by decide +kernel
theorem ok2 : Valid 2 := by decide +kernel
theorem ok3 : Valid 3 := by decide +kernel
theorem ok4 : Valid 4 := by decide +kernel
theorem ok5 : Valid 5 := by decide +kernel
theorem ok6 : Valid 6 := by decide +kernel
theorem ok7 : Valid 7 := by decide +kernel
theorem ok8 : Valid 8 := by decide +kernel
theorem ok9 : Valid 9 := by decide +kernel
theorem ok10 : Valid 10 := by decide +kernel
theorem ok11 : Valid 11 := by decide +kernel
theorem ok12 : Valid 12 := by decide +kernel
theorem ok13 : Valid 13 := by decide +kernel
theorem ok14 : Valid 14 := by decide +kernel
theorem ok15 : Valid 15 := by decide +kernel
theorem ok16 : Valid 16 := by decide +kernel
theorem ok17 : Valid 17 := by decide +kernel
theorem ok18 : Valid 18 := by decide +kernel
theorem ok19 : Valid 19 := by decide +kernel
theorem ok20 : Valid 20 := by decide +kernel
theorem ok21 : Valid 21 := by decide +kernel
theorem ok22 : Valid 22 := by decide +kernel
theorem ok23 : Valid 23 := by decide +kernel
theorem ok24 : Valid 24 := by decide +kernel
theorem ok25 : Valid 25 := by decide +kernel
theorem ok26 : Valid 26 := by decide +kernel
theorem ok27 : Valid 27 := by decide +kernel
theorem ok28 : Valid 28 := by decide +kernel
theorem ok29 : Valid 29 := by decide +kernel
theorem ok30 : Valid 30 := by decide +kernel
theorem ok31 : Valid 31 := by decide +kernel
theorem ok32 : Valid 32 := by decide +kernel
theorem ok33 : Valid 33 := by decide +kernel
theorem ok34 : Valid 34 := by decide +kernel
theorem ok35 : Valid 35 := by decide +kernel
theorem ok36 : Valid 36 := by decide +kernel
theorem ok37 : Valid 37 := by decide +kernel
theorem ok38 : Valid 38 := by decide +kernel
theorem ok39 : Valid 39 := by decide +kernel
theorem ok40 : Valid 40 := by decide +kernel
theorem ok41 : Valid 41 := by decide +kernel
theorem ok42 : Valid 42 := by decide +kernel
theorem ok43 : Valid 43 := by decide +kernel
theorem ok44 : Valid 44 := by decide +kernel
theorem ok45 : Valid 45 := by decide +kernel
theorem ok46 : Valid 46 := by decide +kernel
theorem ok47 : Valid 47 := by decide +kernel
theorem ok48 : Valid 48 := by decide +kernel
theorem ok49 : Valid 49 := by decide +kernel
theorem ok50 : Valid 50 := by decide +kernel
theorem ok51 : Valid 51 := by decide +kernel
theorem ok52 : Valid 52 := by decide +kernel
theorem ok53 : Valid 53 := by decide +kernel
theorem ok54 : Valid 54 := by decide +kernel
theorem ok55 : Valid 55 := by decide +kernel
theorem ok56 : Valid 56 := by decide +kernel
theorem ok57 : Valid 57 := by decide +kernel
theorem ok58 : Valid 58 := by decide +kernel
theorem ok59 : Valid 59 := by decide +kernel
theorem ok60 : Valid 60 := by decide +kernel
theorem ok61 : Valid 61 := by decide +kernel
theorem ok62 : Valid 62 := by decide +kernel
theorem ok63 : Valid 63 := by decide +kernel
theorem ok64 : Valid 64 := by decide +kernel
theorem ok65 : Valid 65 := by decide +kernel
theorem ok66 : Valid 66 := by decide +kernel
theorem ok67 : Valid 67 := by decide +kernel
theorem ok68 : Valid 68 := by decide +kernel
theorem ok69 : Valid 69 := by decide +kernel
theorem ok70 : Valid 70 := by decide +kernel
theorem ok71 : Valid 71 := by decide +kernel
theorem ok72 : Valid 72 := by decide +kernel
theorem ok73 : Valid 73 := by decide +kernel
theorem ok74 : Valid 74 := by decide +kernel
theorem ok75 : Valid 75 := by decide +kernel
theorem ok76 : Valid 76 := by decide +kernel
theorem ok77 : Valid 77 := by decide +kernel
theorem ok78 : Valid 78 := by decide +kernel
theorem ok79 : Valid 79 := by decide +kernel
theorem ok80 : Valid 80 := by decide +kernel
theorem ok81 : Valid 81 := by decide +kernel
theorem ok82 : Valid 82 := by decide +kernel
theorem ok83 : Valid 83 := by decide +kernel
theorem ok84 : Valid 84 := by decide +kernel
theorem ok85 : Valid 85 := by decide +kernel
theorem ok86 : Valid 86 := by decide +kernel
theorem ok87 : Valid 87 := by decide +kernel
theorem ok88 : Valid 88 := by decide +kernel
theorem ok89 : Valid 89 := by decide +kernel
theorem ok90 : Valid 90 := by decide +kernel
theorem ok91 : Valid 91 := by decide +kernel
theorem ok92 : Valid 92 := by decide +kernel
theorem ok93 : Valid 93 := by decide +kernel
theorem ok94 : Valid 94 := by decide +kernel
theorem valid (k : A) : Valid k := by
  fin_cases k
  · exact ok0
  · exact ok1
  · exact ok2
  · exact ok3
  · exact ok4
  · exact ok5
  · exact ok6
  · exact ok7
  · exact ok8
  · exact ok9
  · exact ok10
  · exact ok11
  · exact ok12
  · exact ok13
  · exact ok14
  · exact ok15
  · exact ok16
  · exact ok17
  · exact ok18
  · exact ok19
  · exact ok20
  · exact ok21
  · exact ok22
  · exact ok23
  · exact ok24
  · exact ok25
  · exact ok26
  · exact ok27
  · exact ok28
  · exact ok29
  · exact ok30
  · exact ok31
  · exact ok32
  · exact ok33
  · exact ok34
  · exact ok35
  · exact ok36
  · exact ok37
  · exact ok38
  · exact ok39
  · exact ok40
  · exact ok41
  · exact ok42
  · exact ok43
  · exact ok44
  · exact ok45
  · exact ok46
  · exact ok47
  · exact ok48
  · exact ok49
  · exact ok50
  · exact ok51
  · exact ok52
  · exact ok53
  · exact ok54
  · exact ok55
  · exact ok56
  · exact ok57
  · exact ok58
  · exact ok59
  · exact ok60
  · exact ok61
  · exact ok62
  · exact ok63
  · exact ok64
  · exact ok65
  · exact ok66
  · exact ok67
  · exact ok68
  · exact ok69
  · exact ok70
  · exact ok71
  · exact ok72
  · exact ok73
  · exact ok74
  · exact ok75
  · exact ok76
  · exact ok77
  · exact ok78
  · exact ok79
  · exact ok80
  · exact ok81
  · exact ok82
  · exact ok83
  · exact ok84
  · exact ok85
  · exact ok86
  · exact ok87
  · exact ok88
  · exact ok89
  · exact ok90
  · exact ok91
  · exact ok92
  · exact ok93
  · exact ok94

theorem preserves (k : A) (a b : V) : G.Adj (motion k a) (motion k b) ↔ G.Adj a b := by
  rw [adjFast,adjFast,(valid k).2]
def f0 (i : F) := Fin.ofNat 95 ((first[i.val]?).getD 0)
def f1 (i : F) := Fin.ofNat 95 ((second[i.val]?).getD 0)
def a0 (i : F) := Fin.ofNat 26 ((flagP[i.val]?).getD 0)
def b0 (i : F) := Fin.ofNat 26 ((flagL[i.val]?).getD 0)
def Same (a b c d : V) : Prop := (a=c ∧ b=d) ∨ (a=d ∧ b=c)
instance (a b c d : V) : Decidable (Same a b c d) := by unfold Same; infer_instance
theorem same_trans {a b c d e f : V} (h : Same a b c d) (k : Same c d e f) : Same a b e f := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases k with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Same]
theorem same_sym {a b c d : V} (h : Same a b c d) : Same c d a b := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Same]
theorem same_map (f : V → V) {a b c d : V} (h : Same a b c d) : Same (f a) (f b) (f c) (f d) := by
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [Same]
theorem unsame {f : V → V} (inj : Function.Injective f) {a b c d : V}
    (h : Same (f a) (f b) (f c) (f d)) : s(a,b)=s(c,d) := by
  rcases h with ⟨h,k⟩|⟨h,k⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨inj h,inj k⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨inj h,inj k⟩)
def Type3 (a b : V) := Same a b 0 14 ∨ Same a b 1 15 ∨ Same a b 2 20
instance (a b : V) : Decidable (Type3 a b) := by unfold Type3; infer_instance
theorem same_kind {a b c d : V} (h : Same a b c d) (k : Type3 c d) : Type3 a b := by
  rcases k with k|k|k
  · exact Or.inl (same_trans h k)
  · exact Or.inr (Or.inl (same_trans h k))
  · exact Or.inr (Or.inr (same_trans h k))
theorem flagsAll : ∀a b : V,G.Adj a b → ∃i:F, Same a b (a0 i) (b0 i) := by decide +kernel
theorem stage0 : ∀i:F, Same (motion (f0 i) (a0 i)) (motion (f0 i) (b0 i)) 0 13 := by decide +kernel
theorem stage1 : ∀j:F, Same (motion (f1 j) 0) (motion (f1 j) 13) 0 13 ∧
    (Same (motion (f1 j) (a0 j)) (motion (f1 j) (b0 j)) 0 13 ∨
      Type3 (motion (f1 j) (a0 j)) (motion (f1 j) (b0 j))) := by decide +kernel
def Orbit (a b c d : V) := ∃e : V → V, Function.Bijective e ∧
  (∀i j,G.Adj (e i) (e j) ↔ G.Adj i j) ∧ Same (e a) (e b) 0 13 ∧ Type3 (e c) (e d)
theorem classify {a b c d : V} (firstEdge : G.Adj a b) (secondEdge : G.Adj c d)
    (ne : s(a,b)≠s(c,d)) : Orbit a b c d := by
  obtain ⟨i,hi⟩ := flagsAll a b firstEdge
  let f := motion (f0 i)
  obtain ⟨j,hj⟩ := flagsAll (f c) (f d) ((preserves _ _ _).mpr secondEdge)
  let g := motion (f1 j)
  let e := g ∘ f
  have inj : Function.Injective e := fun u v h =>
    (valid (f0 i)).1 u v ((valid (f1 j)).1 (f u) (f v) h)
  have fst : Same (e a) (e b) 0 13 := same_trans
    (same_map g (same_trans (same_map f hi) (stage0 i))) (stage1 j).1
  have snd := same_map g hj
  refine ⟨e,⟨inj,Finite.injective_iff_surjective.mp inj⟩,fun u v =>
    (preserves (f1 j) _ _).trans (preserves (f0 i) _ _),fst,?_⟩
  rcases (stage1 j).2 with dup|good
  · exact False.elim (ne (unsame inj (same_trans fst (same_sym (same_trans snd dup)))))
  · exact same_kind snd good
def RepeatedOrbit (C : Circuit) : Prop :=
  ∃ j < C.size, (gateAt C j).op=GateOp.and ∧ ¬BelowF G C j ∧
    ∃a b c d : V, G.Adj a b ∧ G.Adj c d ∧ Orbit a b c d ∧
      readsAtMost C 26 [a.val,b.val] 1=false ∧ readsAtMost C 26 [c.val,d.val] 1=false ∧
      gateVal 26 C j (pairInput a b)=true ∧ gateVal 26 C j (pairInput c d)=true
theorem orbitIfSmall {C : Circuit} {o : List Nat} (hm : Monotone2 C) (ht : Tests C o)
    (out : o.length≤2) (small : C.size≤62) :
    ∃T : Circuit, IsLeastAO G T ∧ TopForm G T ∧ T.size≤63 ∧ RepeatedOrbit T := by
  obtain ⟨T,least,top,sz,j,hj,tag,cold,a,b,c,d,ab,cd,ne,r1,r2,v1,v2⟩ := repeatedIfSmall hm ht out small
  exact ⟨T,least,top,sz,j,hj,tag,cold,a,b,c,d,ab,cd,classify ab cd ne,r1,r2,v1,v2⟩
end PEqualNP.Outside.PlaneRead17245

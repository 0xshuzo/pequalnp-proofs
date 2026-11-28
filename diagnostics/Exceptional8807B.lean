import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_8807.Column
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


theorem app_mono (A A' B B' : List Bool) (hA : A.length = A'.length)
    (ha : ∀ i, A.getD i false = true → A'.getD i false = true)
    (hb : ∀ i, B.getD i false = true → B'.getD i false = true) :
    ∀ i, (A ++ B).getD i false = true → (A' ++ B').getD i false = true := by
  intro i
  by_cases hi : i < A.length
  · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hA ▸ hi)]; exact ha i
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hA]
    exact hb _


def val (C : Circuit) (n : ℕ) (l : Fin n) (Z : Finset (Fin n)) (w : ℕ) : Bool :=
  (C.wires (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n)))).getD w false

theorem inc_len (n : ℕ) (Z Y : Finset (Fin n)) :
    (PEqualNP.GenericRejection.incidenceInput Z Y).length = n + n := by
  simp [PEqualNP.GenericRejection.incidenceInput]

theorem val_mono (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (Z Z' : Finset (Fin n)) (h : Z ⊆ Z') (w : ℕ) :
    val C n l Z w = true → val C n l Z' w = true := by
  obtain ⟨hao, _, h2⟩ := hC
  have hleg : ∀ g' ∈ C.gates, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
    fun g' hg' => ⟨hao g' hg', le_of_eq (h2 g' hg')⟩
  refine mono2 C.gates hleg _ _ (by rw [inc_len, inc_len]) ?_ w
  refine app_mono _ _ _ _ (by simp) ?_ (fun _ => id)
  exact ofFn_mono n _ _ (fun v hv => by simp only [decide_eq_true_eq] at hv ⊢; exact h hv)

theorem val_input (C : Circuit) (n : ℕ) (l : Fin n) (Z Z' : Finset (Fin n)) (w : ℕ)
    (hw : w < n + n) (hn : n ≤ w) : val C n l Z w = val C n l Z' w := by
  unfold val
  show (wf C.gates _).getD w false = (wf C.gates _).getD w false
  rw [wf_keep _ _ _ (by rw [inc_len]; exact hw), wf_keep _ _ _ (by rw [inc_len]; exact hw)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
  simp

theorem val_point (C : Circuit) (n : ℕ) (l : Fin n) (p : Fin n) (w : ℕ)
    (hw : w < n) : val C n l {p} w = true → p.val = w := by
  unfold val
  show (wf C.gates _).getD w false = true → _
  rw [wf_keep _ _ _ (by rw [inc_len]; omega)]
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw]
  intro h
  simp at h
  rw [← h]

theorem val_gate (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (k : ℕ) (hk : k < C.size) :
    ∃ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] ∧
      a < n + n + k ∧ b < n + n + k ∧
      ((PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or) ∧
      ∀ Z, val C n l Z (n + n + k) =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op.eval [val C n l Z a, val C n l Z b] := by
  obtain ⟨hao, hrb, h2⟩ := hC
  have hk' : k < C.gates.length := hk
  have hG : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk']
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk'
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (h2 _ hmem)
  have hlt : ∀ i ∈ [a, b], i < n + n + k := by
    intro i hi
    have := hrb k hk' i
    rw [hG, hin] at this
    exact this hi
  refine ⟨a, b, by rw [hG, hin], hlt a (by simp), hlt b (by simp), by rw [hG]; exact hao _ hmem, ?_⟩
  intro Z
  have hlen := inc_len n Z ({l} : Finset (Fin n))
  have g1 := gate_val C.gates (PEqualNP.GenericRejection.incidenceInput Z ({l} : Finset (Fin n))) k hk'
  rw [hlen, hin] at g1
  unfold val
  show (wf C.gates _).getD (n + n + k) false = _
  rw [g1, hG]
  show _ = C.gates[k].op.eval [(wf C.gates _).getD a false, (wf C.gates _).getD b false]
  rw [wire_take C.gates _ k a (by rw [hlen]; exact hlt a (by simp)) (le_of_lt hk'),
    wire_take C.gates _ k b (by rw [hlen]; exact hlt b (by simp)) (le_of_lt hk')]
  simp

open Finset in
theorem colors {n} (f : Nat → Fin n × Fin n) (S : Finset Nat) :
    ∃ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) ∧
      n≤S.card+(univ.image c).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨id,by simp,by simp⟩
  | @insert j S hj ih =>
    obtain ⟨c,ok,cnt⟩ := ih
    let a := c (f j).1
    let b := c (f j).2
    let up := fun z : Fin n => if z=a then b else z
    let d := up ∘ c
    refine ⟨d,?_,?_⟩
    · intro k hk
      rcases mem_insert.mp hk with rfl|hh
      · change up a=up b
        simp [up]
      · exact congrArg up (ok k hh)
    · have sub : univ.image c ⊆ insert a (univ.image d) := by
        intro t ht
        obtain ⟨u,_,rfl⟩ := mem_image.mp ht
        by_cases eq : c u=a
        · exact mem_insert.mpr (.inl eq)
        · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_univ _,by simp [d,up,eq]⟩)
      have h := (card_le_card sub).trans (card_insert_le _ _)
      rw [card_insert_of_notMem hj]
      omega

open Finset in
theorem graph_count {n : ℕ} (S : Finset ℕ) (f : ℕ → Fin n × Fin n) (X : Finset (Fin n))
    (hX : ∀ c : Fin n → Fin n, (∀ j∈S,c (f j).1=c (f j).2) →
      ∀ u ∈ X, ∀ v ∈ X, c u=c v) : X.card≤S.card+1 := by
  classical
  rcases X.eq_empty_or_nonempty with rfl|⟨v,hv⟩
  · simp
  obtain ⟨c,ok,hc⟩ := colors f S
  have sub : univ.image c⊆insert (c v) ((univ\X).image c) := by
    intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    by_cases hu : u∈X
    · exact mem_insert.mpr (.inl (hX c ok u hu v hv))
    · exact mem_insert_of_mem (mem_image.mpr ⟨u,mem_sdiff.mpr ⟨mem_univ _,hu⟩,rfl⟩)
  have hc' := (card_le_card sub).trans (card_insert_le _ _)
  have imgs : ((univ\X).image c).card≤(univ\X).card := card_image_le
  have add := card_sdiff_add_card_eq_card (subset_univ X)
  simp only [card_univ,Fintype.card_fin] at add
  omega

theorem reach (C : Circuit) (n : ℕ) (l : Fin n) (hC : PEqualNP.TopForm.IsAO2 (n + n) C)
    (color : Fin n → Fin n) (Zb : Finset (Fin n))
    (hedge : ∀ k < C.size, ∀ a b, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs = [a, b] →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = GateOp.or →
      val C n l Zb (n + n + k) = false → ∀ u v : Fin n, u ≠ v →
      val C n l {u} a = true → val C n l {v} b = true →
      ∃ u' v', val C n l {u'} a = true ∧ val C n l {v'} b = true ∧ color u'=color v') :
    ∀ w, w < n + n + C.size → val C n l Zb w = false → ∀ u v : Fin n,
      val C n l {u} w = true → val C n l {v} w = true → color u=color v := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw hgood u v hu hv
  by_cases h1 : w < n
  · have e1 := val_point C n l u w h1 hu
    have e2 := val_point C n l v w h1 hv
    have : u = v := Fin.ext (by omega)
    rw [this]
  by_cases h2 : w < n + n
  · rw [val_input C n l {u} Zb w h2 (by omega)] at hu
    rw [hu] at hgood
    exact absurd hgood (by simp)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + n + k := ⟨w - (n + n), by omega⟩
  have hk : k < C.size := by omega
  obtain ⟨a, b, hin, ha, hb, hop, hval⟩ := val_gate C n l hC k hk
  rw [hval] at hgood hu hv
  rcases hop with hop | hop
  · rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.all_cons, List.all_nil, id, Bool.and_true, Bool.and_eq_true,
      Bool.and_eq_false_iff] at hgood hu hv
    rcases hgood with hg | hg
    · exact ih a ha (by omega) hg u v hu.1 hv.1
    · exact ih b hb (by omega) hg u v hu.2 hv.2
  · have hop' := hop
    rw [hop] at hgood hu hv
    simp only [GateOp.eval, List.any_cons, List.any_nil, id, Bool.or_false, Bool.or_eq_true,
      Bool.or_eq_false_iff] at hgood hu hv
    have hgw : val C n l Zb (n + n + k) = false := by
      rw [hval, hop]; simp [GateOp.eval, hgood.1, hgood.2]
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact ih a ha (by omega) hgood.1 u v hu hv
    · by_cases huv : u = v
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw u v huv hu hv
      exact ((ih a ha (by omega) hgood.1 u u' hu hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' v hv' hv)
    · by_cases huv : v = u
      · rw [huv]
      obtain ⟨u', v', hu', hv', hr⟩ := hedge k hk a b hin hop' hgw v u huv hv hu
      exact (((ih a ha (by omega) hgood.1 v u' hv hu').trans hr).trans
        (ih b hb (by omega) hgood.2 v' u hv' hu)).symm
    · exact ih b hb (by omega) hgood.2 u v hu hv

end PEqualNP.Outside.L_meta_8807.Column

open PEqualNP.Outside.L_meta_8807.Column PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8807.Column : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Fin x1)) (x4 : Fin x1),   PEqualNP.TopForm.IsAO2 (x1 + x1) x2 →     x2.output < x1 + x1 + x2.size →       (∀ x7 ∈ x3, x2.eval (PEqualNP.GenericRejection.incidenceInput {x7} {x4}) = Bool.true) →         x2.eval (PEqualNP.GenericRejection.incidenceInput x3ᶜ {x4}) = Bool.false →           ∃ (x9 : Finset ℕ),             x3.card ≤ x9.card + (1 : ℕ) ∧               ∀ x10 ∈ x9,                 x10 < x2.size ∧                   (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                     have x12 : Finset (Fin x1) → Bool := fun (x12 : Finset (Fin x1)) => PEqualNP.CircuitLowerBounds.wireValue x2 (PEqualNP.GenericRejection.incidenceInput x12 {x4}) (x1 + x1 + x10);                     x12 x3ᶜ = Bool.false ∧ (∃ (x13 : Fin x1) (x14 : Fin x1), x13 ≠ x14 ∧ x12 {x13} = Bool.true ∧ x12 {x14} = Bool.true) ∧ ∀ (x13 : Fin x1), x12 {x13} = Bool.true → x13 ∈ x3 := by
  intro n C X l hC hout hacc hrej
  classical
  have hrej' : val C n l Xᶜ C.output = false := hrej
  have hacc' : ∀ p ∈ X, val C n l {p} C.output = true := hacc
  have hsub : ∀ w, val C n l Xᶜ w = false → ∀ p : Fin n, val C n l {p} w = true → p ∈ X := by
    intro w hw p hp
    by_contra hpX
    have := val_mono C n l hC {p} Xᶜ (by simpa using hpX) w hp
    rw [hw] at this
    exact absurd this (by simp)
  refine ⟨(Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true),
    ?_, ?_⟩
  · rcases X.eq_empty_or_nonempty with hX | ⟨p0, _⟩
    · rw [hX]; simp
    let A : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
    let B : ℕ → ℕ := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
    let f : ℕ → Fin n × Fin n := fun j =>
      if h : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A j) = true ∧ val C n l {v} (B j) = true
      then (h.choose, h.choose_spec.choose) else (p0, p0)
    apply graph_count _ f X
    intro color glued u hu v hv
    refine reach C n l hC color Xᶜ ?_ C.output hout hrej' u v (hacc' u hu) (hacc' v hv)
    intro k hk a b hin hop hgood u v huv hua hvb
    have hAk : A k = a := by simp [A, hin]
    have hBk : B k = b := by simp [B, hin]
    have hex : ∃ u v : Fin n, u ≠ v ∧ val C n l {u} (A k) = true ∧ val C n l {v} (B k) = true :=
      ⟨u, v, huv, hAk ▸ hua, hBk ▸ hvb⟩
    obtain ⟨a', b', hin', _, _, _, hval⟩ := val_gate C n l hC k hk
    rw [hin] at hin'
    simp only [List.cons.injEq, and_true] at hin'
    obtain ⟨rfl, rfl⟩ := hin'
    have hk9 : k ∈ (Finset.range C.size).filter (fun j =>
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      val C n l Xᶜ (n + n + j) = false ∧
      ∃ p q : Fin n, p ≠ q ∧ val C n l {p} (n + n + j) = true ∧ val C n l {q} (n + n + j) = true) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hop, hgood, u, v, huv, ?_, ?_⟩
      · rw [hval, hop]; simp [GateOp.eval, hua]
      · rw [hval, hop]; simp [GateOp.eval, hvb]
    have hfk : f k = (hex.choose, hex.choose_spec.choose) := by
      simp only [f, hex, dite_true]
    obtain ⟨hne, h1, h2⟩ := hex.choose_spec.choose_spec
    refine ⟨hex.choose, hex.choose_spec.choose, hAk ▸ h1, hBk ▸ h2, ?_⟩
    simpa only [hfk] using glued k hk9
  · intro j hj
    obtain ⟨hjr, hop, hgood, p, q, hpq, hp, hq⟩ := Finset.mem_filter.mp hj
    refine ⟨Finset.mem_range.mp hjr, hop, ?_⟩
    show val C n l Xᶜ (n + n + j) = false ∧
      (∃ (x13 : Fin n) (x14 : Fin n), x13 ≠ x14 ∧ val C n l {x13} (n + n + j) = true ∧
        val C n l {x14} (n + n + j) = true) ∧
      ∀ (x13 : Fin n), val C n l {x13} (n + n + j) = true → x13 ∈ X
    exact ⟨hgood, ⟨p, q, hpq, hp, hq⟩, hsub _ hgood⟩

namespace PEqualNP.Outside.L_meta_8807
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.GenericRejection
open Finset
def Good {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (j : Nat) (l : Fin n) : Prop :=
  (gateAt C j).op=.or ∧ wireValue C (incidenceInput (S l)ᶜ {l}) (n+n+j)=false ∧
  (∃ p r : Fin n, p≠r ∧ wireValue C (incidenceInput {p} {l}) (n+n+j)=true ∧
    wireValue C (incidenceInput {r} {l}) (n+n+j)=true) ∧
  (∀ p, wireValue C (incidenceInput {p} {l}) (n+n+j)=true → p∈S l)
noncomputable def load {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (j : Nat) : Nat := by
  classical
  exact (univ.filter fun l => Good C S j l).card
noncomputable def heavy {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (t : Nat) :=
  (range C.size).filter (fun j => t<load C S j)
theorem column_mass {n q : Nat} (C : Circuit) (S : Fin n → Finset (Fin n))
    (qpos : 1≤q) (degree : ∀ l,(S l).card=q+1) (ao : IsAO2 (n+n) C)
    (valid : C.output<n+n+C.size) (hit : RightOnIncidentPairs S C)
    (off : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false) :
    n*q≤∑ j∈range C.size, load C S j := by
  classical
  have line (l : Fin n) : q≤((range C.size).filter (fun j => Good C S j l)).card := by
    obtain ⟨J,sz,jok⟩ := Column n C (S l) l ao valid (hit l) (off _ _ (by simpa) (by
      intro k hk
      obtain rfl : k=l := mem_singleton.mp hk
      exact disjoint_compl_right))
    rw [degree] at sz
    have sub : J⊆(range C.size).filter (fun j => Good C S j l) := by
      intro j hj
      obtain ⟨bound,op,data⟩ := jok j hj
      exact mem_filter.mpr ⟨mem_range.mpr bound,op,data⟩
    have many := card_le_card sub
    omega
  calc
    n*q = ∑ _ : Fin n, q := by simp
    _ ≤ ∑ l : Fin n, ((range C.size).filter (fun j => Good C S j l)).card := sum_le_sum (fun l _ => line l)
    _ = ∑ j∈range C.size, load C S j := by
      simp only [load,card_filter]
      rw [sum_comm]

theorem mass_by_tail {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (t : Nat) :
    (∑ j∈range C.size, load C S j) ≤ t*C.size+(n-t)*(heavy C S t).card := by
  classical
  let J := range C.size
  let H := heavy C S t
  have sub : H⊆J := filter_subset _ _
  have cardJ : (J\H).card+H.card=C.size := by
    simpa [J] using card_sdiff_add_card_eq_card sub
  have small : ∀ j∈J\H, load C S j ≤ t := by
    intro j hj
    have h := mem_sdiff.mp hj
    exact Nat.le_of_not_gt (fun gt => h.2 (mem_filter.mpr ⟨h.1,gt⟩))
  have total : ∀ j∈H, load C S j≤n := by
    intro j _
    simpa [load] using (card_le_card (filter_subset (fun l => Good C S j l) (univ : Finset (Fin n))))
  have split := sum_sdiff sub (f := fun j => load C S j)
  have s := sum_le_sum small
  have h := sum_le_sum total
  simp only [sum_const,nsmul_eq_mul] at s h
  change (∑ j∈J,load C S j)≤t*C.size+(n-t)*H.card
  rw [←split]
  calc
    _ ≤ (J\H).card*t+H.card*n := Nat.add_le_add s h
    _ ≤ _ := by
      rw [←cardJ,Nat.mul_add]
      have z := Nat.mul_le_mul_left H.card (show n≤t+(n-t) by omega)
      rw [Nat.mul_add] at z
      nlinarith only [z]

theorem tail_budget {n q t : Nat} (C : Circuit) (S : Fin n → Finset (Fin n))
    (mass : n*q≤∑ j∈range C.size, load C S j) (tpos : 0<t) (tcap : t≤100)
    (few : 100*(heavy C S t).card≤(100-t)*q) : n*q≤100*C.size := by
  have pay := mass_by_tail C S t
  have src : n*q≤t*C.size+n*(heavy C S t).card := mass.trans
    (pay.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le n t)) _))
  have right := Nat.mul_le_mul_left n few
  have left := Nat.mul_le_mul_left 100 src
  have sub : (100-t)+t=100 := by omega
  have eq := congrArg (fun k : Nat => n*k*q) sub
  have done : t*(n*q)≤t*(100*C.size) := by nlinarith only [right,left,eq]
  exact Nat.le_of_mul_le_mul_left done tpos

theorem many_medium {n q} (C : Circuit) (S : Fin n → Finset (Fin n))
    (mass : n*q≤∑ j∈range C.size, load C S j) (small : 100*C.size<n*q) :
    ∀ t : Nat, 0<t → t≤100 → (100-t)*q<100*(heavy C S t).card := by
  intro t ht tc
  by_contra! bd
  exact (Nat.not_le_of_gt small) (tail_budget C S mass ht tc bd)

namespace Entropy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem prefix_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, prefix_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact prefix_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [prefix_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

section Circ2

variable {n : ℕ} {C : Circuit}

theorem acts_mono (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩


end Circ2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def input {N : ℕ} (P L : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p∈P)) (fun l => decide (l∈L))

def Hit {N : ℕ} (I : Fin N → Fin N → Prop) (P L : Finset (Fin N)) : Prop :=
  ∃ p ∈ P, ∃ l ∈ L, I p l

theorem input_l {N} (P L : Finset (Fin N)) (p : Fin N) :
    input P L (Fin.castAdd N p) = decide (p∈P) := Fin.addCases_left ..
theorem input_r {N} (P L : Finset (Fin N)) (l : Fin N) :
    input P L (Fin.natAdd N l) = decide (l∈L) := Fin.addCases_right ..

theorem wire_mono {N} {C : Circuit} (hm : Monotone2 C) {P P' L L' : Finset (Fin N)}
    (hp : P ⊆ P') (hl : L ⊆ L') (w : ℕ) :
    val C (input P L) w = true → val C (input P' L') w = true := by
  apply acts_mono hm
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp only [input_l,decide_eq_true_eq]
    exact fun h => hp h
  · intro l
    simp only [input_r,decide_eq_true_eq]
    exact fun h => hl h

theorem and_parents {n : ℕ} (C : Circuit) (ho : n ≤ C.output)
    (hop : ∃ g : Gate, C.gates[C.output-n]? = some g ∧ g.op = GateOp.and)
    (hs : ∀ j (g : Gate), C.gates[j]? = some g →
      ∃ a b : ℕ, g.inputs=[a,b] ∧ a<b ∧ b<n+j) :
    ∃ a b : ℕ, a<b ∧ b<C.output ∧ ∀ x : Fin n → Bool,
      circuitFun n C x = (val C x a && val C x b) := by
  obtain ⟨g,hg,op⟩ := hop
  obtain ⟨a,b,ins,ab,bo⟩ := hs _ _ hg
  have eq : n+(C.output-n)=C.output := by omega
  rw [eq] at bo
  refine ⟨a,b,ab,bo,?_⟩
  intro x
  change val C x C.output = _
  have hh := val_gate C x hg
  rw [eq,ins,op] at hh
  simpa [operand,ab.trans bo,bo,GateOp.eval] using hh

def PairOK {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ p l, I p l → circuitFun (N+N) C
    (fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l)) = true

def Rejects {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ x : Fin (N+N) → Bool, Fintype.card {l : Fin N // x (Fin.natAdd N l) = true} ≤ q →
    (¬∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      circuitFun (N+N) C x = false

theorem sets_exact {N q} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hm : Monotone2 C) (hpos : PairOK I C) (hneg : Rejects q I C)
    (P L : Finset (Fin N)) (small : L.card ≤ q) :
    circuitFun (N+N) C (input P L) = true ↔ Hit I P L := by
  constructor
  · intro h
    by_contra bad
    have card : Fintype.card {l : Fin N // input P L (Fin.natAdd N l) = true} = L.card := by
      rw [Fintype.card_subtype]
      congr 1
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,input_r,decide_eq_true_eq]
    have err := hneg (input P L) (card.trans_le small) (by
      rintro ⟨p,l,pl,hp,hl⟩
      exact bad ⟨p,by simpa only [input_l,decide_eq_true_eq] using hp,l,
        by simpa only [input_r,decide_eq_true_eq] using hl,pl⟩)
    simp [h] at err
  · rintro ⟨p,hp,l,hl,pl⟩
    have good := hpos p l pl
    apply acts_mono (C:=C) hm (x:=fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l))
      (y:=input P L) _ C.output good
    rintro i h
    rcases of_decide_eq_true h with rfl | rfl
    · rw [input_l]; exact decide_eq_true hp
    · rw [input_r]; exact decide_eq_true hl


def outside {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (L : Finset (Fin N)) : Finset (Fin N) := Finset.univ.filter fun p => ∀ l ∈ L, ¬ I p l

theorem outside_miss {N} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (L : Finset (Fin N)) : ¬Hit I (outside I L) L := by
  rintro ⟨p,hp,l,hl,h⟩
  exact (Finset.mem_filter.mp hp).2 l hl h

theorem escape_line {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {L : Finset (Fin N)} (small : L.card≤q) {b : Fin N} (out : b∉L) :
    ∃ p ∈ outside I L, I p b := by
  classical
  by_contra fail
  let S := Finset.univ.filter (fun p : Fin N => I p b)
  have chooseLine (p : Fin N) (hp : p ∈ S) : ∃ l ∈ L, I p l := by
    by_contra none
    have po : p ∈ outside I L := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun l hl h => none ⟨l,hl,h⟩⟩
    exact fail ⟨p,po,(Finset.mem_filter.mp hp).2⟩
  choose! f hf using chooseLine
  have bound : S.card ≤ L.card := by
    apply Finset.card_le_card_of_injOn f (fun p hp => (hf p hp).1)
    intro p hp p' hp' same
    by_contra ne
    have one := unique p p' ne
    have shared : I p (f p) ∧ I p' (f p) := ⟨(hf p hp).2,same ▸ (hf p' hp').2⟩
    have eq := one.unique shared ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hp').2⟩
    exact out (eq ▸ (hf p hp).1)
  have card : S.card = q+1 := by simpa only [S,Fintype.card_subtype] using hdeg b
  omega

theorem incomparable_inputs {N q} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    {L M : Finset (Fin N)} (ls : L.card≤q) (ms : M.card≤q) (ne : L≠M) :
    Hit I (outside I L ∪ outside I M) (L∪M) := by
  classical
  by_cases sub : M ⊆ L
  · obtain ⟨b,bl,bm⟩ := Finset.not_subset.mp (fun rev : L ⊆ M => ne (Finset.Subset.antisymm rev sub))
    obtain ⟨p,hp,hit⟩ := escape_line I hdeg unique ms bm
    exact ⟨p,Finset.mem_union_right _ hp,b,Finset.mem_union_left _ bl,hit⟩
  · obtain ⟨b,bm,bl⟩ := Finset.not_subset.mp sub
    obtain ⟨p,hp,hit⟩ := escape_line I hdeg unique ls bl
    exact ⟨p,Finset.mem_union_left _ hp,b,Finset.mem_union_right _ bm,hit⟩

theorem true_of_incidence {N} {I : Fin N → Fin N → Prop} {C : Circuit}
    (hm : Monotone2 C) (accept : PairOK I C) (P L : Finset (Fin N)) (hit : Hit I P L) :
    circuitFun (N+N) C (input P L) = true := by
  obtain ⟨p,hp,l,hl,pl⟩ := hit
  apply acts_mono (C:=C) hm (x:=fun z => decide (z = Fin.castAdd N p ∨ z = Fin.natAdd N l))
    (y:=input P L) _ C.output (accept p l pl)
  rintro i h
  rcases of_decide_eq_true h with rfl | rfl
  · rw [input_l]; exact decide_eq_true hp
  · rw [input_r]; exact decide_eq_true hl

theorem root_separates {N q} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    {L M : Finset (Fin N)} (ls : L.card≤q) (ms : M.card≤q) (ne : L≠M) :
    circuitFun (N+N) C (input (outside I L) L) = false ∧
    circuitFun (N+N) C (input (outside I M) M) = false ∧
    circuitFun (N+N) C (input (outside I L ∪ outside I M) (L∪M)) = true := by
  have off (X : Finset (Fin N)) (small : X.card≤q) :
      circuitFun (N+N) C (input (outside I X) X) = false := by
    have contra := (sets_exact hm accept reject (outside I X) X small).not.mpr (outside_miss I X)
    cases h : circuitFun (N+N) C (input (outside I X) X) <;> simp_all
  exact ⟨off L ls,off M ms,true_of_incidence hm accept _ _ (incomparable_inputs I hdeg unique ls ms ne)⟩


def andOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

def ands (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun j => andOp C.gates[j.val].op = true

def choices {n : ℕ} (C : Circuit) (x : Fin n → Bool) : Finset (Fin C.gates.length) :=
  (ands C).filter fun j => val C x (C.gates[j.val].inputs.getD 0 0) = true

theorem union_false {n} (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g → ∃ a b : ℕ, g.inputs=[a,b] ∧ a<n+j ∧ b<n+j)
    (x y z : Fin n → Bool) (hz : ∀ i, z i = (x i || y i))
    (same : choices C x = choices C y) :
    ∀ i, val C x i=false → val C y i=false → val C z i=false := by
  classical
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hx hy
    by_cases raw : i<n
    · let j : Fin n := ⟨i,raw⟩
      change val C z j.val = false
      rw [val_input, hz, ←val_input C x, ←val_input C y]
      simp [j,hx,hy]
    by_cases gone : n + C.gates.length ≤ i
    · exact val_beyond _ _ gone
    let k := i-n
    have hk : k<C.gates.length := by dsimp [k]; omega
    let j : Fin C.gates.length := ⟨k,hk⟩
    let g : Gate := C.gates[j.val]
    have hg : C.gates[k]?=some g := List.getElem?_eq_some_iff.mpr ⟨hk,rfl⟩
    obtain ⟨a,b,ins,ab,bk⟩ := hs k g hg
    have node : n+k=i := by dsimp [k]; omega
    have ai : a < i := by omega
    have bi : b < i := by omega
    have ev (t : Fin n → Bool) : val C t i=g.op.eval [val C t a,val C t b] := by
      have h := val_gate C t hg
      rw [node,ins] at h
      simpa [operand,ai,bi] using h
    rw [ev] at hx hy ⊢
    have hop := (hm g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with hand | hor
    · have eq : val C x a = val C y a := by
        have h : j ∈ choices C x ↔ j ∈ choices C y := by rw [same]
        have h' : val C x a=true ↔ val C y a=true := by
          have active : j∈ands C := Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,show andOp g.op=true by rw [hand]; rfl⟩
          simp only [choices,Finset.mem_filter,active,true_and] at h
          rw [show C.gates[j.val].inputs=[a,b] from ins] at h
          exact h
        cases ax : val C x a <;> cases ay : val C y a <;> simp_all
      rw [hand] at hx hy ⊢
      simp only [GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] at hx hy ⊢
      cases ax : val C x a with
      | false =>
        have ay : val C y a=false := eq.symm.trans ax
        simp [ih a ai ax ay]
      | true =>
        have ay : val C y a=true := eq.symm.trans ax
        have bx : val C x b=false := by simpa [ax] using hx
        have by' : val C y b=false := by simpa [ay] using hy
        simp [ih b bi bx by']
    · rw [hor] at hx hy ⊢
      simp only [GateOp.eval,List.any_cons,List.any_nil,id_eq,Bool.or_false,Bool.or_eq_false_iff] at hx hy ⊢
      exact ⟨ih a ai hx.1 hy.1,ih b bi hx.2 hy.2⟩

theorem input_union {N} (P Q L M : Finset (Fin N)) (i : Fin (N+N)) :
    input (P∪Q) (L∪M) i = (input P L i || input Q M i) := by
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [input_l,Finset.mem_union]
  · intro l
    rw [input_r,input_r,input_r]; simp [Finset.mem_union]

theorem many_and_choices {N q} (C : Circuit) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hdeg : ∀ l, Fintype.card {p : Fin N // I p l} = q+1)
    (unique : ∀ p p' : Fin N, p≠p' → ∃! l, I p l ∧ I p' l)
    (hm : Monotone2 C) (accept : PairOK I C) (reject : Rejects q I C)
    (hs : ∀ j (g : Gate), C.gates[j]?=some g →
      ∃ a b : ℕ, g.inputs=[a,b] ∧ a<N+N+j ∧ b<N+N+j) :
    (Finset.univ.powersetCard q : Finset (Finset (Fin N))).card ≤ 2^(ands C).card := by
  classical
  let tag := fun L : Finset (Fin N) => choices C (input (outside I L) L)
  rw [←Finset.card_powerset]
  apply Finset.card_le_card_of_injOn tag
  · intro L _
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · intro L hL M hM eq
    by_contra ne
    have ls := (Finset.mem_powersetCard.mp hL).2.le
    have ms := (Finset.mem_powersetCard.mp hM).2.le
    obtain ⟨a,b,c⟩ := root_separates I hdeg unique hm accept reject ls ms ne
    have err := union_false C hm hs _ _ _
      (input_union (outside I L) (outside I M) L M) eq C.output a b
    change circuitFun (N+N) C (input (outside I L ∪ outside I M) (L∪M))=false at err
    simp [c] at err

theorem separate {N} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro eq
  have e := congrArg Fin.val eq
  have := p.isLt
  change p.val=N+l.val at e
  omega
open Finset PEqualNP.TopForm PEqualNP.GenericRejection
theorem family_encode {N q b : Nat} (cap : q*b≤N) :
    b^q ≤ (univ.powersetCard q : Finset (Finset (Fin N))).card := by
  classical
  let embed : Fin q × Fin b ↪ Fin N :=
    ⟨fun z => Fin.castLE cap (finProdFinEquiv z),fun x y h =>
      finProdFinEquiv.injective (Fin.ext (congrArg (fun i : Fin N => i.val) h))⟩
  let graph (f : Fin q → Fin b) := univ.image (fun i => embed (i,f i))
  have image (f : Fin q → Fin b) : (graph f).card=q := by
    have inj : Function.Injective (fun i => embed (i,f i)) :=
      fun i j eq => congrArg Prod.fst (embed.injective eq)
    simp [graph,card_image_of_injective _ inj]
  let tag (f : Fin q → Fin b) : ↑(univ.powersetCard q : Finset (Finset (Fin N))) :=
    ⟨graph f,mem_powersetCard.mpr ⟨subset_univ _,image f⟩⟩
  have inj : Function.Injective tag := by
    intro f g h
    have sets : graph f=graph g := congrArg Subtype.val h
    funext i
    have hi : embed (i,f i)∈graph f := mem_image_of_mem _ (mem_univ i)
    rw [sets] at hi
    obtain ⟨j,_,eq⟩ := mem_image.mp hi
    have ee := embed.injective eq
    have ji : j=i := congrArg Prod.fst ee
    subst j
    exact (congrArg Prod.snd ee).symm
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective tag inj

theorem and_power_floor {N q : Nat} (C : Circuit) (S : Fin N → Finset (Fin N))
    (col : ∀ l,(S l).card=q+1) (uniq : ∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (b : Nat) (cap : q*b≤N) : b^q ≤ 2^(ands C).card := by
  classical
  let I := fun p l : Fin N => p ∈ S l
  have deg (l : Fin N) : Fintype.card {p : Fin N // I p l} = q+1 := by
    simpa [I,Fintype.card_subtype] using col l
  have hit (p l : Fin N) (h : I p l) : circuitFun (N+N) C (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l))=true := by
    let x : Fin (N+N) → Bool := Fin.addCases (fun a => decide (a∈({p}:Finset (Fin N)))) (fun b => decide (b∈({l}:Finset (Fin N))))
    have raw : List.ofFn x = incidenceInput {p} {l} := List.ofFn_fin_append _ _
    have fn : x = (fun i => decide (i=Fin.castAdd N p ∨ i=Fin.natAdd N l)) := by
      funext i
      refine Fin.addCases (fun a => ?_) (fun b => ?_) i
      · change x (Fin.castAdd N a) = _
        rw [show x (Fin.castAdd N a) = decide (a∈({p}:Finset (Fin N))) from Fin.addCases_left ..]
        simp only [Finset.mem_singleton,Fin.castAdd_inj,separate a l,or_false]
      · change x (Fin.natAdd N b) = _
        rw [show x (Fin.natAdd N b) = decide (b∈({l}:Finset (Fin N))) from Fin.addCases_right ..]
        simp only [Finset.mem_singleton,Fin.natAdd_inj,Ne.symm (separate p b),false_or]
    rw [←fn]
    change C.eval (List.ofFn x)=true
    rw [raw]
    exact pos l p h
  have off (x : Fin (N+N) → Bool) (lim : Fintype.card {l : Fin N // x (Fin.natAdd N l)=true} ≤ q)
      (none : ¬ ∃ p l, I p l ∧ x (Fin.castAdd N p)=true ∧ x (Fin.natAdd N l)=true) : circuitFun (N+N) C x=false := by
    let X := Finset.univ.filter (fun p => x (Fin.castAdd N p)=true)
    let Y := Finset.univ.filter (fun l => x (Fin.natAdd N l)=true)
    have eq : x = Fin.addCases (fun p => decide (p∈X)) (fun l => decide (l∈Y)) := by
      funext i
      refine Fin.addCases (fun p => ?_) (fun l => ?_) i
      · rw [Fin.addCases_left]; simp [X]
      · rw [Fin.addCases_right]; simp [Y]
    have raw : List.ofFn x = incidenceInput X Y := by rw [eq]; exact List.ofFn_fin_append _ _
    change C.eval (List.ofFn x)=false
    rw [raw]
    apply sound X Y
    · simpa [Y,Fintype.card_subtype] using lim
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hx
      exact none ⟨p,l,hp,(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hl).2⟩
  have mon : Monotone2 C := fun g hg => ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ao.1 g hg,
    (ao.2.2 g hg).le⟩
  have shape (j : Nat) (g : Gate) (hg : C.gates[j]?=some g) :
      ∃ a b : Nat, g.inputs=[a,b] ∧ a<N+N+j ∧ b<N+N+j := by
    obtain ⟨hj,eq⟩ := List.getElem?_eq_some_iff.mp hg
    have gg : PEqualNP.MetaComplexity.NestedCover.gateAt C j=g := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt,List.getD,hg]
    obtain ⟨a,b,ab⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hg))
    have pre := ao.2.1 j hj
    rw [gg,ab] at pre
    exact ⟨a,b,ab,pre a (by simp),pre b (by simp)⟩
  have ub := many_and_choices C I deg uniq mon hit off shape
  exact (family_encode cap).trans ub
end Entropy
open Entropy Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.GenericRejection PEqualNP.TopForm
def aWire (C : Circuit) : Finset Nat := (ands C).map ⟨Fin.val,Fin.val_injective⟩
theorem aWire_spec (C : Circuit) : (aWire C).card=(ands C).card ∧ aWire C⊆range C.size ∧
    ∀ j∈aWire C, (gateAt C j).op=GateOp.and := by
  classical
  refine ⟨card_map _,?_,?_⟩
  · rintro j hj
    obtain ⟨i,_,rfl⟩ := mem_map.mp hj
    exact mem_range.mpr i.isLt
  · intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
    have gg : gateAt C i.val=C.gates[i.val] := by simp [gateAt,List.getD,i.isLt]
    change (gateAt C i.val).op=GateOp.and
    rw [gg]
    have h := (mem_filter.mp hi).2
    cases eq : C.gates[i.val].op <;> simp_all [andOp]
theorem AND_credit {n} (C : Circuit) (S : Fin n → Finset (Fin n)) (t : Nat) :
    (∑ j∈range C.size,load C S j) + t*(ands C).card ≤ t*C.size+(n-t)*(heavy C S t).card := by
  classical
  let W := aWire C
  let R := range C.size \ W
  let H := heavy C S t
  have ws : W⊆range C.size := (aWire_spec C).2.1
  have wz (j) (hj : j∈W) : load C S j=0 := by
    unfold load
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro l hl
    have orGate := (mem_filter.mp hl).2.1
    have andGate := (aWire_spec C).2.2 j hj
    rw [andGate] at orGate
    contradiction
  have hs : H⊆R := by
    intro j hj
    have hh := mem_filter.mp hj
    exact mem_sdiff.mpr ⟨hh.1,fun z => by have h := wz j z; omega⟩
  have small : ∀ j∈R\H,load C S j≤t := by
    intro j hj
    obtain ⟨jr,nh⟩ := mem_sdiff.mp hj
    exact Nat.le_of_not_gt (fun gt => nh (mem_filter.mpr ⟨(mem_sdiff.mp jr).1,gt⟩))
  have top : ∀ j∈H,load C S j≤n := by
    intro j _
    simpa [load] using (card_le_card (filter_subset (fun l => Good C S j l) (univ : Finset (Fin n))))
  have pay1 := sum_le_sum small
  have pay2 := sum_le_sum top
  simp only [sum_const,nsmul_eq_mul] at pay1 pay2
  have h1 := sum_sdiff ws (f := fun j => load C S j)
  have h2 := sum_sdiff hs (f := fun j => load C S j)
  have zsum : (∑ j∈W,load C S j)=0 := sum_eq_zero wz
  rw [zsum,Nat.add_zero] at h1
  have count1 : R.card+(ands C).card=C.size := by
    have hh := card_sdiff_add_card_eq_card ws
    simpa [R,W,(aWire_spec C).1] using hh
  have count2 : (R\H).card+H.card=R.card := card_sdiff_add_card_eq_card hs
  have z := Nat.mul_le_mul_left H.card (show n≤t+(n-t) by omega)
  rw [Nat.mul_add] at z
  change _≤t*C.size+(n-t)*H.card
  rw [←count1,←count2]
  change (∑ j∈R,load C S j)=(∑ j∈range C.size,load C S j) at h1
  rw [←h1,←h2]
  nlinarith only [pay1,pay2,z]

theorem exceptional_budget {n q} (C : Circuit) (S : Fin n → Finset (Fin n))
    (mass : n*q≤∑ j∈range C.size,load C S j)
    (cap : (n-100)*(heavy C S 100).card≤100*(ands C).card) : n*q≤100*C.size := by
  have rhs := AND_credit C S 100
  omega
theorem fractionalAnd {N q} (C : Circuit) (S : Fin N → Finset (Fin N))
    (col : ∀ l,(S l).card=q+1) (uniq : ∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (b k e : Nat) (cap : q*b≤N) (pack : 2^e≤b^k) : e*q ≤ k*(ands C).card := by
  have ub := Entropy.and_power_floor C S col uniq ao pos sound b cap
  have ee := Nat.pow_le_pow_left pack q
  have bb := Nat.pow_le_pow_left ub k
  rw [←pow_mul,←pow_mul] at ee bb
  rw [Nat.mul_comm q k] at bb
  rw [Nat.mul_comm (ands C).card k] at bb
  have zz := ee.trans bb
  by_contra! bad
  have fl := Nat.pow_lt_pow_right (by decide : 1<2) bad
  omega

theorem one_gate_through949 {N q} (C : Circuit) (S : Fin N → Finset (Fin N))
    (order : N=q^2+q+1) (lo : 300≤q) (hi : q≤949)
    (col : ∀ l,(S l).card=q+1) (uniq : ∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (ok : C.output<N+N+C.size) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (rare : (heavy C S 100).card≤1) : N*q≤100*C.size := by
  have mass := column_mass C S (by omega) col ao ok pos sound
  apply exceptional_budget C S mass
  have prod := Nat.mul_le_mul_left (N-100) rare
  simp only [Nat.mul_one] at prod
  apply prod.trans
  by_cases mid : q≤799
  · have cap : q*256≤N := by rw [order]; nlinarith [Nat.mul_le_mul_left q lo]
    have floor := fractionalAnd C S col uniq ao pos sound 256 1 8 cap (by decide)
    simp only [Nat.one_mul] at floor
    have h := Nat.mul_le_mul_left q mid
    rw [order]
    have hh : 100≤q^2+q+1 := by omega
    have zz := Nat.sub_add_cancel hh
    nlinarith only [h,floor,zz]
  · have cap : q*768≤N := by rw [order]; nlinarith [Nat.mul_le_mul_left q (show 768≤q by omega)]
    have floor := fractionalAnd C S col uniq ao pos sound 768 2 19 cap (by decide)
    have h := Nat.mul_le_mul_left q hi
    rw [order]
    have hh : 100≤q^2+q+1 := by omega
    have zz := Nat.sub_add_cancel hh
    nlinarith only [h,floor,zz]

theorem two_gates_through424 {N q} (C : Circuit) (S : Fin N → Finset (Fin N))
    (order : N=q^2+q+1) (lo : 400≤q) (hi : q≤424)
    (col : ∀ l,(S l).card=q+1) (uniq : ∀ p r, p≠r → ∃! l, p∈S l ∧ r∈S l)
    (ao : IsAO2 (N+N) C) (ok : C.output<N+N+C.size) (pos : RightOnIncidentPairs S C)
    (sound : ∀ X Y, Y.card≤q → IsFalseInput S X Y → C.eval (incidenceInput X Y)=false)
    (rare : (heavy C S 100).card≤2) : N*q≤100*C.size := by
  have mass := column_mass C S (by omega) col ao ok pos sound
  apply exceptional_budget C S mass
  have prod := Nat.mul_le_mul_left (N-100) rare
  apply prod.trans
  have cap : q*384≤N := by rw [order]; nlinarith [Nat.mul_le_mul_left q (show 384≤q by omega)]
  have floor := fractionalAnd C S col uniq ao pos sound 384 2 17 cap (by decide)
  have h := Nat.mul_le_mul_left q hi
  rw [order]
  have hh : 100≤q^2+q+1 := by omega
  have zz := Nat.sub_add_cancel hh
  nlinarith only [h,floor,zz]

end PEqualNP.Outside.L_meta_8807
